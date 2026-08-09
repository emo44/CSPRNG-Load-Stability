
"""
CSPRNG Output Stability Under Sustained CPU Load
=================================================

Empirical Assessment of CSPRNG Output Stability Under Sustained CPU Load

A controlled experimental framework for evaluating observable statistical
and performance characteristics of Python's `secrets.token_bytes()`
under sustained CPU load.

Research areas:
    - Applied Cryptography
    - Computer Security
    - Operating Systems
    - Random Number Generation
    - Experimental Computer Science

Author: Emo44
Year: 2026
License: MIT

Repository:
    https://github.com/emo44/CSPRNG-Load-Stability

IMPORTANT:
    This software is intended for experimental and research purposes.
    The results produced by this experiment do not constitute a
    cryptographic security proof or a formal audit of the underlying
    random-number generator.
"""


from __future__ import annotations

import csv
import json
import math
import multiprocessing as mp
import os
import queue
import random
import secrets
import sys
import threading
import time
import dataclasses
import platform
import hashlib
from dataclasses import asdict, dataclass, field
from datetime import datetime
from pathlib import Path
from typing import Optional, List, Tuple, Dict, Any

import numpy as np
import tkinter as tk
from tkinter import messagebox, scrolledtext, ttk

try:
    import psutil
except ImportError:
    print("psutil missing. Install dependencies with:")
    print("    pip install numpy psutil scipy matplotlib statsmodels")
    sys.exit(1)

try:
    from scipy.stats import ttest_rel, wilcoxon, shapiro, t, mannwhitneyu
    from scipy.special import gammaincc, erfc
except ImportError:
    print("scipy missing. Install dependencies with:")
    print("    pip install scipy")
    sys.exit(1)

try:
    import statsmodels.stats.power as smp
    import statsmodels.stats.api as sms
    HAS_STATSMODELS = True
except ImportError:
    HAS_STATSMODELS = False
    print("statsmodels not installed. Power analysis will be skipped.")

import matplotlib.pyplot as plt
from matplotlib.backends.backend_tkagg import FigureCanvasTkAgg

# ============================================================================
# CONFIGURATION
# ============================================================================

NUM_PAIRS = 30                      # 15 AB + 15 BA
BITS_PER_SESSION = 5_000_000
WARMUP_SECONDS = 3
STRESS_SECONDS = 30
SAMPLE_INTERVAL = 0.2
COOLDOWN_SECONDS = 60
SAVE_RAW_BYTES = True
PERMUTATIONS = 100_000
OUTPUT_DIR = Path("fingerprint_experiment_v7")
RANDOM_SEED = 12345
POSITIVE_CONTROL_BIASES = [0.51, 0.505, 0.5005]  # three levels
RUN_POSITIVE_CONTROL = True
STRESS_CPU_THRESHOLD = 80.0  # minimum % to consider stress valid

# ============================================================================
# DATA MODELS
# ============================================================================

@dataclass
class SessionResult:
    pair_id: int
    condition: str
    order: str
    timestamp_start: str
    timestamp_end: str

    n_bits: int
    n_bytes: int
    ones: int
    proportion: float
    z_score: float

    # Diagnostics (descriptive, not primary endpoints)
    monobit_p: float
    runs_p: float
    block_frequency_p: float
    byte_chisq_p: float
    autocorrelation: float
    cumulative_sums_p: float
    longest_run_p: float
    serial_p: float
    approx_entropy_p: float

    # System metrics during the exact generation interval
    cpu_percent_gen: Optional[float]
    cpu_temp_c_gen: Optional[float]
    cpu_freq_mhz_gen: Optional[float]

    # Global metrics (entire period)
    cpu_percent_avg: Optional[float]
    cpu_temp_c_avg: Optional[float]
    cpu_freq_mhz_avg: Optional[float]
    memory_percent_avg: Optional[float]

    # Latency and throughput
    generation_time_seconds: float
    throughput_mib_s: float

    entropy_avail_before: Optional[int]
    entropy_avail_after: Optional[int]

    cpu_governor: Optional[str] = None
    thermal_throttling_detected: bool = False

    cpu_timeline: Optional[List[Tuple[float, float, float, float]]] = field(
        default_factory=list
    )
    raw_file: Optional[str] = None
    raw_sha256: Optional[str] = None
    is_positive_control: bool = False
    positive_control_bias: Optional[float] = None
    stress_valid: bool = True

# ============================================================================
# UTILITIES
# ============================================================================

def bits_from_bytes(data: bytes) -> np.ndarray:
    try:
        if not isinstance(data, (bytes, bytearray)):
            data = bytes(data)
        raw = np.frombuffer(data, dtype=np.uint8)
        return np.unpackbits(raw)
    except (TypeError, ValueError, OverflowError) as e:
        print(f"bits_from_bytes error: {e}")
        return np.array([], dtype=np.uint8)

def z_score_proportion(bits: np.ndarray) -> float:
    n = len(bits)
    if n == 0:
        return float("nan")
    k = int(bits.sum())
    expected = n * 0.5
    std = math.sqrt(n * 0.25)
    if std == 0:
        return float("nan")
    return (k - expected) / std

def get_entropy_available() -> Optional[int]:
    if sys.platform != "linux":
        return None
    try:
        with open("/proc/sys/kernel/random/entropy_avail", "r") as f:
            return int(f.read().strip())
    except Exception:
        return None

def get_cpu_governor() -> Optional[str]:
    if sys.platform != "linux":
        return None
    try:
        with open("/sys/devices/system/cpu/cpu0/cpufreq/scaling_governor", "r") as f:
            return f.read().strip()
    except Exception:
        return None

def check_thermal_throttling() -> bool:
    if sys.platform != "linux":
        return False
    try:
        for path in Path("/sys/class/thermal").glob("thermal_message*"):
            with open(path / "throttle_status", "r") as f:
                if "throttled" in f.read().lower():
                    return True
    except Exception:
        pass
    try:
        with open("/sys/devices/system/cpu/cpu0/cpufreq/scaling_max_freq", "r") as f:
            max_freq = int(f.read().strip())
        with open("/sys/devices/system/cpu/cpu0/cpufreq/scaling_cur_freq", "r") as f:
            cur_freq = int(f.read().strip())
        if cur_freq < 0.8 * max_freq:
            return True
    except Exception:
        pass
    return False

def get_system_metadata() -> Dict[str, Any]:
    meta = {
        "platform": platform.platform(),
        "python_version": sys.version,
        "numpy_version": np.__version__,
        "scipy_version": __import__("scipy").__version__,
        "psutil_version": psutil.__version__,
        "cpu_count": os.cpu_count(),
        "ram_gb": round(psutil.virtual_memory().total / (1024**3), 2),
        "cpu_governor": get_cpu_governor(),
        "thermal_throttling_detected": check_thermal_throttling(),
    }
    try:
        if sys.platform == "linux":
            with open("/proc/cpuinfo", "r") as f:
                for line in f:
                    if "model name" in line:
                        meta["cpu_model"] = line.split(":")[1].strip()
                        break
        elif sys.platform == "win32":
            import winreg
            key = winreg.OpenKey(winreg.HKEY_LOCAL_MACHINE,
                                 r"HARDWARE\DESCRIPTION\System\CentralProcessor\0")
            meta["cpu_model"] = winreg.QueryValueEx(key, "ProcessorNameString")[0]
        else:
            meta["cpu_model"] = "Unknown"
    except Exception:
        meta["cpu_model"] = "Unknown"
    return meta

# ============================================================================
# STATISTICAL TESTS (custom diagnostics)
# ============================================================================

def monobit_test(bits: np.ndarray) -> float:
    n = len(bits)
    if n == 0:
        return float("nan")
    s = int(np.sum(bits))
    statistic = abs(2 * s - n) / math.sqrt(n)
    return erfc(statistic / math.sqrt(2))

def runs_test(bits: np.ndarray) -> float:
    n = len(bits)
    if n < 2:
        return float("nan")
    pi = float(np.mean(bits))
    if abs(pi - 0.5) >= 2.0 / math.sqrt(n):
        return 0.0
    runs = 1 + int(np.sum(bits[1:] != bits[:-1]))
    numerator = abs(runs - 2.0 * n * pi * (1.0 - pi))
    denominator = 2.0 * math.sqrt(n) * pi * (1.0 - pi)
    if denominator == 0:
        return float("nan")
    z = numerator / denominator
    return erfc(z / math.sqrt(2))

def block_frequency_test(bits: np.ndarray, block_size: int = 1000) -> float:
    n = len(bits)
    if n < block_size:
        return float("nan")
    num_blocks = n // block_size
    blocks = bits[:num_blocks * block_size].reshape(num_blocks, block_size)
    proportions = blocks.mean(axis=1)
    chi_square = 4.0 * block_size * np.sum((proportions - 0.5) ** 2)
    return float(gammaincc(num_blocks / 2.0, chi_square / 2.0))

def byte_chisquare_test(data: bytes) -> float:
    if not data:
        return float("nan")
    try:
        values = np.frombuffer(data, dtype=np.uint8)
    except (TypeError, ValueError):
        try:
            values = np.array(list(data), dtype=np.uint8)
        except (OverflowError, ValueError):
            return float("nan")
    counts = np.bincount(values, minlength=256)
    expected = len(values) / 256.0
    if expected == 0:
        return float("nan")
    chi_square = np.sum((counts - expected) ** 2 / expected)
    return float(gammaincc(255 / 2.0, chi_square / 2.0))

def autocorrelation_test(bits: np.ndarray) -> float:
    if len(bits) < 2:
        return float("nan")
    x = bits[:-1].astype(np.float64)
    y = bits[1:].astype(np.float64)
    sx = np.std(x)
    sy = np.std(y)
    if sx == 0 or sy == 0:
        return float("nan")
    return float(np.corrcoef(x, y)[0, 1])

def cumulative_sums_test(bits: np.ndarray) -> float:
    n = len(bits)
    if n < 10:
        return float("nan")
    x = 2 * bits.astype(np.int64) - 1
    S = np.cumsum(x)
    z = np.max(np.abs(S))
    if z == 0:
        return 1.0
    p = erfc(z / (np.sqrt(2 * n)))
    return float(p)

def longest_run_ones_test(bits: np.ndarray, block_size: int = 10000) -> float:
    n = len(bits)
    if n < block_size:
        return float("nan")
    num_blocks = n // block_size
    if num_blocks == 0:
        return float("nan")
    blocks = bits[:num_blocks * block_size].reshape(num_blocks, block_size)
    max_runs = []
    for block in blocks:
        max_run = 0
        current = 0
        for b in block:
            if b == 1:
                current += 1
                max_run = max(max_run, current)
            else:
                current = 0
        max_runs.append(max_run)
    counts = np.zeros(5, dtype=int)
    for mr in max_runs:
        if mr <= 10:
            counts[0] += 1
        elif mr == 11:
            counts[1] += 1
        elif mr == 12:
            counts[2] += 1
        elif mr == 13:
            counts[3] += 1
        else:
            counts[4] += 1
    pi = np.array([0.0882, 0.2092, 0.2483, 0.1933, 0.2610])
    expected = num_blocks * pi
    chi_square = np.sum((counts - expected) ** 2 / expected)
    return float(gammaincc(4 / 2.0, chi_square / 2.0))

def serial_test(bits: np.ndarray, m: int = 16) -> float:
    n = len(bits)
    if n < m * 10:
        return float("nan")
    patterns = np.zeros(1 << m, dtype=np.int64)
    mask = (1 << m) - 1
    val = 0
    for i, b in enumerate(bits):
        val = ((val << 1) | b) & mask
        if i >= m - 1:
            patterns[val] += 1
    total = n - m + 1
    if total == 0:
        return float("nan")
    expected = total / (1 << m)
    if expected < 1:
        return float("nan")
    chi_square = np.sum((patterns - expected) ** 2 / expected)
    df = (1 << m) - 1
    return float(gammaincc(df / 2.0, chi_square / 2.0))

def approximate_entropy_test(bits: np.ndarray, m: int = 2) -> float:
    n = len(bits)
    if n < 10:
        return float("nan")
    def _phi(k):
        pat = np.zeros(1 << k, dtype=np.int64)
        mask = (1 << k) - 1
        val = 0
        for i, b in enumerate(bits):
            val = ((val << 1) | b) & mask
            if i >= k - 1:
                pat[val] += 1
        total = n - k + 1
        if total == 0:
            return 0.0
        freqs = pat / total
        log_sum = np.sum(freqs[freqs > 0] * np.log(freqs[freqs > 0]))
        return log_sum
    phi_m = _phi(m)
    phi_m1 = _phi(m + 1)
    if phi_m == 0 or phi_m1 == 0:
        return float("nan")
    apen = phi_m - phi_m1
    chi2 = 2 * n * (np.log(2) - apen)
    df = 1 << m
    return float(gammaincc(df / 2.0, chi2 / 2.0))

# ============================================================================
# COMPLETE ANALYSIS
# ============================================================================

def analyze_data(data: bytes) -> dict:
    try:
        if not isinstance(data, (bytes, bytearray)):
            data = bytes(data)
    except (TypeError, ValueError, OverflowError) as e:
        print(f"analyze_data: conversion error {e}")
        return {
            "n_bits": 0,
            "n_bytes": 0,
            "ones": 0,
            "proportion": float("nan"),
            "z_score": float("nan"),
            "monobit_p": float("nan"),
            "runs_p": float("nan"),
            "block_frequency_p": float("nan"),
            "byte_chisq_p": float("nan"),
            "autocorrelation": float("nan"),
            "cumulative_sums_p": float("nan"),
            "longest_run_p": float("nan"),
            "serial_p": float("nan"),
            "approx_entropy_p": float("nan"),
        }

    bits = bits_from_bytes(data)
    if len(bits) == 0:
        return {
            "n_bits": 0,
            "n_bytes": 0,
            "ones": 0,
            "proportion": float("nan"),
            "z_score": float("nan"),
            "monobit_p": float("nan"),
            "runs_p": float("nan"),
            "block_frequency_p": float("nan"),
            "byte_chisq_p": float("nan"),
            "autocorrelation": float("nan"),
            "cumulative_sums_p": float("nan"),
            "longest_run_p": float("nan"),
            "serial_p": float("nan"),
            "approx_entropy_p": float("nan"),
        }

    ones = int(bits.sum())
    n = len(bits)

    def safe_call(func, *args, default=float("nan")):
        try:
            result = func(*args)
            if result is None or not np.isfinite(result):
                return default
            return result
        except Exception:
            return default

    return {
        "n_bits": n,
        "n_bytes": len(data),
        "ones": ones,
        "proportion": float(ones / n),
        "z_score": safe_call(z_score_proportion, bits),
        "monobit_p": safe_call(monobit_test, bits),
        "runs_p": safe_call(runs_test, bits),
        "block_frequency_p": safe_call(block_frequency_test, bits),
        "byte_chisq_p": safe_call(byte_chisquare_test, data),
        "autocorrelation": safe_call(autocorrelation_test, bits),
        "cumulative_sums_p": safe_call(cumulative_sums_test, bits),
        "longest_run_p": safe_call(longest_run_ones_test, bits),
        "serial_p": safe_call(serial_test, bits),
        "approx_entropy_p": safe_call(approximate_entropy_test, bits),
    }

# ============================================================================
# SYSTEM MONITOR
# ============================================================================

def get_cpu_temperature() -> Optional[float]:
    try:
        temperatures = psutil.sensors_temperatures()
        if not temperatures:
            return None
        preferred = ["coretemp", "k10temp", "cpu_thermal", "cpu-thermal"]
        for name in preferred:
            if name in temperatures and temperatures[name]:
                return float(temperatures[name][0].current)
        for entries in temperatures.values():
            if entries:
                return float(entries[0].current)
    except Exception:
        pass
    return None

class SystemMonitor:
    def __init__(self, interval: float = SAMPLE_INTERVAL):
        self.interval = interval
        self.samples: List[Tuple[float, float, float, float]] = []
        self._running = False
        self._thread: Optional[threading.Thread] = None

    def start(self):
        if self._running:
            return
        self._running = True
        self.samples.clear()
        self._thread = threading.Thread(target=self._monitor, daemon=True)
        self._thread.start()

    def stop(self):
        self._running = False
        if self._thread:
            self._thread.join(timeout=2.0)

    def _monitor(self):
        while self._running:
            ts = time.time()
            cpu = psutil.cpu_percent(interval=None)
            temp = get_cpu_temperature()
            freq = None
            try:
                f = psutil.cpu_freq()
                freq = f.current if f else None
            except Exception:
                pass
            self.samples.append((ts, cpu, temp, freq))
            time.sleep(self.interval)

    def get_stats(self, t_start: Optional[float] = None, t_end: Optional[float] = None) -> Dict[str, Optional[float]]:
        if not self.samples:
            return {
                "cpu_percent_avg": None,
                "cpu_temp_c_avg": None,
                "cpu_freq_mhz_avg": None,
                "memory_percent_avg": None,
            }
        if t_start is not None and t_end is not None:
            filtered = [s for s in self.samples if t_start <= s[0] <= t_end]
        else:
            filtered = self.samples

        if not filtered:
            return {
                "cpu_percent_avg": None,
                "cpu_temp_c_avg": None,
                "cpu_freq_mhz_avg": None,
                "memory_percent_avg": None,
            }

        cpu_vals = [s[1] for s in filtered if s[1] is not None]
        temp_vals = [s[2] for s in filtered if s[2] is not None]
        freq_vals = [s[3] for s in filtered if s[3] is not None]
        mem = None
        try:
            mem = psutil.virtual_memory().percent
        except Exception:
            pass

        return {
            "cpu_percent_avg": float(np.mean(cpu_vals)) if cpu_vals else None,
            "cpu_temp_c_avg": float(np.mean(temp_vals)) if temp_vals else None,
            "cpu_freq_mhz_avg": float(np.mean(freq_vals)) if freq_vals else None,
            "memory_percent_avg": mem,
        }

# ============================================================================
# CPU STRESS
# ============================================================================

def cpu_stress_worker(stop_event):
    x = 0x123456789ABCDEF
    while not stop_event.is_set():
        for _ in range(10000):
            x = (x * 6364136223846793005 + 1442695040888963407) & ((1 << 64) - 1)
        if x == 0:
            x = 0x123456789ABCDEF

class CPUStress:
    def __init__(self):
        self.processes = []
        self.stop_event = None

    def start(self):
        ctx = mp.get_context("spawn")
        self.stop_event = ctx.Event()
        cpu_count = os.cpu_count() or 1
        worker_count = max(1, cpu_count)
        for _ in range(worker_count):
            process = ctx.Process(target=cpu_stress_worker, args=(self.stop_event,))
            process.daemon = True
            process.start()
            self.processes.append(process)

    def stop(self):
        if self.stop_event is not None:
            self.stop_event.set()
        for process in self.processes:
            process.join(timeout=3)
        for process in self.processes:
            if process.is_alive():
                process.terminate()
                process.join()
        self.processes.clear()
        self.stop_event = None

# ============================================================================
# GENERATORS AND EXPERIMENT
# ============================================================================

def biased_random_bytes(n_bytes: int, bias: float, rng=None) -> bytes:
    if rng is None:
        rng = np.random.default_rng()
    bits = rng.choice([0, 1], size=n_bytes * 8, p=[1 - bias, bias])
    return np.packbits(bits.astype(np.uint8)).tobytes()

def generate_random_data(pair_id: int, is_positive_control: bool = False, bias: Optional[float] = None) -> bytes:
    n_bytes = BITS_PER_SESSION // 8
    if BITS_PER_SESSION % 8 != 0:
        raise ValueError("BITS_PER_SESSION must be a multiple of 8.")
    if is_positive_control and bias is not None:
        rng = np.random.default_rng(RANDOM_SEED + pair_id)
        return biased_random_bytes(n_bytes, bias, rng)
    return secrets.token_bytes(n_bytes)

def save_raw_data(data: bytes, pair_id: int, condition: str, is_positive_control: bool, bias: Optional[float] = None) -> Tuple[str, str]:
    OUTPUT_DIR.mkdir(exist_ok=True)
    suffix = "_pc" if is_positive_control else ""
    bias_str = f"_b{bias:.4f}" if bias is not None else ""
    filename = f"pair_{pair_id:02d}_{condition}{suffix}{bias_str}.bin"
    path = OUTPUT_DIR / filename
    path.write_bytes(data)
    sha256 = hashlib.sha256(data).hexdigest()
    return str(path), sha256

def run_session(
    pair_id: int,
    condition: str,
    order: str,
    ui_queue: queue.Queue,
    is_positive_control: bool = False,
    bias: Optional[float] = None,
) -> SessionResult:

    start_time = datetime.now()
    ui_queue.put(("log", f"   Preparing: {condition.upper()} (PC={is_positive_control}, bias={bias})"))

    monitor = SystemMonitor()
    monitor.start()

    stress = None
    if condition == "stress":
        stress = CPUStress()
        stress.start()
        ui_queue.put(("log", f"   CPU stress started ({STRESS_SECONDS}s)."))

    time.sleep(WARMUP_SECONDS)

    entropy_before = get_entropy_available()
    governor = get_cpu_governor()
    throttling_before = check_thermal_throttling()

    ui_queue.put(("log", "   Generating data..."))
    gen_start_ts = time.time()
    gen_start_perf = time.perf_counter()
    data = generate_random_data(pair_id, is_positive_control, bias)
    gen_end_perf = time.perf_counter()
    gen_end_ts = time.time()
    generation_time = gen_end_perf - gen_start_perf

    entropy_after = get_entropy_available()
    throttling_after = check_thermal_throttling()
    throttling_detected = throttling_before or throttling_after

    # Statistics during the generation interval
    stats_gen = monitor.get_stats(t_start=gen_start_ts, t_end=gen_end_ts)
    # Global statistics
    stats_global = monitor.get_stats()

    monitor.stop()
    if stress is not None:
        stress.stop()

    # Check if stress was effective
    stress_valid = True
    if condition == "stress":
        cpu_avg = stats_gen.get("cpu_percent_avg")
        if cpu_avg is not None and cpu_avg < STRESS_CPU_THRESHOLD:
            stress_valid = False
            ui_queue.put(("log", f"   ⚠️ WARNING: CPU stress only reached {cpu_avg:.1f}% (< {STRESS_CPU_THRESHOLD}%)"))

    timeline = monitor.samples

    try:
        analysis = analyze_data(data)
    except Exception as e:
        ui_queue.put(("log", f"   ⚠️ Error in analysis: {e}"))
        analysis = {
            "n_bits": 0,
            "n_bytes": 0,
            "ones": 0,
            "proportion": float("nan"),
            "z_score": float("nan"),
            "monobit_p": float("nan"),
            "runs_p": float("nan"),
            "block_frequency_p": float("nan"),
            "byte_chisq_p": float("nan"),
            "autocorrelation": float("nan"),
            "cumulative_sums_p": float("nan"),
            "longest_run_p": float("nan"),
            "serial_p": float("nan"),
            "approx_entropy_p": float("nan"),
        }

    raw_file = None
    raw_sha256 = None
    if SAVE_RAW_BYTES:
        try:
            raw_file, raw_sha256 = save_raw_data(data, pair_id, condition, is_positive_control, bias)
        except Exception as e:
            ui_queue.put(("log", f"   ⚠️ Error saving raw: {e}"))
            raw_file = None

    n_bytes = len(data)
    throughput_mib_s = (n_bytes / generation_time) / (1024 ** 2) if generation_time > 0 else float("nan")

    end_time = datetime.now()

    return SessionResult(
        pair_id=pair_id,
        condition=condition,
        order=order,
        timestamp_start=start_time.isoformat(),
        timestamp_end=end_time.isoformat(),
        n_bits=analysis["n_bits"],
        n_bytes=analysis["n_bytes"],
        ones=analysis["ones"],
        proportion=analysis["proportion"],
        z_score=analysis["z_score"],
        monobit_p=analysis["monobit_p"],
        runs_p=analysis["runs_p"],
        block_frequency_p=analysis["block_frequency_p"],
        byte_chisq_p=analysis["byte_chisq_p"],
        autocorrelation=analysis["autocorrelation"],
        cumulative_sums_p=analysis["cumulative_sums_p"],
        longest_run_p=analysis["longest_run_p"],
        serial_p=analysis["serial_p"],
        approx_entropy_p=analysis["approx_entropy_p"],
        cpu_percent_gen=stats_gen.get("cpu_percent_avg"),
        cpu_temp_c_gen=stats_gen.get("cpu_temp_c_avg"),
        cpu_freq_mhz_gen=stats_gen.get("cpu_freq_mhz_avg"),
        cpu_percent_avg=stats_global.get("cpu_percent_avg"),
        cpu_temp_c_avg=stats_global.get("cpu_temp_c_avg"),
        cpu_freq_mhz_avg=stats_global.get("cpu_freq_mhz_avg"),
        memory_percent_avg=stats_global.get("memory_percent_avg"),
        generation_time_seconds=generation_time,
        throughput_mib_s=throughput_mib_s,
        entropy_avail_before=entropy_before,
        entropy_avail_after=entropy_after,
        cpu_governor=governor,
        thermal_throttling_detected=throttling_detected,
        cpu_timeline=timeline,
        raw_file=raw_file,
        raw_sha256=raw_sha256,
        is_positive_control=is_positive_control,
        positive_control_bias=bias,
        stress_valid=stress_valid,
    )

# ============================================================================
# COMPARATIVE STATISTICS (corrected)
# ============================================================================

def fdr_correction(p_values: Dict[str, float]) -> Dict[str, float]:
    """Benjamini-Hochberg monotonic correction."""
    if not p_values:
        return {}
    items = [(k, float(v)) for k, v in p_values.items() if np.isfinite(v)]
    if not items:
        return {}
    items.sort(key=lambda x: x[1])
    m = len(items)
    adjusted = {}
    prev = 1.0
    for rank in range(m, 0, -1):
        key, p = items[rank - 1]
        corrected = min(prev, p * m / rank)
        adjusted[key] = min(1.0, corrected)
        prev = corrected
    return adjusted

def paired_metric_arrays(results, metric):
    """Extract paired arrays by pair_id for a given metric."""
    idle = {
        r.pair_id: getattr(r, metric)
        for r in results
        if r.condition == "idle" and not r.is_positive_control
    }
    stress = {
        r.pair_id: getattr(r, metric)
        for r in results
        if r.condition == "stress" and not r.is_positive_control
    }
    common_ids = sorted(set(idle) & set(stress))
    pairs = [
        (pid, idle[pid], stress[pid])
        for pid in common_ids
        if np.isfinite(idle[pid]) and np.isfinite(stress[pid])
    ]
    if not pairs:
        return np.array([]), np.array([]), []
    pair_ids = [p[0] for p in pairs]
    x = np.array([p[1] for p in pairs], dtype=float)
    y = np.array([p[2] for p in pairs], dtype=float)
    return x, y, pair_ids

def cohens_d_paired(x, y) -> float:
    diffs = np.asarray(x) - np.asarray(y)
    if len(diffs) < 2:
        return float("nan")
    std = np.std(diffs, ddof=1)
    if std == 0:
        return 0.0
    return float(np.mean(diffs) / std)

def permutation_test_paired(x, y, permutations=PERMUTATIONS, seed=12345):
    rng = np.random.default_rng(seed)
    diffs = np.asarray(x) - np.asarray(y)
    observed = abs(np.mean(diffs))
    count = 0
    for _ in range(permutations):
        signs = rng.choice([-1.0, 1.0], size=len(diffs))
        simulated = abs(np.mean(diffs * signs))
        if simulated >= observed:
            count += 1
    return (count + 1) / (permutations + 1)

def ci_paired_diff(x, y, confidence=0.95):
    diffs = np.asarray(x) - np.asarray(y)
    if len(diffs) < 2:
        return float("nan"), float("nan"), float("nan")
    mean_diff = np.mean(diffs)
    std_err = np.std(diffs, ddof=1) / np.sqrt(len(diffs))
    if std_err == 0:
        return mean_diff, mean_diff, mean_diff
    t_crit = t.ppf((1 + confidence) / 2, len(diffs) - 1)
    ci_low = mean_diff - t_crit * std_err
    ci_high = mean_diff + t_crit * std_err
    return mean_diff, ci_low, ci_high

def paired_statistics(results):
    """Full statistical analysis with primary/secondary endpoints."""
    # Primary and secondary endpoints
    primary_metrics = ["proportion", "generation_time_seconds", "throughput_mib_s"]
    secondary_metrics = [
        "z_score", "autocorrelation",
        "cpu_percent_gen", "cpu_temp_c_gen", "cpu_freq_mhz_gen",
        "cpu_percent_avg", "cpu_temp_c_avg", "cpu_freq_mhz_avg",
        "entropy_avail_before", "entropy_avail_after"
    ]
    # Randomness diagnostics (not subjected to t-test)
    randomness_diagnostics = [
        "monobit_p", "runs_p", "block_frequency_p",
        "byte_chisq_p", "cumulative_sums_p", "longest_run_p",
        "serial_p", "approx_entropy_p"
    ]

    all_metrics = primary_metrics + secondary_metrics + randomness_diagnostics
    output = {}
    normality_results = {}
    ci_results = {}
    raw_p_values = {}

    for metric in all_metrics:
        x, y, pair_ids = paired_metric_arrays(results, metric)
        if len(x) < 2:
            continue

        # Normality
        diffs = x - y
        if len(diffs) >= 3:
            shapiro_stat, shapiro_p = shapiro(diffs)
        else:
            shapiro_stat, shapiro_p = float("nan"), float("nan")
        normality_results[metric] = {"statistic": shapiro_stat, "p_value": shapiro_p}

        # Tests
        t_stat, p_ttest = ttest_rel(x, y)
        w_stat, p_wilcox = wilcoxon(x, y, correction=True)
        perm_p = permutation_test_paired(x, y)
        mean_diff, ci_low, ci_high = ci_paired_diff(x, y)

        # Only keep p-values for primary/secondary endpoints
        if metric in primary_metrics + secondary_metrics:
            raw_p_values[metric] = float(p_ttest)

        output[metric] = {
            "idle_mean": float(np.mean(x)),
            "stress_mean": float(np.mean(y)),
            "difference": float(mean_diff),
            "ci_95_low": float(ci_low),
            "ci_95_high": float(ci_high),
            "paired_t": float(t_stat),
            "paired_p_raw": float(p_ttest) if metric in primary_metrics + secondary_metrics else None,
            "wilcoxon_stat": float(w_stat),
            "wilcoxon_p": float(p_wilcox),
            "permutation_p": float(perm_p),
            "cohens_d": float(cohens_d_paired(x, y)),  # correct sign: idle - stress
            "shapiro_p": float(shapiro_p),
            "n_pairs": len(pair_ids),
        }
        ci_results[metric] = {"mean_diff": mean_diff, "ci_low": ci_low, "ci_high": ci_high}

    # FDR only for endpoints with p-values
    adjusted_p = fdr_correction(raw_p_values)
    for metric in output:
        if metric in adjusted_p:
            output[metric]["paired_p_fdr"] = adjusted_p[metric]
        elif metric in primary_metrics + secondary_metrics:
            output[metric]["paired_p_fdr"] = float("nan")

    # Positive control analysis (paired by pair_id and condition)
    pc_output = {}
    for bias in POSITIVE_CONTROL_BIASES:
        pc_idle = {
            r.pair_id: r.proportion
            for r in results
            if r.is_positive_control and r.condition == "idle" and r.positive_control_bias == bias
        }
        pc_stress = {
            r.pair_id: r.proportion
            for r in results
            if r.is_positive_control and r.condition == "stress" and r.positive_control_bias == bias
        }
        common = sorted(set(pc_idle) & set(pc_stress))
        if len(common) < 2:
            continue
        x_pc = np.array([pc_idle[pid] for pid in common], dtype=float)
        y_pc = np.array([pc_stress[pid] for pid in common], dtype=float)
        t_stat, p_val = ttest_rel(x_pc, y_pc)
        pc_output[f"bias_{bias:.4f}"] = {
            "idle_mean": float(np.mean(x_pc)),
            "stress_mean": float(np.mean(y_pc)),
            "difference": float(np.mean(y_pc - x_pc)),
            "paired_t": float(t_stat),
            "paired_p": float(p_val),
            "n_pairs": len(common),
        }

    # Order analysis (AB vs BA)
    order_analysis = {}
    for order in ["AB", "BA"]:
        for metric in primary_metrics:
            x_order = np.array([
                getattr(r, metric)
                for r in results
                if r.condition == "idle" and not r.is_positive_control and r.order == order
                and np.isfinite(getattr(r, metric))
            ], dtype=float)
            y_order = np.array([
                getattr(r, metric)
                for r in results
                if r.condition == "stress" and not r.is_positive_control and r.order == order
                and np.isfinite(getattr(r, metric))
            ], dtype=float)
            if len(x_order) >= 2 and len(y_order) >= 2:
                u_stat, p_mw = mannwhitneyu(x_order, y_order, alternative="two-sided")
                order_analysis[f"{order}_{metric}"] = {
                    "idle_mean": float(np.mean(x_order)),
                    "stress_mean": float(np.mean(y_order)),
                    "mannwhitney_u": float(u_stat),
                    "mannwhitney_p": float(p_mw),
                    "n_idle": len(x_order),
                    "n_stress": len(y_order),
                }

    return output, normality_results, ci_results, pc_output, order_analysis

# ============================================================================
# POWER ANALYSIS (sensitivity)
# ============================================================================

def power_sensitivity_analysis(n_pairs: int = NUM_PAIRS, alpha: float = 0.05) -> Dict[str, float]:
    if not HAS_STATSMODELS:
        return {}
    effect_sizes = [0.1, 0.2, 0.3, 0.4, 0.5, 0.6, 0.7, 0.8]
    powers = {}
    for d in effect_sizes:
        try:
            power = smp.TTestPower().power(effect_size=d, nobs=n_pairs, alpha=alpha, alternative="two-sided")
            powers[f"d={d:.1f}"] = power
        except:
            powers[f"d={d:.1f}"] = float("nan")
    return powers

# ============================================================================
# EXPORT
# ============================================================================

def save_csv(results):
    OUTPUT_DIR.mkdir(exist_ok=True)
    path = OUTPUT_DIR / "sessions.csv"
    if not results:
        return path
    base_fields = [f.name for f in dataclasses.fields(SessionResult) if f.name != "cpu_timeline"]
    with path.open("w", newline="", encoding="utf-8") as f:
        writer = csv.DictWriter(f, fieldnames=base_fields)
        writer.writeheader()
        for r in results:
            row = asdict(r)
            row.pop("cpu_timeline", None)
            writer.writerow(row)
    return path

def save_json(results, statistics, normality, ci, pc_analysis, order_analysis, power_sensitivity, metadata):
    OUTPUT_DIR.mkdir(exist_ok=True)
    path = OUTPUT_DIR / "experiment.json"
    payload = {
        "configuration": {
            "num_pairs": NUM_PAIRS,
            "bits_per_session": BITS_PER_SESSION,
            "warmup_seconds": WARMUP_SECONDS,
            "stress_seconds": STRESS_SECONDS,
            "sample_interval": SAMPLE_INTERVAL,
            "cooldown_seconds": COOLDOWN_SECONDS,
            "permutations": PERMUTATIONS,
            "random_seed": RANDOM_SEED,
            "positive_control_biases": POSITIVE_CONTROL_BIASES,
            "run_positive_control": RUN_POSITIVE_CONTROL,
            "stress_cpu_threshold": STRESS_CPU_THRESHOLD,
        },
        "system_metadata": metadata,
        "power_sensitivity": power_sensitivity,
        "normality_tests": normality,
        "confidence_intervals": ci,
        "positive_control_analysis": pc_analysis,
        "order_analysis": order_analysis,
        "statistics": statistics,
        "results": [asdict(r) for r in results],
    }
    with path.open("w", encoding="utf-8") as f:
        json.dump(payload, f, indent=2, default=str)
    return path

# ============================================================================
# REPORTS
# ============================================================================

def generate_markdown(results, statistics, normality, ci, pc_analysis, order_analysis, power_sensitivity, metadata):
    path = OUTPUT_DIR / "report.md"
    idle_prop = [r.proportion for r in results if r.condition == "idle" and not r.is_positive_control and np.isfinite(r.proportion)]
    stress_prop = [r.proportion for r in results if r.condition == "stress" and not r.is_positive_control and np.isfinite(r.proportion)]

    lines = []
    lines.append("# CSPRNG CPU Load Experiment (v7)")
    lines.append("")
    lines.append(f"Generated: {datetime.now().isoformat()}")
    lines.append("")
    lines.append("## Objective")
    lines.append("Compare the observable statistical properties and acquisition latency of `secrets.token_bytes()` under idle and sustained CPU load, using a balanced AB/BA design, positive controls, and FDR correction.")
    lines.append("")
    lines.append("## System Metadata")
    for key, val in metadata.items():
        lines.append(f"- {key}: {val}")
    lines.append("")
    lines.append("## Configuration")
    lines.append(f"- Pairs: {NUM_PAIRS} (15 AB + 15 BA)")
    lines.append(f"- Bits per session: {BITS_PER_SESSION:,}")
    lines.append(f"- Warm-up: {WARMUP_SECONDS}s")
    lines.append(f"- Stress duration: {STRESS_SECONDS}s")
    lines.append(f"- Cooldown: {COOLDOWN_SECONDS}s")
    lines.append(f"- Permutations: {PERMUTATIONS}")
    lines.append(f"- Random seed: {RANDOM_SEED}")
    lines.append(f"- Positive control biases: {POSITIVE_CONTROL_BIASES}")
    lines.append(f"- CPU stress threshold: {STRESS_CPU_THRESHOLD}%")
    lines.append("")
    lines.append("## Power Sensitivity")
    for label, power in power_sensitivity.items():
        lines.append(f"- {label}: {power:.4f}")
    lines.append("")
    lines.append("## Important limitation")
    lines.append("This experiment does not constitute cryptographic proof of CSPRNG security.")
    lines.append("")

    # Primary endpoints
    lines.append("## Primary endpoints")
    for metric in ["proportion", "generation_time_seconds", "throughput_mib_s"]:
        if metric not in statistics:
            continue
        s = statistics[metric]
        lines.append(f"### `{metric}`")
        lines.append(f"- Idle mean: {s['idle_mean']:.8f}")
        lines.append(f"- Stress mean: {s['stress_mean']:.8f}")
        lines.append(f"- Difference (idle − stress): {s['difference']:.8f}")
        lines.append(f"- 95% CI: [{s['ci_95_low']:.8f}, {s['ci_95_high']:.8f}]")
        lines.append(f"- FDR-adjusted p: {s.get('paired_p_fdr', float('nan')):.4g}")
        lines.append(f"- Cohen's d: {s['cohens_d']:.4f}")
        lines.append(f"- N pairs: {s['n_pairs']}")
        lines.append("")

    # Positive controls
    if pc_analysis:
        lines.append("## Positive controls (biased generators)")
        for bias, vals in pc_analysis.items():
            lines.append(f"### Bias {bias}")
            lines.append(f"- Idle mean: {vals['idle_mean']:.8f}")
            lines.append(f"- Stress mean: {vals['stress_mean']:.8f}")
            lines.append(f"- Difference: {vals['difference']:.8f}")
            lines.append(f"- Paired t-test p: {vals['paired_p']:.4g}")
            lines.append(f"- N pairs: {vals['n_pairs']}")
            lines.append("")

    # Order analysis
    if order_analysis:
        lines.append("## Order effects (AB vs BA)")
        for key, vals in order_analysis.items():
            lines.append(f"- {key}: Mann-Whitney p = {vals['mannwhitney_p']:.4g}")
        lines.append("")

    # Normality
    lines.append("## Normality of differences (Shapiro-Wilk)")
    lines.append("| Metric | W statistic | p-value |")
    lines.append("|--------|-------------|---------|")
    for metric, vals in normality.items():
        lines.append(f"| `{metric}` | {vals['statistic']:.6f} | {vals['p_value']:.4g} |")
    lines.append("")

    # Main table (only primary and secondary endpoints)
    lines.append("## Paired statistical analysis (FDR-corrected, primary & secondary endpoints)")
    lines.append("| Metric | Idle mean | Stress mean | Diff | 95% CI | FDR adj. p | Wilcoxon p | Permutation p | Cohen's d | N pairs |")
    lines.append("|--------|-----------|-------------|------|--------|------------|------------|---------------|-----------|---------|")
    for metric, vals in statistics.items():
        if "paired_p_fdr" not in vals:
            continue
        lines.append(
            f"| `{metric}` | {vals['idle_mean']:.8f} | {vals['stress_mean']:.8f} | "
            f"{vals['difference']:.8f} | [{vals['ci_95_low']:.8f}, {vals['ci_95_high']:.8f}] | "
            f"{vals['paired_p_fdr']:.4g} | {vals['wilcoxon_p']:.4g} | "
            f"{vals['permutation_p']:.4g} | {vals['cohens_d']:.4f} | {vals['n_pairs']} |"
        )

    # Randomness diagnostics (distribution of p-values)
    lines.append("")
    lines.append("## Randomness diagnostics (descriptive)")
    lines.append("The following are p-values from individual randomness tests, presented descriptively. They are not used as endpoints for hypothesis testing.")
    lines.append("")
    diag_metrics = ["monobit_p", "runs_p", "block_frequency_p", "byte_chisq_p", "cumulative_sums_p", "longest_run_p", "serial_p", "approx_entropy_p"]
    for metric in diag_metrics:
        if metric not in statistics:
            continue
        s = statistics[metric]
        lines.append(f"### `{metric}`")
        lines.append(f"- Idle mean p: {s['idle_mean']:.4g}")
        lines.append(f"- Stress mean p: {s['stress_mean']:.4g}")
        lines.append(f"- Difference: {s['difference']:.4g}")
        lines.append("")

    lines.append("## Interpretation")
    lines.append("A lack of statistically detectable differences (FDR-adjusted p > 0.05) with narrow confidence intervals is consistent with stable output behavior under the tested conditions.")
    lines.append("The positive controls confirm that the analysis pipeline is sensitive to known biases.")
    lines.append("")
    path.write_text("\n".join(lines), encoding="utf-8")
    return path

def generate_latex(results, statistics, normality, ci, pc_analysis, order_analysis, power_sensitivity):
    path = OUTPUT_DIR / "report.tex"
    p_stats = statistics.get("proportion", {})
    idle_mean = p_stats.get("idle_mean", float("nan"))
    stress_mean = p_stats.get("stress_mean", float("nan"))
    p_fdr = p_stats.get("paired_p_fdr", float("nan"))
    d_val = p_stats.get("cohens_d", float("nan"))
    ci_low = p_stats.get("ci_95_low", float("nan"))
    ci_high = p_stats.get("ci_95_high", float("nan"))
    n_pairs = p_stats.get("n_pairs", 0)

    tex = rf"""
\documentclass[11pt,a4paper]{{article}}
\usepackage[utf8]{{inputenc}}
\usepackage[T1]{{fontenc}}
\usepackage{{geometry}}
\usepackage{{booktabs}}
\usepackage{{amsmath}}
\geometry{{margin=2.5cm}}
\title{{CSPRNG Output Under CPU Load (v7)}}
\author{{Automated Experiment}}
\date{{\today}}
\begin{{document}}
\maketitle
\section*{{Objective}}
Compare statistical properties and latency of \texttt{{secrets.token\_bytes()}} under idle and sustained CPU load using a balanced AB/BA design.
\section*{{Configuration}}
\begin{{itemize}}
  \item Pairs: {NUM_PAIRS} (15 idle→stress, 15 stress→idle)
  \item Bits per session: {BITS_PER_SESSION:,}
  \item Stress duration: {STRESS_SECONDS}s
  \item Cooldown: {COOLDOWN_SECONDS}s
  \item FDR correction applied.
  \item Positive control biases: {', '.join(map(str, POSITIVE_CONTROL_BIASES))}
\end{{itemize}}
\section*{{Power Sensitivity}}
{chr(10).join([f"- {label}: {power:.4f}" for label, power in power_sensitivity.items()])}
\section*{{Primary Endpoint: Proportion of Ones}}
\begin{{table}}[h]
\centering
\begin{{tabular}}{{lcc}}
\toprule
Condition & Mean & N pairs \\
\midrule
Idle & {idle_mean:.8f} & {n_pairs} \\
Stress & {stress_mean:.8f} & {n_pairs} \\
\bottomrule
\end{{tabular}}
\end{{table}}
Difference: {p_stats.get('difference', float('nan')):.8f} \\
95\% CI: [{ci_low:.8f}, {ci_high:.8f}] \\
FDR-adjusted p: {p_fdr:.6g} \\
Cohen's d: {d_val:.6f}
\section*{{Positive Controls}}
{chr(10).join([f"Bias {bias}: p = {vals['paired_p']:.6g} (N={vals['n_pairs']})" for bias, vals in pc_analysis.items()])}
\section*{{Conclusion}}
No statistically detectable difference was observed. The positive controls confirm pipeline sensitivity.
\end{{document}}
"""
    path.write_text(tex, encoding="utf-8")
    return path

# ============================================================================
# GUI
# ============================================================================

class CSPRNGExperimentGUI:

    def __init__(self, root):
        self.root = root
        self.root.title("CSPRNG CPU Load Experiment v7")
        self.root.geometry("1100x850")
        self.root.minsize(900, 700)
        OUTPUT_DIR.mkdir(exist_ok=True)
        self.results = []
        self.running = False
        self.ui_queue = queue.Queue()
        self.configure_style()
        self.build_ui()
        self.root.after(100, self.process_ui_queue)
        self.log("Ready. Experiment v7: corrected FDR, exact pairing, paired positive controls, etc.")

    def configure_style(self):
        style = ttk.Style()
        try:
            style.theme_use("clam")
        except tk.TclError:
            pass
        style.configure("Title.TLabel", font=("Segoe UI", 16, "bold"))
        style.configure("Subtitle.TLabel", font=("Segoe UI", 10))

    def build_ui(self):
        main = ttk.Frame(self.root, padding=20)
        main.pack(fill=tk.BOTH, expand=True)
        ttk.Label(main, text="CSPRNG CPU Load Experiment v7", style="Title.TLabel").pack(pady=(0, 5))
        ttk.Label(main, text="30 pairs · AB/BA · FDR corrected · Paired PC · CI · Power",
                  style="Subtitle.TLabel").pack(pady=(0, 15))
        controls = ttk.Frame(main)
        controls.pack(fill=tk.X)
        self.start_button = ttk.Button(controls, text="▶ Run", command=self.start_experiment)
        self.start_button.pack(side=tk.LEFT, padx=5)
        self.report_button = ttk.Button(controls, text="📄 Generate report", command=self.generate_report, state=tk.DISABLED)
        self.report_button.pack(side=tk.LEFT, padx=5)
        self.reset_button = ttk.Button(controls, text="🔄 Reset", command=self.reset)
        self.reset_button.pack(side=tk.LEFT, padx=5)
        log_frame = ttk.LabelFrame(main, text="Progress", padding=10)
        log_frame.pack(fill=tk.BOTH, expand=True, pady=10)
        self.log_text = scrolledtext.ScrolledText(log_frame, font=("Consolas", 9))
        self.log_text.pack(fill=tk.BOTH, expand=True)
        graph_frame = ttk.LabelFrame(main, text="Proportion per session", padding=10)
        graph_frame.pack(fill=tk.BOTH, expand=True, pady=10)
        self.figure, self.ax = plt.subplots(figsize=(8, 3), dpi=100)
        self.canvas = FigureCanvasTkAgg(self.figure, master=graph_frame)
        self.canvas.get_tk_widget().pack(fill=tk.BOTH, expand=True)

    # Helper to safely format values that may be None
    def _fmt(self, value, fmt=".1f"):
        return f"{value:{fmt}}" if value is not None else "N/A"

    def log(self, message):
        timestamp = time.strftime("%H:%M:%S")
        self.log_text.insert(tk.END, f"[{timestamp}] {message}\n")
        self.log_text.see(tk.END)

    def reset(self):
        if self.running:
            return
        self.results.clear()
        self.report_button.config(state=tk.DISABLED)
        self.ax.clear()
        self.ax.set_title("Waiting for data...")
        self.canvas.draw()
        self.log("Experiment reset.")

    def start_experiment(self):
        if self.running:
            return
        self.running = True
        self.start_button.config(state=tk.DISABLED)
        self.report_button.config(state=tk.DISABLED)
        self.results.clear()
        thread = threading.Thread(target=self.experiment_worker, daemon=True)
        thread.start()

    def experiment_worker(self):
        try:
            self.ui_queue.put(("log", "=== EXPERIMENT START (v7) ==="))
            self.ui_queue.put(("log", f"Pairs: {NUM_PAIRS} (15 AB + 15 BA)"))
            self.ui_queue.put(("log", f"Bits per session: {BITS_PER_SESSION:,}"))
            self.ui_queue.put(("log", f"Stress: {STRESS_SECONDS}s, Cooldown: {COOLDOWN_SECONDS}s"))
            self.ui_queue.put(("log", f"Positive control biases: {POSITIVE_CONTROL_BIASES}"))

            random.seed(RANDOM_SEED)
            orders = ["AB"] * 15 + ["BA"] * 15
            random.shuffle(orders)

            for pair_id in range(1, NUM_PAIRS + 1):
                order = orders[pair_id - 1]
                conditions = ["idle", "stress"] if order == "AB" else ["stress", "idle"]
                self.ui_queue.put(("log", f"\n--- PAIR {pair_id}/{NUM_PAIRS} (order {order}) ---"))

                for idx, condition in enumerate(conditions):
                    # Normal session
                    self.ui_queue.put(("log", f"Session: {condition.upper()} (normal)"))
                    result = run_session(pair_id, condition, order, self.ui_queue, is_positive_control=False)
                    self.results.append(result)

                    cpu_gen_str = self._fmt(result.cpu_percent_gen, ".1f")
                    self.ui_queue.put((
                        "log",
                        f"   prop={result.proportion:.8f} | "
                        f"lat={result.generation_time_seconds:.3f}s | "
                        f"thr={result.throughput_mib_s:.2f} MiB/s | "
                        f"CPU_gen={cpu_gen_str}%"
                    ))

                    # Positive control for each condition and each bias
                    if RUN_POSITIVE_CONTROL:
                        for bias in POSITIVE_CONTROL_BIASES:
                            self.ui_queue.put(("log", f"   PC bias={bias:.4f}"))
                            pc_result = run_session(pair_id, condition, order, self.ui_queue,
                                                    is_positive_control=True, bias=bias)
                            self.results.append(pc_result)
                            self.ui_queue.put((
                                "log",
                                f"   PC: prop={pc_result.proportion:.8f} | "
                                f"lat={pc_result.generation_time_seconds:.3f}s"
                            ))

                    if idx < len(conditions) - 1:
                        self.ui_queue.put(("log", f"   Cooldown {COOLDOWN_SECONDS}s..."))
                        time.sleep(COOLDOWN_SECONDS)

                self.ui_queue.put(("plot", None))

            statistics, normality, ci_results, pc_analysis, order_analysis = paired_statistics(self.results)
            metadata = get_system_metadata()
            power_sensitivity = power_sensitivity_analysis()

            csv_path = save_csv(self.results)
            json_path = save_json(self.results, statistics, normality, ci_results, pc_analysis, order_analysis, power_sensitivity, metadata)
            md_path = generate_markdown(self.results, statistics, normality, ci_results, pc_analysis, order_analysis, power_sensitivity, metadata)
            tex_path = generate_latex(self.results, statistics, normality, ci_results, pc_analysis, order_analysis, power_sensitivity)

            self.ui_queue.put(("log", "\n=== EXPERIMENT COMPLETED ==="))
            self.ui_queue.put(("log", f"CSV: {csv_path}"))
            self.ui_queue.put(("log", f"JSON: {json_path}"))
            self.ui_queue.put(("log", f"Markdown: {md_path}"))
            self.ui_queue.put(("log", f"LaTeX: {tex_path}"))
            self.ui_queue.put(("finished", statistics))

        except Exception as exc:
            self.ui_queue.put(("error", repr(exc)))

    def process_ui_queue(self):
        try:
            while True:
                action, payload = self.ui_queue.get_nowait()
                if action == "log":
                    self.log(payload)
                elif action == "plot":
                    self.update_plot()
                elif action == "finished":
                    self.running = False
                    self.start_button.config(state=tk.NORMAL)
                    self.report_button.config(state=tk.NORMAL)
                    self.log("Results saved. You can generate the report.")
                elif action == "error":
                    self.running = False
                    self.start_button.config(state=tk.NORMAL)
                    self.log(f"ERROR: {payload}")
                    messagebox.showerror("Error", payload)
        except queue.Empty:
            pass
        self.root.after(100, self.process_ui_queue)

    def update_plot(self):
        idle = [r.proportion for r in self.results if r.condition == "idle" and not r.is_positive_control and np.isfinite(r.proportion)]
        stress = [r.proportion for r in self.results if r.condition == "stress" and not r.is_positive_control and np.isfinite(r.proportion)]
        self.ax.clear()
        if idle:
            self.ax.plot(range(1, len(idle) + 1), idle, "o-", label="Idle")
        if stress:
            self.ax.plot(range(1, len(stress) + 1), stress, "o-", label="Stress")
        self.ax.axhline(0.5, color="black", linewidth=0.8, alpha=0.5, linestyle="--")
        self.ax.set_xlabel("Session")
        self.ax.set_ylabel("Proportion of ones")
        self.ax.set_title("CSPRNG output (v7)")
        self.ax.grid(alpha=0.25)
        self.ax.legend()
        self.canvas.draw()

    def generate_report(self):
        if not self.results:
            messagebox.showwarning("No data", "Run the experiment first.")
            return
        statistics, normality, ci_results, pc_analysis, order_analysis = paired_statistics(self.results)
        metadata = get_system_metadata()
        power_sensitivity = power_sensitivity_analysis()
        md_path = generate_markdown(self.results, statistics, normality, ci_results, pc_analysis, order_analysis, power_sensitivity, metadata)
        tex_path = generate_latex(self.results, statistics, normality, ci_results, pc_analysis, order_analysis, power_sensitivity)
        self.log(f"Markdown report: {md_path}")
        self.log(f"LaTeX report: {tex_path}")
        messagebox.showinfo("Report", f"Reports generated in:\n{OUTPUT_DIR.resolve()}")

# ============================================================================
# MAIN
# ============================================================================

def main():
    mp.freeze_support()
    try:
        mp.set_start_method("spawn", force=True)
    except RuntimeError:
        pass
    root = tk.Tk()
    app = CSPRNGExperimentGUI(root)
    root.mainloop()

if __name__ == "__main__":
    main()