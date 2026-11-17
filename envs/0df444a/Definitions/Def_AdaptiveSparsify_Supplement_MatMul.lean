-- Prove2me | Definitions.Def_AdaptiveSparsify_Supplement_MatMul
-- name    : AdaptiveSparsify_Supplement_MatMul
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T11:51:04.152208+00:00
-- url     : https://prove2.me/theorems/0f06fef1-7fdb-404b-b187-ddf46996a660
-- title:
--   Achievable matrix multiplication exponents $\omega_0$ on the barrier-oracle RAM
-- statement:
--   The exponent $\omega$ of Theorems 2 and 6 is the exponent of $N\times N$ matrix multiplication. Since $\omega$ is an infimum that need not be attained, a bound "in time $N^\omega$" is read as a bound for every **achievable exponent** on the machine of the mission.
--
--   A program $P$ of the barrier-oracle RAM **multiplies matrices in work $C_\omega N^{\omega_0}$** if
--
--   1. $P$ is admissible (rational literals, stops through `halt`), and
--   2. for every $N\ge1$, all real matrices $X,Y\in\mathbb R^{N\times N}$ and every Gaussian tape, the run of $P$ with no barrier reachable, started with $N$ in integer cell $0$, $X$ in real cells $0,\dots,N^2-1$ and $Y$ in real cells $N^2,\dots,2N^2-1$ (row-major), halts without fault after at most $C_\omega N^{\omega_0}$ units of work with $(XY)_{ij}$ in real cell $-1-(iN+j)$.
--
--   The schoolbook algorithm shows that $\omega_0=3$ is achievable. Theorems 2 and 6 of the supplement hold for every achievable $\omega_0\ge2$, with program and constants allowed to depend on $\omega_0$, $C_\omega$ and the multiplication program.
--
--   **Formalization Note** The multiplication program must work on every tape and with every barrier call faulting, so it is deterministic and uses no oracle. The published straight-line-program exponent `OAI.MatrixMultiplication.Arithmetic.omega` is not used, because it is not about programs of this machine.
-- source:
--   Liu, Peng, Tang, Weng, Yang, Adaptive Matrix Sparsification with Applications to Empirical Risk Minimization and Computational Geometry (manuscript, sha256 7a66a27b…), Theorem 2, p.7; Theorem 6, p.32; §5.4 Running time, p.39; §6.4, pp.46–47

import Mathlib
import Definitions.Def_AdaptiveSparsify_Machine

namespace AdaptiveSparsify

/-!
# Achievable matrix multiplication exponents on the barrier-oracle RAM

Liu, Peng, Tang, Weng, Yang, *Adaptive Matrix Sparsification …* (manuscript, sha256 7a66a27b…), the
exponent `ω` of Theorem 2, p.7, of Theorem 6, p.32, and of their proofs (§5.4 "Running time", p.39;
§6.4, pp.46–47), where `ω` is the exponent of `n × n` matrix multiplication.

**Formalization Note.**
* `ω` is an infimum that need not be attained, so a bound "in time `n^ω`" is read as a bound for
  every **achievable** exponent: `ω₀` is achievable with constant `C_ω` when one admissible program of
  the published machine `AdaptiveSparsify.Machine` multiplies two `N × N` real matrices for every
  `N ≥ 1` within `C_ω N^{ω₀}` work. The schoolbook program shows that `ω₀ = 3` is achievable.
* The multiplication program is deterministic: it must halt without fault on **every** Gaussian tape,
  and no barrier is reachable (`BarrierEnv.empty`, every `oracle` call faults).
* Layout. Integer cell `0` holds `N`. Real cells `0, …, N² − 1` hold `X` in row-major order and cells
  `N², …, 2N² − 1` hold `Y`; every other cell is `0`. On `halt`, entry `(i, j)` of `X Y` is read from
  real cell `-1 - (i N + j)`.
-/

namespace Supplement

open Matrix

/-- Entry `o` (row-major) of an `N × N` matrix, for `o < N²`. -/
def rowMajor {N : ℕ} (X : Matrix (Fin N) (Fin N) ℝ) (o : ℕ) (h : o < N * N) : ℝ :=
  X ⟨o / N, Nat.div_lt_of_lt_mul h⟩
    ⟨o % N, Nat.mod_lt _ (Nat.pos_of_ne_zero (by rintro rfl; simp at h))⟩

/-- The integer input memory of a multiplication: cell `0` holds `N`. -/
def matMulIntMem (N : ℕ) : ℤ → ℤ := fun a => if a = 0 then (N : ℤ) else 0

/-- The real input memory of a multiplication: `X` from cell `0`, then `Y` from cell `N²`, row-major. -/
noncomputable def matMulRealMem {N : ℕ} (X Y : Matrix (Fin N) (Fin N) ℝ) : ℤ → ℝ := fun a =>
  if h : 0 ≤ a ∧ a.toNat < N * N then rowMajor X a.toNat h.2
  else if h' : (N * N : ℕ) ≤ a ∧ a.toNat - N * N < N * N then rowMajor Y (a.toNat - N * N) h'.2
  else 0

/-- `P` multiplies `N × N` real matrices in work `C_ω N^{ω₀}`: admissible, and for every `N ≥ 1`, all
`X, Y` and every tape, the run with no barrier halts without fault within `C_ω N^{ω₀}` work, with
`(X Y)_{ij}` in real cell `-1 - (i N + j)`. -/
def IsMatMulProgram (P : Program) (ω₀ Cω : ℝ) : Prop :=
  Admissible P ∧
    ∀ (N : ℕ), 1 ≤ N → ∀ (X Y : Matrix (Fin N) (Fin N) ℝ) (ω : ℕ → ℝ), ∃ t : ℕ,
      (run P BarrierEnv.empty ω (init (matMulIntMem N) (matMulRealMem X Y)) t).halted = true ∧
      (run P BarrierEnv.empty ω (init (matMulIntMem N) (matMulRealMem X Y)) t).faulted = false ∧
      ((run P BarrierEnv.empty ω (init (matMulIntMem N) (matMulRealMem X Y)) t).work : ℝ) ≤
        Cω * (N : ℝ) ^ ω₀ ∧
      ∀ i j : Fin N,
        (run P BarrierEnv.empty ω (init (matMulIntMem N) (matMulRealMem X Y)) t).core.mem
          (-1 - (((i : ℕ) * N + (j : ℕ) : ℕ) : ℤ)) = (X * Y) i j

end Supplement

end AdaptiveSparsify


