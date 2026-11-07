-- Prove2me | Definitions.Def_TTTSampling_Rbar
-- name    : TTTSampling_Rbar
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T21:36:17.526843+00:00
-- url     : https://prove2.me/theorems/21f17255-9937-4808-bb1c-345fe038a64a
-- title:
--   Parameters $\bar R=\lceil 2R^2\rceil$, $N$, $K$ of Algorithm 3 and the loop length $L$
-- statement:
--   For $R\ge1$, $\delta\in(0,1)$, a class size $m=|\mathcal F|$ and a constant $C_{\mathsf N}\in\mathbb N$, Algorithm 3 (Line 1) uses
--
--   $$
--   \bar R=\lceil 2R^2\rceil,\qquad N=C_{\mathsf N}\Bigl\lceil\sqrt{\log m}\cdot R^2\bar R^2\Bigl(\log\frac{R\log m}{\delta}\Bigr)\Bigr\rceil,\qquad K=\lceil 4R\log_2(1/\delta)\rceil,
--   $$
--
--   with natural logarithms in $N$. The module also fixes the number of inner iterations run per round, $L=N+2\bar R(\lfloor\log_2 m\rfloor+1)\ge 2\bar R\log_2 m+N$, the almost-sure bound of Lemma 3.9.
--
--   **Formalization Note** $C_{\mathsf N}$ is a natural number. The ceiling of a nonpositive number is $0$; for $m\ge2$, $R\ge1$ and $\delta<1/2$ the argument of the ceiling in $N$ is positive.
-- source:
--   Golowich, Moitra, Rohatgi, The Power of Test-Time Training for Approximate Sampling, arXiv:2606.11437 (version of November 3, 2026), Algorithm 3, Line 1, p.12 (PDF p.14); Lemma 3.9, p.26 (PDF p.28)

import Mathlib

namespace TTTSampling

/-- **The parameters of Algorithm 3**, Line 1.

Golowich, Moitra, Rohatgi, arXiv:2606.11437 (version of November 3, 2026), Algorithm 3, Line 1,
printed p.12 (PDF p.14): "Define R̄ := ⌈2R²⌉, N := C_N ⌈√(log |ℱ|) · R²R̄² (log (R log |ℱ|/δ))⌉
(for an appropriate constant C_N, specified in Lemma 3.13), and K := ⌈4R log₂(1/δ)⌉."

`Rbar R = ⌈2R²⌉` is also the threshold `M` passed to Algorithm 2 (Line 7).

**Formalization Note** Ceilings of nonnegative reals are `Nat.ceil`. -/
noncomputable def Rbar (R : ℝ) : ℕ := ⌈2 * R ^ 2⌉₊

/-- The number of particles `N = C_N ⌈√(log |ℱ|) · R² R̄² · log(R log |ℱ| / δ)⌉` (Algorithm 3,
Line 1, p.12), with `m = |ℱ|` and natural logarithms.

**Formalization Note** `C_N` is a natural number. For `|ℱ| ≥ 2`, `R ≥ 1` and `δ < 1/2` the
argument of the ceiling is positive; `Nat.ceil` returns `0` for a nonpositive argument, a case the
paper's formula leaves undefined. -/
noncomputable def Npart (C_N m : ℕ) (R δ : ℝ) : ℕ :=
  C_N * ⌈Real.sqrt (Real.log m) * R ^ 2 * (Rbar R : ℝ) ^ 2 * Real.log (R * Real.log m / δ)⌉₊

/-- The number of outer rounds `K = ⌈4R log₂(1/δ)⌉` (Algorithm 3, Line 1, p.12). -/
noncomputable def Kreps (R δ : ℝ) : ℕ := ⌈4 * R * Real.logb 2 (1 / δ)⌉₊

/-- The number of inner iterations run per round in the Lean encoding of the while loop of
Algorithm 3 (Lines 5–10): `L = N + 2R̄(⌊log₂ |ℱ|⌋ + 1) ≥ 2R̄ log₂ |ℱ| + N`, the almost-sure bound on
`J` of Lemma 3.9 (p.26). The loop body is the identity once every particle is complete, so running
`L` iterations is the paper's loop whenever `J ≤ L`. -/
noncomputable def pathLen (C_N m : ℕ) (R δ : ℝ) : ℕ :=
  Npart C_N m R δ + 2 * Rbar R * (Nat.log 2 m + 1)

end TTTSampling


