-- Prove2me | Definitions.Def_QMCBeyondHK_sigmaSOSq
-- name    : QMCBeyondHK_sigmaSOSq
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T06:35:10.046212+00:00
-- url     : https://prove2.me/theorems/7582c8cf-618e-45e7-89ed-46a6d9562443
-- title:
--   Fourier coefficients $\hat f_k$ and the squared smoothed-out variation $\sigma_{SO}(f)^2$
-- statement:
--   For $f \in L^2([0,1)^d)$ and a frequency $k \in \mathbb Z^d$, the **Fourier coefficient** is
--   $$
--   \hat f_k = \int_{[0,1)^d} f(x)\, e^{-2\pi i \langle k, x\rangle}\,dx .
--   $$
--   The squared **smoothed-out variation** of $f$ (introduced by Bansal and Jiang) is
--   $$
--   \sigma_{SO}(f)^2 = \sum_{k \in \mathbb Z^d \setminus \{0\}} |\hat f_k|^2 \prod_{i=1}^d \max(1, |k_i|).
--   $$
--
--   It is the error characterization of the mission's main theorem: it can be much smaller than the Hardy–Krause variation.
--
--   **Formalization Note** The coefficient is a Bochner integral over the cube (equal to Mathlib's `mFourierCoeff` of the lift of $f$ to the torus); $\sigma_{SO}(f)^2$ is a sum of nonnegative terms in $[0,\infty]$, and "$f$ has finite $\sigma_{SO}(f)$" is $\sigma_{SO}(f)^2 < \infty$.
-- source:
--   Ezeunala, Jha, Jiang, Quasi-Monte Carlo Beyond Hardy–Krause II: (1 + ε)n Samples Suffice, arXiv:2609.10921 (sha256 bc273e88…), Theorem 2.2, p.6 (PDF p.8)

import Mathlib
import Definitions.Def_QMCBeyondHK_cube

set_option autoImplicit false

open MeasureTheory
open scoped ENNReal

namespace QMCBeyondHK

/-- The Fourier coefficient `f̂_k = ∫_{[0,1)^d} f(x) e^{−2πi⟨k,x⟩} dx` of frequency `k ∈ ℤ^d`
(arXiv:2609.10921, sha256 bc273e88…, Theorem 2.2, p.6, PDF p.8).

**Formalization Note** A Bochner integral over the cube; it equals Mathlib's `mFourierCoeff` of
the lift of `f` to the torus `(ℝ/ℤ)^d`. Every statement using it assumes `f ∈ L²`, so it is
integrable. -/
noncomputable def fourierCoeff (d : ℕ) (f : (Fin d → ℝ) → ℝ) (k : Fin d → ℤ) : ℂ :=
  ∫ x in cube d, (f x : ℂ) * Complex.exp (-(2 * Real.pi * Complex.I * ∑ i, (k i : ℂ) * (x i : ℂ)))

/-- The squared smoothed-out variation `σ_SO(f)² = ∑_{k∈ℤ^d∖{0}} |f̂_k|² ∏_{i∈[d]} max(1, |k_i|)`
(arXiv:2609.10921, sha256 bc273e88…, Theorem 2.2, p.6, PDF p.8; introduced in [BJ25]).

**Formalization Note** An unconditional sum of nonnegative terms in `ℝ≥0∞`: "finite `σ_SO(f)`"
is `sigmaSOSq d f < ⊤`. -/
noncomputable def sigmaSOSq (d : ℕ) (f : (Fin d → ℝ) → ℝ) : ℝ≥0∞ :=
  ∑' k : {k : Fin d → ℤ // k ≠ 0},
    (‖fourierCoeff d f k.1‖₊ : ℝ≥0∞) ^ 2 * ∏ i, ((max 1 (k.1 i).natAbs : ℕ) : ℝ≥0∞)

end QMCBeyondHK


