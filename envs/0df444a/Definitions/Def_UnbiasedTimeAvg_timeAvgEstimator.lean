-- Prove2me | Definitions.Def_UnbiasedTimeAvg_timeAvgEstimator
-- name    : UnbiasedTimeAvg_timeAvgEstimator
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T03:20:33.749386+00:00
-- url     : https://prove2.me/theorems/3973719d-2044-44aa-bf46-8ee6e84ce664
-- title:
--   The conventional time-average estimator $f_k$
-- statement:
--   For $k\ge1$ and a burn-in $b=b(k)$,
--   $$f_k:=\frac{1}{k-b}\sum_{i=b}^{k-1}f(X_i).$$
--   This is the standard estimator of the steady-state mean $\mu$ that the mission's unbiased estimator is compared with.
--
--   **Formalization Note** The burn-in is a natural number at the fixed $k$; the theorems assume the paper's standing $b(k)\le k/2$ as `2 * b ≤ k`. The denominator $k-b$ is computed in $\mathbb R$.
-- source:
--   N. Kahalé, Unbiased time-average estimators for Markov chains, arXiv:2209.09581v1 (20 Sep 2022), p.2 (definition of f_k)

import Mathlib
import Definitions.Def_UnbiasedTimeAvg_coupledChain

namespace UnbiasedTimeAvg

/-- **The conventional time-average estimator `f_k`.** Kahalé, arXiv:2209.09581v1, p.2: "For
`k ≥ 1`, define the time-average estimator `f_k := (1/(k − b(k))) Σ_{i=b(k)}^{k−1} f(X_i)`, where
`b(k) ≥ 0` is a burn-in period that may depend on `k`."

`timeAvgEstimator g x₀ U f b k ω = (k − b)⁻¹ Σ_{i=b}^{k−1} f(X_i(ω))`.

**Formalization Note.** `b` is the value `b(k)` at the fixed `k`; the paper's standing
`b(k) ≤ k/2` (p.4) is a hypothesis of each theorem (`2 * b ≤ k`), which makes `k − b ≥ 1` for
`k ≥ 1`. The subtraction `k − b` is taken in `ℝ`. -/
noncomputable def timeAvgEstimator {Ω F F' : Type*} (g : F → F' → F) (x₀ : F)
    (U : ℤ → Ω → F') (f : F → ℝ) (b k : ℕ) : Ω → ℝ :=
  fun ω => (1 / ((k : ℝ) - b)) * ∑ i ∈ Finset.Ico b k, f (coupledChain g x₀ U i 0 ω)

end UnbiasedTimeAvg


