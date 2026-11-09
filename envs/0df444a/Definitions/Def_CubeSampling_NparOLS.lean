-- Prove2me | Definitions.Def_CubeSampling_NparOLS
-- name    : CubeSampling_NparOLS
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T12:20:31.049701+00:00
-- url     : https://prove2.me/theorems/68e2e847-1f4b-4cc7-b4ad-87a40f4d8432
-- title:
--   Parametric threshold of ordinary least squares
-- statement:
--   The least integer $N \ge 1$ such that the worst-subspace OLS risk satisfies
--   $$
--   \sup_{V}\ \sup_{\hat\theta \text{ OLS}}\ \sup_{\theta} Q_{1-\delta,\theta}\bigl(\|\hat\theta - \theta\|_2^2\bigr) \le A\sigma^2\,\frac{m + \log(1/\delta)}{n} \qquad\text{for every } n \ge N,
--   $$
--   and $\infty$ if there is none. It is the analogue of Definition 1.3 for OLS in place of the minimax estimator.
-- source:
--   Weinberger, Subspace Uncertainty and Sharp Sampling Thresholds on the Boolean Cube, arXiv:2610.12358 (version of 2 Nov 2026), Definition 1.3 and Theorem 1.5, p.4

import Mathlib
import Definitions.Def_CubeSampling_olsWorstRisk
open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace CubeSampling

/-- The parametric threshold of ordinary least squares: the least integer `N ≥ 1` such that the
worst-subspace OLS risk is at most `Aσ² (m + log(1/δ)) / n` for every `n ≥ N` (Weinberger, *Subspace Uncertainty and Sharp Sampling Thresholds on the Boolean Cube*, arXiv:2610.12358 (version of 2 Nov 2026, sha256 43fdcd90…4f79), Definition 1.3
and Theorem 1.5, p.4); `⊤` when no such `N` exists. -/
noncomputable def NparOLS (d k m : ℕ) (A σ δ : ℝ) : ℕ∞ :=
  sInf ((fun N : ℕ => (N : ℕ∞)) '' {N : ℕ | 1 ≤ N ∧ ∀ n : ℕ, N ≤ n →
    olsWorstRisk d k m σ n δ ≤ ENNReal.ofReal (A * σ ^ 2 * (m + Real.log (1 / δ)) / n)})

end CubeSampling


