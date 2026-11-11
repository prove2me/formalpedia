-- Prove2me | Definitions.Def_TightContinualCounting_LowerBounds_errors
-- name    : TightContinualCounting_LowerBounds_errors
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-10T07:03:40.30868+00:00
-- url     : https://prove2.me/theorems/4ac0ac97-4927-4bbb-9bcf-e2c9cee31cf4
-- title:
--   Worst-case mean squared and maximum per-coordinate squared errors
-- statement:
--   Let $M(x)$ be the output law on $\mathbb R^n$ for a binary input $x$, and write $(A_nx)_t=\sum_{i=1}^t x_i$. Define the two squared-error measures by
--
--   $$
--   \operatorname{MeanSE}(M)=\max_x\mathbb E_{y\sim M(x)}\left[\frac1n\sum_{t=1}^n(y_t-(A_nx)_t)^2\right],\qquad
--   \operatorname{MaxSE}(M)=\max_x\max_{t\in[n]}\mathbb E_{y\sim M(x)}[(y_t-(A_nx)_t)^2].
--   $$
--
--   Both values are nonnegative extended real numbers. The maximum over coordinates is outside the expectation in MaxSE; MeanSE averages squares before taking expectation. Together with the referenced expected sup norm, these are the three loss measures of Theorem 1.
--
--   **Formalization Note** Coordinates use `Fin n`; nonnegative lower integrals and suprema in $\mathbb R_{\ge0}\cup\{+\infty\}$ preserve infinite losses. The theorems assume $n\ge1$. The total definition gives MeanSE and MaxSE zero for $n=0$ (an unused domain).
-- source:
--   Charlie Harrison, Ethan Leeman, Tight Lower Bounds for Differentially Private Continual Counting, STOC 2027 submission #1453 (October 2026), p.2, definitions of MeanSE and MaxSE

import Mathlib
import Definitions.Def_ContinualCounting_prefixSum
import Definitions.Def_ContinualCounting_linfError

open MeasureTheory
open scoped ENNReal

namespace TightContinualCounting.LowerBounds

/-- Worst-input expected average squared error, including infinite values (p.2). -/
noncomputable def meanSE {n : ℕ}
    (M : (Fin n → Bool) → Measure (Fin n → ℝ)) : ℝ≥0∞ :=
  ⨆ x, ∫⁻ y, ENNReal.ofReal
    ((∑ t : Fin n, (y t - ContinualCounting.prefixSum (ContinualCounting.bitVec x) t) ^ 2)
      / (n : ℝ)) ∂(M x)

/-- Worst input and coordinate expected squared error (p.2). -/
noncomputable def maxSE {n : ℕ}
    (M : (Fin n → Bool) → Measure (Fin n → ℝ)) : ℝ≥0∞ :=
  ⨆ x, ⨆ t : Fin n, ∫⁻ y, ENNReal.ofReal
    ((y t - ContinualCounting.prefixSum (ContinualCounting.bitVec x) t) ^ 2) ∂(M x)

end TightContinualCounting.LowerBounds


