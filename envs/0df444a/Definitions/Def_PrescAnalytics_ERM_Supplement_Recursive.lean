-- Prove2me | Definitions.Def_PrescAnalytics_ERM_Supplement_Recursive
-- name    : PrescAnalytics_ERM_Supplement_Recursive
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-23T19:51:58.839961+00:00
-- url     : https://prove2.me/theorems/c858ddb0-70bb-4546-a2bb-ecdbee39ee23
-- title:
--   Recursive naïve-kernel weights
-- statement:
--   The bandwidth of observation $i$ is $h_i=Ci^{-\delta}$, independent of the final sample size. With the naïve kernel,
--   $$w_{N,i}(x)=\frac{K((x^i-x)/h_i)}{\sum_{j=1}^N K((x^j-x)/h_j)}.$$
--   The construction keeps the per-observation bandwidth distinct from $h_N$. Lean uses $i+1$ in this bandwidth because observations start at index zero; vanishing denominators give zero weights.
-- source:
--   Bertsimas, Kallus, From Predictive to Prescriptive Analytics, arXiv:1402.5481v4, p. 11, Eq. (14)

import Mathlib
import Definitions.Def_PrescAnalytics_ERM_Supplement_Kernel

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal

namespace PrescAnalytics.ERM.Supplement

/-- (14), with observation i+1 carrying bandwidth C(i+1)^(-δ); i starts at zero. -/
noncomputable def recursiveScore {dx : ℕ} (C δ : ℝ)
    (xs : ℕ → EuclideanSpace ℝ (Fin dx)) (x : EuclideanSpace ℝ (Fin dx)) (i : ℕ) : ℝ :=
  kernel .naive ((bandwidth C δ (i + 1))⁻¹ • (xs i - x))

noncomputable def recursiveWeight {dx : ℕ} (C δ : ℝ)
    (xs : ℕ → EuclideanSpace ℝ (Fin dx)) (x : EuclideanSpace ℝ (Fin dx))
    (N i : ℕ) : ℝ :=
  if i < N then recursiveScore C δ xs x i /
    (∑ j ∈ Finset.range N, recursiveScore C δ xs x j) else 0

end PrescAnalytics.ERM.Supplement


