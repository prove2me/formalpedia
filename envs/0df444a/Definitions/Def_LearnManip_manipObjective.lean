-- Prove2me | Definitions.Def_LearnManip_manipObjective
-- name    : LearnManip_manipObjective
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T18:55:43.712168+00:00
-- url     : https://prove2.me/theorems/4f9e3298-dd21-4503-a2e8-8d8ea9bdf521
-- title:
--   Dissemination utility, the objective of (15)
-- statement:
--   For a function $g(s,c)$, the objective of the DP equation (15) at a quantity $q$, the dissemination utility (16):
--   $$-cq+\alpha g\bigl(\tfrac{s}{1+sq},c\eta\bigr)+\frac{\sigma^2_{\mu^q}}{2\gamma(1-\alpha)^2}.$$
--   It trades the cost of dissemination and the loss of future variance against the room for distortion created now.
-- source:
--   Keppo, Kim, Zhang, Learning Manipulation Through Information Dissemination (SSRN 3465030, 2021-09-04), (15), p.13, (16), p.14

import Mathlib
import Definitions.Def_LearnManip_Params
import Definitions.Def_LearnManip_postVar
import Definitions.Def_LearnManip_meanVar

open scoped NNReal ENNReal
open MeasureTheory ProbabilityTheory

namespace LearnManip

/-- The objective of the DP equation (15), p.13 (the dissemination utility (16), p.14), of Keppo, Kim,
Zhang (SSRN 3465030, 2021-09-04), at the quantity `q`:
`−c q + α g(s/(1+sq), cη) + σ²_{μ^q} / (2γ(1−α)²)`. -/
noncomputable def manipObjective (P : Params) (g : ℝ≥0 → ℝ≥0 → ℝ) (s c q : ℝ≥0) : ℝ :=
  -((c : ℝ) * q) + (P.α : ℝ) * g (postVar s q) (c * P.η)
    + (meanVar s q : ℝ) / (2 * (P.γ : ℝ) * (1 - (P.α : ℝ)) ^ 2)

end LearnManip


