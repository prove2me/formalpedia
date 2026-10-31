-- Prove2me | Definitions.Def_LearnManip_coeffK
-- name    : LearnManip_coeffK
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T18:55:53.782601+00:00
-- url     : https://prove2.me/theorems/ee00b1a7-4092-4726-abc1-5bc061f63b2f
-- title:
--   The coefficient $1/(2\gamma(1-\alpha)^2)$
-- statement:
--   The constant
--   $$K=\frac{1}{2\gamma(1-\alpha)^2},$$
--   the coefficient of $s$ in the closed form (18) and of $\sigma^2_{\mu^q}$ in (15). It is also the limit slope of the manipulation value.
-- source:
--   Keppo, Kim, Zhang, Learning Manipulation Through Information Dissemination (SSRN 3465030, 2021-09-04), (18), p.15

import Mathlib
import Definitions.Def_LearnManip_Params

open scoped NNReal ENNReal
open MeasureTheory ProbabilityTheory

namespace LearnManip

/-- The coefficient `1 / (2γ(1−α)²)` of `s` in (18), p.15, of Keppo, Kim, Zhang (SSRN 3465030,
2021-09-04). -/
noncomputable def coeffK (P : Params) : ℝ := 1 / (2 * (P.γ : ℝ) * (1 - (P.α : ℝ)) ^ 2)

end LearnManip


