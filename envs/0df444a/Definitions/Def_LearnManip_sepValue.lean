-- Prove2me | Definitions.Def_LearnManip_sepValue
-- name    : LearnManip_sepValue
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T18:55:42.924221+00:00
-- url     : https://prove2.me/theorems/648d8c0d-fad9-4e46-9d36-57339639789e
-- title:
--   Separable function $\mu/(1-\alpha)+g(s,c)$
-- statement:
--   For a function $g(s,c)$, the additively separable function
--   $$v(\mu,s,c)=\frac{\mu}{1-\alpha}+g(s,c).$$
--   The first term is the discounted payoff without manipulation, and the second is the gain from manipulation.
-- source:
--   Keppo, Kim, Zhang, Learning Manipulation Through Information Dissemination (SSRN 3465030, 2021-09-04), (14), p.13; (EC.14), p.ec9 (PDF 48)

import Mathlib
import Definitions.Def_LearnManip_Params

open scoped NNReal ENNReal
open MeasureTheory ProbabilityTheory

namespace LearnManip

/-- The additively separable function `v(μ, s, c) = μ/(1−α) + g(s, c)` of (14), p.13, and (EC.14),
p.ec9 (PDF 48), of Keppo, Kim, Zhang (SSRN 3465030, 2021-09-04). -/
noncomputable def sepValue (P : Params) (g : ℝ≥0 → ℝ≥0 → ℝ) (μ : ℝ) (s c : ℝ≥0) : ℝ :=
  μ / (1 - (P.α : ℝ)) + g s c

end LearnManip


