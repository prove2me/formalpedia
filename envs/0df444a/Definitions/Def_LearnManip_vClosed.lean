-- Prove2me | Definitions.Def_LearnManip_vClosed
-- name    : LearnManip_vClosed
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T19:01:03.876775+00:00
-- url     : https://prove2.me/theorems/9efbeb7b-baf3-4e57-a464-2666e84af1bf
-- title:
--   Closed form of the optimal value
-- statement:
--   The closed form of the optimal value,
--   $$v(\mu,s,c)=\frac{\mu}{1-\alpha}+G(s,c),$$
--   with $G$ the closed form (18).
-- source:
--   Keppo, Kim, Zhang, Learning Manipulation Through Information Dissemination (SSRN 3465030, 2021-09-04), (14), p.13, and (18), p.15

import Mathlib
import Definitions.Def_LearnManip_Params
import Definitions.Def_LearnManip_sepValue
import Definitions.Def_LearnManip_Gclosed

open scoped NNReal ENNReal
open MeasureTheory ProbabilityTheory

namespace LearnManip

/-- The closed form of the optimal value, (14), p.13, with (18), p.15, of Keppo, Kim, Zhang (SSRN
3465030, 2021-09-04): `v(μ, s, c) = μ/(1−α) + G(s, c)`. -/
noncomputable def vClosed (P : Params) : ℝ → ℝ≥0 → ℝ≥0 → ℝ := sepValue P (Gclosed P)

end LearnManip


