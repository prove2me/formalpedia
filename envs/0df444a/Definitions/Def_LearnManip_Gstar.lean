-- Prove2me | Definitions.Def_LearnManip_Gstar
-- name    : LearnManip_Gstar
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T18:59:13.028783+00:00
-- url     : https://prove2.me/theorems/9494530e-7776-4369-871f-467a8bc45dd4
-- title:
--   The distorted law with density $\Lambda^*$
-- statement:
--   The distorted law of the posterior mean under the optimal rule: the undistorted law of $\mu^{q^*}$ with density $\Lambda^*$, as in (4). By the goal theorem it is the normal law with the boosted mean.
-- source:
--   Keppo, Kim, Zhang, Learning Manipulation Through Information Dissemination (SSRN 3465030, 2021-09-04), (4), p.8, and (19), p.17

import Mathlib
import Definitions.Def_LearnManip_Params
import Definitions.Def_LearnManip_baseLaw
import Definitions.Def_LearnManip_qStar
import Definitions.Def_LearnManip_LambdaStar

open scoped NNReal ENNReal
open MeasureTheory ProbabilityTheory

namespace LearnManip

/-- The distorted law of the posterior mean under the optimal rule: the undistorted law of `μ^{q*}`
with density `Λ*`, (4) and (19), of Keppo, Kim, Zhang (SSRN 3465030, 2021-09-04). -/
noncomputable def Gstar (P : Params) (μ : ℝ) (s c : ℝ≥0) : Measure ℝ :=
  (baseLaw μ s (qStar P s c)).withDensity fun y => ENNReal.ofReal (LambdaStar P μ s c y)

end LearnManip


