-- Prove2me | Definitions.Def_OnlinePrimalDual_Framework_alg2X
-- name    : OnlinePrimalDual_Framework_alg2X
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-21T05:34:27.576332+00:00
-- url     : https://prove2.me/theorems/e24d4942-7693-43ed-9077-20f431138ad6
-- title:
--   Algorithm 2's (the continuous algorithm) final primal value
-- statement:
--   Algorithm 2's update rule (p. 121), `x_i ← (1/d)(exp((ln(1+d)/c_i)·∑_{j ∣ i ∈ S(j)} y_j) - 1)`,
--   is already a closed form in the accumulated dual sum; `alg2X inst y i` evaluates it at the
--   final accumulated sum `dualSum inst y i`.
-- source:
--   Buchbinder & Naor, The Design of Competitive Online Algorithms via a Primal-Dual Approach, FnT TCS 2009, p. 121, Algorithm 2

import Mathlib
import Definitions.Def_OnlinePrimalDual_Framework_CoveringInstance
import Definitions.Def_OnlinePrimalDual_Framework_dualSum

namespace OnlinePrimalDual.Framework

/-- The final value Algorithm 2 (the continuous algorithm, p. 121, PDF p. 32) assigns to primal
variable `xᵢ`: `xᵢ = (1/d)(exp((ln(1+d)/cᵢ) · ∑_{j | i ∈ S(j)} yⱼ) − 1)`, exactly the update
function stated in Algorithm 2's step (1b), evaluated at the final accumulated dual sum
`dualSum inst y i` (the exponential only ever depends on dual variables of constraints already
revealed, since `y` is `0` on constraints not yet arrived). -/
noncomputable def alg2X {I J : Type*} [Fintype I] [Fintype J] [DecidableEq I]
    (inst : CoveringInstance I J) (y : J → ℝ) (i : I) : ℝ :=
  (1 / inst.d) * (Real.exp (Real.log (1 + inst.d) / inst.c i * dualSum inst y i) - 1)

end OnlinePrimalDual.Framework


