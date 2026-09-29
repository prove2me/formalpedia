-- Prove2me | Definitions.Def_OnlinePrimalDual_Framework_dualSum
-- name    : OnlinePrimalDual_Framework_dualSum
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-21T05:32:31.376139+00:00
-- url     : https://prove2.me/theorems/3eaef765-a310-436b-ad13-fdce3d69c9a6
-- title:
--   Accumulated dual value charged against a primal variable's packing constraint
-- statement:
--   `dualSum inst y i := ∑_{j ∣ i ∈ S(j)} y_j`, the left-hand side of primal variable `i`'s
--   packing/dual constraint `∑_{j ∣ i ∈ S(j)} y_j ≤ c_i` (Fig. 4.1). Used to state packing
--   feasibility and violation, and as the argument to Algorithms 2 and 3's update rules for `x_i`.
-- source:
--   Buchbinder & Naor, The Design of Competitive Online Algorithms via a Primal-Dual Approach, FnT TCS 2009, p. 116, Fig. 4.1

import Mathlib
import Definitions.Def_OnlinePrimalDual_Framework_CoveringInstance

namespace OnlinePrimalDual.Framework

/-- The accumulated dual value `∑_{j | i ∈ S(j)} yⱼ` charged against primal variable `i`'s
dual/packing constraint `∑_{j | i ∈ S(j)} yⱼ ≤ cᵢ` (Fig. 4.1, p. 116, PDF p. 27). Used both to
state packing feasibility/violation and, in Section 4.2's algorithms, as the argument to each
algorithm's update rule for `xᵢ`. -/
def dualSum {I J : Type*} [Fintype I] [Fintype J] [DecidableEq I]
    (inst : CoveringInstance I J) (y : J → ℝ) (i : I) : ℝ :=
  ∑ j ∈ Finset.univ.filter (fun j => i ∈ inst.S j), y j

end OnlinePrimalDual.Framework


