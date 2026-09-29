-- Prove2me | Definitions.Def_OnlinePrimalDual_BoundedAllocation_packingValue
-- name    : OnlinePrimalDual_BoundedAllocation_packingValue
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-21T06:05:28.516713+00:00
-- url     : https://prove2.me/theorems/c8e790d6-a74c-4a4c-b559-c9794fa01a23
-- title:
--   The value (total seller profit) of a fractional allocation
-- statement:
--   `packingValue inst y := Σ_j Σ_{i∈S(j)} b(j)y(i,j)`, the packing/dual objective of Fig. 13.1.
-- source:
--   Buchbinder & Naor, The Design of Competitive Online Algorithms via a Primal-Dual Approach, FnT TCS 2009, p. 239, Fig. 13.1

import Mathlib
import Definitions.Def_OnlinePrimalDual_BoundedAllocation_AllocationInstance

namespace OnlinePrimalDual.BoundedAllocation

/-- The value (total seller profit) of a fractional allocation `y`, the packing/dual objective
of Fig. 13.1: `∑_j ∑_{i∈S(j)} b(j)y(i,j)`. -/
def packingValue {I J : Type*} [Fintype I] [Fintype J] [DecidableEq I]
    (inst : AllocationInstance I J) (y : I → J → ℝ) : ℝ :=
  ∑ j, ∑ i ∈ inst.S j, inst.b j * y i j

end OnlinePrimalDual.BoundedAllocation


