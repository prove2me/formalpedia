-- Prove2me | Definitions.Def_OnlinePrimalDual_BoundedAllocation_packingFeasible
-- name    : OnlinePrimalDual_BoundedAllocation_packingFeasible
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-21T06:04:53.588813+00:00
-- url     : https://prove2.me/theorems/8a7b6b31-0068-4335-8507-741f98730ea0
-- title:
--   Feasibility for the fractional packing (dual) allocation LP
-- statement:
--   A fractional allocation `y(i,j)` is feasible iff non-negative, each item allocated at most
--   fully (`∀j, Σ_{i∈S(j)} y(i,j) ≤ 1`), and each buyer's budget respected
--   (`∀i, Σ_{j|i∈S(j)} b(j)y(i,j) ≤ B(i)`).
-- source:
--   Buchbinder & Naor, The Design of Competitive Online Algorithms via a Primal-Dual Approach, FnT TCS 2009, p. 239, Fig. 13.1

import Mathlib
import Definitions.Def_OnlinePrimalDual_BoundedAllocation_AllocationInstance

namespace OnlinePrimalDual.BoundedAllocation

/-- Feasibility for the fractional packing (dual) LP of Fig. 13.1: `y i j` is the fraction of
item `j` allocated to buyer `i`, non-negative, each item fully allocated at most once
(`∀j, ∑_{i∈S(j)} y(i,j) ≤ 1`), and each buyer's budget respected
(`∀i, ∑_{j|i∈S(j)} b(j)y(i,j) ≤ B(i)`). -/
def packingFeasible {I J : Type*} [Fintype I] [Fintype J] [DecidableEq I]
    (inst : AllocationInstance I J) (y : I → J → ℝ) : Prop :=
  (∀ i j, 0 ≤ y i j) ∧
  (∀ j, ∑ i ∈ inst.S j, y i j ≤ 1) ∧
  (∀ i, ∑ j ∈ Finset.univ.filter (fun j => i ∈ inst.S j), inst.b j * y i j ≤ inst.B i)

end OnlinePrimalDual.BoundedAllocation


