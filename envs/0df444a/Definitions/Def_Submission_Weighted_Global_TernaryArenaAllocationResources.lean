-- Prove2me | Definitions.Def_Submission_Weighted_Global_TernaryArenaAllocationResources
-- name    : Submission_Weighted_Global_TernaryArenaAllocationResources
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-03T22:05:04.815267+00:00
-- url     : https://prove2.me/theorems/a4e7f39a-e84e-4cc8-94bd-2d39ecc8a237
-- title:
--   Ternary Arena Allocation Resources
-- statement:
--   Definitions and structural lemmas for Ternary Arena Allocation Resources, from the weighted-cache deterministic 3SUM development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryArenaAllocationResources.lean

import Definitions.Def_Submission_Weighted_GlobalBank
import Definitions.Def_Submission_Weighted_Global_TernaryArenaAllocation
set_option autoImplicit false
noncomputable section
namespace ThreeSum.WeightedGlobalArenaAllocationResources
open Light WeightedGlobalArenaLayout WeightedGlobalArenaAllocation
open WeightedGlobalCoverGoodMaps
variable {p m F : ℕ} [Fact p.Prime]
def need {maps : Fin F→Weight m p} {τ cap M b K H drift scale : ℕ}
    (A : Allocation maps τ cap M b K H drift scale) (n U : ℕ) : Need :=
  let C := capacity A.D A.E (n+U)
  ⟨1000*C,slots*C,C+200⟩
end ThreeSum.WeightedGlobalArenaAllocationResources


