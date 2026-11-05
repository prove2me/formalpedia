-- Prove2me | Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_TernaryArenaAllocationResources
-- name    : WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_TernaryArenaAllocationResources
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-04T14:27:01.199788+00:00
-- url     : https://prove2.me/theorems/8bfe49d9-8ed9-4ec1-b658-fbf495367cea
-- title:
--   TernaryArenaAllocationResources
-- statement:
--   Definitions and structural lemmas for TernaryArenaAllocationResources, from the weighted-cache deterministic 3SUM development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/e1ae71db2231f172c6541820e2ce0a54aa14fc64/Submission/Weighted/Global/TernaryArenaAllocationResources.lean

import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_GlobalBank
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_TernaryArenaAllocation
set_option autoImplicit false
namespace WeightedCache3SUMRefinement_e1ae71d
open _root_.ThreeSum
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
end
end WeightedCache3SUMRefinement_e1ae71d


