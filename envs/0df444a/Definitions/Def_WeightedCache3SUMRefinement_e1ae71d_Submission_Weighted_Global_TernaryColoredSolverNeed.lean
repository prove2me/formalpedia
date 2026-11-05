-- Prove2me | Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_TernaryColoredSolverNeed
-- name    : WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_TernaryColoredSolverNeed
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-04T14:42:50.172768+00:00
-- url     : https://prove2.me/theorems/81569d6f-2953-4fd8-9ea9-d8caaac94cbc
-- title:
--   TernaryColoredSolverNeed
-- statement:
--   Definitions and structural lemmas for TernaryColoredSolverNeed, from the weighted-cache deterministic 3SUM development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/e1ae71db2231f172c6541820e2ce0a54aa14fc64/Submission/Weighted/Global/TernaryColoredSolverNeed.lean

import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_GlobalBank
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_TernaryArenaAllocationResources
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_LightTernaryColorPreparationProof
import Definitions.Def_Submission_ThreeSum_TernaryColorPreludeResources_w3sum_ac885d1
set_option autoImplicit false
namespace WeightedCache3SUMRefinement_e1ae71d
open _root_.ThreeSum
noncomputable section
namespace ThreeSum.WeightedGlobalColoredSolverNeed
open Light WeightedGlobalArenaLayout WeightedGlobalArenaAllocation WeightedGlobalArenaPrefixFootprints
open WeightedGlobalCoverGoodMaps WeightedGlobalLocalParameters LightWeightedGlobalColorPreparation
set_option maxHeartbeats 500000
set_option maxRecDepth 24000
variable {p m F : ℕ} [Fact p.Prime]
def preparationCells (M b n U : ℕ) : ℕ :=
  1000*(n+U+LightWeightedGlobalDimensions.J M b n U+3)^2*
    (2^(LightWeightedGlobalDimensions.J M b n U)+1)
def need {maps : Fin F→Weight m p} {τ cap M b K H drift scale : ℕ}
    (Alloc : Allocation maps τ cap M b K H drift scale) (n U : ℕ) : Need :=
  let J := LightWeightedGlobalDimensions.J M b n U
  let a := WeightedGlobalArenaAllocationResources.need Alloc n U
  ⟨LightTernaryColorPrelude.word n U+LightTernarySignedMatrix.word U b J+
    LightTernaryCarryCodes.word J (2^J)+LightWeightedGlobalDimensions.word M b p K n U+a.word+100,
    preparationCells M b n U+a.cells,a.depth+LightTernaryColorPrelude.depth n+1000⟩
def fixedNeed {maps : Fin F→Weight m p} {τ cap M b K H drift scale : ℕ}
    (Alloc : Allocation maps τ cap M b K H drift scale) (κ n _U : ℕ) : Need :=need Alloc n (n^κ)
end ThreeSum.WeightedGlobalColoredSolverNeed
end
end WeightedCache3SUMRefinement_e1ae71d


