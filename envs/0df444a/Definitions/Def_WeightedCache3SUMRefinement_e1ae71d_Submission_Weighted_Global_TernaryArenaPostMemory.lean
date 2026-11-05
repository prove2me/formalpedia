-- Prove2me | Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_TernaryArenaPostMemory
-- name    : WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_TernaryArenaPostMemory
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-04T15:16:54.073768+00:00
-- url     : https://prove2.me/theorems/3c3b9fbf-e35b-48cc-8c28-3bdcec564940
-- title:
--   TernaryArenaPostMemory
-- statement:
--   Definitions and structural lemmas for TernaryArenaPostMemory, from the weighted-cache deterministic 3SUM development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/e1ae71db2231f172c6541820e2ce0a54aa14fc64/Submission/Weighted/Global/TernaryArenaPostMemory.lean

import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_GlobalBank
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_TernaryArenaPostSelection
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_TernaryArenaCleanupLayout
set_option autoImplicit false
namespace WeightedCache3SUMRefinement_e1ae71d
open _root_.ThreeSum
noncomputable section
namespace ThreeSum.WeightedGlobalArenaPostMemory
open Light WeightedGlobalArenaLayout WeightedGlobalArenaSourceSetup WeightedGlobalArenaPostSelection
open LightOriginalSurvivors LightOriginalSurvivorPair TernaryExtensionEncoding
open WeightedGlobalCoverGoodMaps
set_option maxHeartbeats 4000000
variable {p m F r J : ℕ} [Fact p.Prime]
structure Metadata (maps : Fin F→Weight m p) (τ : ℕ) (I : Input) (μ : ℕ→ℤ) : Prop where
  codes : Seg μ I.prefixFree ((bankCodes m r).map (fun c => (c : ℤ)))
  powers : LightSubsetAddress.Powers μ (I.prefixFree+4^(N m r)) (2*N m r)
  wanted : Seg μ (addr I.free I.capacity 19) (TernaryWantedBatchIndex.cells (entries (r := r) maps τ I))
end ThreeSum.WeightedGlobalArenaPostMemory
end
end WeightedCache3SUMRefinement_e1ae71d


