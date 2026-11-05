-- Prove2me | Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_TernaryArenaQueryNative
-- name    : WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_TernaryArenaQueryNative
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-04T13:23:13.468194+00:00
-- url     : https://prove2.me/theorems/b83e5323-a11d-4718-ac38-f7967e8abdc0
-- title:
--   TernaryArenaQueryNative
-- statement:
--   Definitions and structural lemmas for TernaryArenaQueryNative, from the weighted-cache deterministic 3SUM development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/e1ae71db2231f172c6541820e2ce0a54aa14fc64/Submission/Weighted/Global/TernaryArenaQueryNative.lean

import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_GlobalBank
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_TernaryArenaQueryModel
import Definitions.Def_Submission_ThreeSum_TernaryCoefficientCodes
import Theorems.Thm_Light_Ends_block

set_option autoImplicit false
namespace WeightedCache3SUMRefinement_e1ae71d
open _root_.ThreeSum
noncomputable section
namespace ThreeSum.WeightedGlobalArenaQueryModel
open TernaryJointType WeightedGlobalLocalParameters WeightedGlobalCoverGoodMaps TernaryCoverHashes
open TernaryWantedBatchIndex TernaryExtensionEncoding
variable {m p F r : ℕ} [Fact p.Prime]
set_option maxHeartbeats 2000000
set_option maxRecDepth 18000
def nativeRow (maps : Fin F → Weight m p) (τ : ℕ) (targets : ℕ → ℤ) (positions : ℕ → ℕ) (n : ℕ)
    (j : Fin (queries (r := r) maps τ targets positions n).length) : Fin r → ZMod p :=
  fun i => WeightedGlobalGoodOutputCatalog.native (maps (block maps τ targets positions n j i).1)
    (block maps τ targets positions n j i).2
end ThreeSum.WeightedGlobalArenaQueryModel
end
end WeightedCache3SUMRefinement_e1ae71d


