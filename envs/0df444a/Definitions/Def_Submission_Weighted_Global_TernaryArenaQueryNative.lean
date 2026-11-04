-- Prove2me | Definitions.Def_Submission_Weighted_Global_TernaryArenaQueryNative
-- name    : Submission_Weighted_Global_TernaryArenaQueryNative
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-03T16:32:16.672335+00:00
-- url     : https://prove2.me/theorems/1d8b29e0-3787-40a0-81d8-ca2002fbf434
-- title:
--   Ternary Arena Query Native
-- statement:
--   Definitions and structural lemmas for Ternary Arena Query Native, from the weighted-cache deterministic 3SUM development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryArenaQueryNative.lean

import Definitions.Def_Submission_Weighted_GlobalBank
import Definitions.Def_Submission_Weighted_Global_TernaryArenaQueryModel
import Definitions.Def_Submission_ThreeSum_TernaryCoefficientCodes
import Theorems.Thm_Light_Ends_block

set_option autoImplicit false
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


