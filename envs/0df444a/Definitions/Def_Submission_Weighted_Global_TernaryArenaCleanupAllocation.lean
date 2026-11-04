-- Prove2me | Definitions.Def_Submission_Weighted_Global_TernaryArenaCleanupAllocation
-- name    : Submission_Weighted_Global_TernaryArenaCleanupAllocation
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-03T22:20:57.923839+00:00
-- url     : https://prove2.me/theorems/947706b5-32b8-4a2a-8958-f1b58617c617
-- title:
--   Ternary Arena Cleanup Allocation
-- statement:
--   Definitions and structural lemmas for Ternary Arena Cleanup Allocation, from the weighted-cache deterministic 3SUM development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryArenaCleanupAllocation.lean

import Definitions.Def_Submission_Weighted_GlobalBank
import Definitions.Def_Submission_Weighted_Global_TernaryArenaFinalGuardAllocation
import Definitions.Def_Submission_Weighted_Global_TernaryArenaCleanupLayout
set_option autoImplicit false
noncomputable section
namespace ThreeSum.WeightedGlobalArenaCleanupAllocation
open Light WeightedGlobalArenaLayout WeightedGlobalArenaSourceSetup WeightedGlobalArenaPrefixFootprints
open WeightedGlobalCoverGoodMaps WeightedGlobalLocalParameters WeightedGlobalArenaAllocation TernaryExtensionEncoding
set_option maxHeartbeats 8000000
variable {p m F r J : ℕ} [Fact p.Prime]
end ThreeSum.WeightedGlobalArenaCleanupAllocation


