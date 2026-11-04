-- Prove2me | Definitions.Def_Submission_Weighted_Global_TernaryArenaTensorGuardAllocation
-- name    : Submission_Weighted_Global_TernaryArenaTensorGuardAllocation
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-03T22:11:22.518235+00:00
-- url     : https://prove2.me/theorems/566693c1-55f8-4b75-b4ee-9135f0a2fc00
-- title:
--   Ternary Arena Tensor Guard Allocation
-- statement:
--   Definitions and structural lemmas for Ternary Arena Tensor Guard Allocation, from the weighted-cache deterministic 3SUM development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryArenaTensorGuardAllocation.lean

import Definitions.Def_Submission_Weighted_GlobalBank
import Definitions.Def_Submission_Weighted_Global_TernaryArenaAllocationResources
import Definitions.Def_Submission_Weighted_Global_TernaryArenaSourceArithmetic
import Definitions.Def_Submission_Weighted_Global_TernaryArenaTensorBounds
import Definitions.Def_Submission_Weighted_Global_TernaryArenaPrimitiveBounds
import Definitions.Def_Submission_Weighted_Global_TernaryArenaQueryTime
import Definitions.Def_Submission_Weighted_Global_TernaryArenaCandidateGuard
import Definitions.Def_Submission_Weighted_Global_TernaryPrefixPreparedHeader
set_option autoImplicit false
noncomputable section
namespace ThreeSum.WeightedGlobalArenaTensorGuardAllocation
open Light TernaryJointType WeightedGlobalLocalParameters WeightedGlobalCoverGoodMaps
open WeightedGlobalArenaSourceSetup WeightedGlobalNativeCompleteFrontend WeightedGlobalArenaLayout
open WeightedGlobalArenaPrefixFootprints WeightedGlobalArenaAllocation
open LightWeightedGlobalSeedScoreFactory WeightedGlobalArenaSeedCandidate
variable {p m F r : ℕ} [Fact p.Prime]
set_option maxHeartbeats 10000000
set_option maxRecDepth 24000
end ThreeSum.WeightedGlobalArenaTensorGuardAllocation


