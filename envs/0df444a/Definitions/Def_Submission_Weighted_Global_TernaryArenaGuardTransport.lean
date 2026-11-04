-- Prove2me | Definitions.Def_Submission_Weighted_Global_TernaryArenaGuardTransport
-- name    : Submission_Weighted_Global_TernaryArenaGuardTransport
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-03T21:28:47.465867+00:00
-- url     : https://prove2.me/theorems/b7095836-6bb4-4b23-9369-e94db88016a0
-- title:
--   Ternary Arena Guard Transport
-- statement:
--   Definitions and structural lemmas for Ternary Arena Guard Transport, from the weighted-cache deterministic 3SUM development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryArenaGuardTransport.lean

import Definitions.Def_Submission_Weighted_GlobalBank
import Definitions.Def_Submission_Weighted_Global_TernaryArenaCandidateGuard
import Definitions.Def_Submission_Weighted_Global_TernaryArenaScoreScan
import Definitions.Def_Submission_Weighted_Global_LightTernaryControllerFull
set_option autoImplicit false
noncomputable section
namespace ThreeSum.WeightedGlobalArenaGuardTransport
open Light TernaryJointType WeightedGlobalLocalParameters WeightedGlobalCoverGoodMaps
open WeightedGlobalArenaSourceSetup WeightedGlobalNativeCompleteFrontend WeightedGlobalArenaLayout
open LightWeightedGlobalSeedScoreFactory WeightedGlobalArenaSeedCandidate WeightedGlobalArenaScoreScan
variable {p m F r : ℕ} [Fact p.Prime]
set_option maxHeartbeats 6000000
set_option maxRecDepth 24000
end ThreeSum.WeightedGlobalArenaGuardTransport


