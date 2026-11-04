-- Prove2me | Definitions.Def_Submission_Weighted_Global_TernaryArenaCandidateScoreBounds
-- name    : Submission_Weighted_Global_TernaryArenaCandidateScoreBounds
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-03T22:10:52.17048+00:00
-- url     : https://prove2.me/theorems/533f2b4b-e8c5-4873-9299-2e9353c05cf0
-- title:
--   Ternary Arena Candidate Score Bounds
-- statement:
--   Definitions and structural lemmas for Ternary Arena Candidate Score Bounds, from the weighted-cache deterministic 3SUM development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryArenaCandidateScoreBounds.lean

import Definitions.Def_Submission_Weighted_GlobalBank
import Definitions.Def_Submission_Weighted_Global_TernaryArenaCandidateGuard
import Definitions.Def_Submission_Weighted_Global_TernaryArenaTensorBounds
import Definitions.Def_Submission_Weighted_Global_TernaryArenaAllocationResources
set_option autoImplicit false
noncomputable section
namespace ThreeSum.WeightedGlobalArenaCandidateScoreBounds
open WeightedGlobalNativePairMoments WeightedGlobalNativeMomentBounds WeightedGlobalNativeTensorScore
open WeightedGlobalArenaPrefixFootprints WeightedGlobalArenaSourceSetup WeightedGlobalArenaSourceBounds
open WeightedGlobalArenaSeedCandidate LightWeightedGlobalSeedScoreFactory
open WeightedGlobalCoverGoodMaps WeightedGlobalLocalParameters WeightedGlobalNativeCompleteFrontend
open scoped BigOperators
variable {p m F r : ℕ} [Fact p.Prime]
set_option maxHeartbeats 6000000
end ThreeSum.WeightedGlobalArenaCandidateScoreBounds


