-- Prove2me | Definitions.Def_Submission_Weighted_Global_TernaryArenaCandidateGuardAllocation
-- name    : Submission_Weighted_Global_TernaryArenaCandidateGuardAllocation
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-03T22:10:22.97831+00:00
-- url     : https://prove2.me/theorems/72f2d46c-2528-475c-bcbf-a2d60da589ff
-- title:
--   Ternary Arena Candidate Guard Allocation
-- statement:
--   Definitions and structural lemmas for Ternary Arena Candidate Guard Allocation, from the weighted-cache deterministic 3SUM development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryArenaCandidateGuardAllocation.lean

import Definitions.Def_Submission_Weighted_GlobalBank
import Definitions.Def_Submission_Weighted_Global_TernaryArenaCandidateGuard
import Definitions.Def_Submission_Weighted_Global_TernaryArenaAllocationResources
import Definitions.Def_Submission_Weighted_Global_TernaryArenaPrimitiveBounds
set_option autoImplicit false
noncomputable section
namespace ThreeSum.WeightedGlobalArenaCandidateGuardAllocation
open Light WeightedGlobalLocalParameters WeightedGlobalCoverGoodMaps WeightedGlobalArenaLayout
open WeightedGlobalArenaSourceSetup WeightedGlobalArenaSeedCandidate WeightedGlobalArenaPrefixFootprints
open WeightedGlobalArenaAllocation LightWeightedGlobalSeedScoreFactory
variable {p m F r : ℕ} [Fact p.Prime]
set_option maxHeartbeats 6000000
end ThreeSum.WeightedGlobalArenaCandidateGuardAllocation


