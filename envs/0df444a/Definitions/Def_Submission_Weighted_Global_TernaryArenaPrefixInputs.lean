-- Prove2me | Definitions.Def_Submission_Weighted_Global_TernaryArenaPrefixInputs
-- name    : Submission_Weighted_Global_TernaryArenaPrefixInputs
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-03T23:47:10.301192+00:00
-- url     : https://prove2.me/theorems/0fba33f2-ea89-43e6-9628-4e98a46c7c79
-- title:
--   Ternary Arena Prefix Inputs
-- statement:
--   Definitions and structural lemmas for Ternary Arena Prefix Inputs, from the weighted-cache deterministic 3SUM development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryArenaPrefixInputs.lean

import Definitions.Def_Submission_Weighted_GlobalBank
import Definitions.Def_Submission_Weighted_Global_TernaryArenaOriginalInputs
import Definitions.Def_Submission_Weighted_Global_TernaryArenaPrefixState
import Definitions.Def_Submission_Weighted_Global_TernaryArenaPreparedMemory
import Definitions.Def_Submission_Weighted_Global_TernaryArenaSeedDataReads
import Definitions.Def_Submission_Weighted_Global_TernaryArenaTensorGuardAllocation
import Definitions.Def_Submission_Weighted_Global_TernaryArenaCandidateGuardAllocation
import Definitions.Def_Submission_Weighted_Global_TernaryArenaCandidateScoreBounds
set_option autoImplicit false
noncomputable section
namespace ThreeSum.WeightedGlobalArenaPrefixInputs
open Light TernaryJointType WeightedGlobalLocalParameters WeightedGlobalCoverGoodMaps WeightedGlobalArenaLayout
open WeightedGlobalArenaSourceSetup WeightedGlobalArenaSeedCandidate WeightedGlobalArenaSeedData
open WeightedGlobalArenaSelectedBudgets WeightedGlobalArenaAllocation
open TernaryOriginalRowMenu WeightedGlobalNativeCompleteFrontend
open TernaryExtensionEncoding
open LightWeightedGlobalSeedScoreFactory
variable {p m F : ℕ} [Fact p.Prime]
variable {E : Type*} [Field E] [Fintype E] [DecidableEq E] [Algebra (ZMod p) E]
set_option maxHeartbeats 10000000
set_option maxRecDepth 24000
end ThreeSum.WeightedGlobalArenaPrefixInputs


