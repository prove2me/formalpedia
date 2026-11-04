-- Prove2me | Definitions.Def_Submission_Weighted_Global_TernaryArenaPhaseFrames
-- name    : Submission_Weighted_Global_TernaryArenaPhaseFrames
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-04T00:56:42.344129+00:00
-- url     : https://prove2.me/theorems/f7f04aaf-101c-4171-a47d-e2b620c4fb93
-- title:
--   Ternary Arena Phase Frames
-- statement:
--   Definitions and structural lemmas for Ternary Arena Phase Frames, from the weighted-cache deterministic 3SUM development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryArenaPhaseFrames.lean

import Definitions.Def_Submission_Weighted_GlobalBank
import Definitions.Def_Submission_Weighted_Global_TernaryArenaPhase
import Theorems.Thm_ThreeSum_WeightedGlobalArenaFrontBounds_capacity

set_option autoImplicit false
noncomputable section
namespace ThreeSum.WeightedGlobalArenaPhaseFrames
open Light WeightedGlobalArenaLayout WeightedGlobalArenaSourceSetup WeightedGlobalArenaSeedCandidate
open LightWeightedGlobalSeedScoreFactory LightWeightedGlobalControllerFactory
open WeightedGlobalArenaControllerPlan WeightedGlobalArenaScoreScan
variable {p m F : ℕ} [Fact p.Prime]
set_option maxHeartbeats 6000000
set_option maxRecDepth 24000
def Stable (I : Input) (x : ℕ) : Prop :=
  x<addr I.free I.capacity 1 ∨
    (addr I.free I.capacity 2≤x ∧ x<addr I.free I.capacity 3)
open TernaryJointType WeightedGlobalLocalParameters WeightedGlobalCoverGoodMaps
open WeightedGlobalArenaSeedData WeightedGlobalArenaPrefixInputs WeightedGlobalNativeCompleteFrontend
open WeightedGlobalArenaSelectedBudgets WeightedGlobalArenaAllocation WeightedGlobalArenaPhase
variable {E : Type*} [Field E] [Fintype E] [DecidableEq E] [Algebra (ZMod p) E]
end ThreeSum.WeightedGlobalArenaPhaseFrames


