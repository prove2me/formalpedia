-- Prove2me | Definitions.Def_Submission_Weighted_Global_TernaryMomentChannelResources
-- name    : Submission_Weighted_Global_TernaryMomentChannelResources
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-03T15:25:20.043506+00:00
-- url     : https://prove2.me/theorems/c5c7e075-8482-4715-b625-436ccae9520b
-- title:
--   Ternary Moment Channel Resources
-- statement:
--   Definitions and structural lemmas for Ternary Moment Channel Resources, from the weighted-cache deterministic 3SUM development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryMomentChannelResources.lean

import Definitions.Def_Submission_Weighted_GlobalBank
import Definitions.Def_Submission_Weighted_Global_TernaryMomentDetectorResources
import Definitions.Def_Submission_Weighted_Global_TernaryPhysicalPairWordBounds
import Definitions.Def_Submission_ThreeSum_TernaryMomentSchedule
set_option autoImplicit false
noncomputable section
namespace ThreeSum.WeightedGlobalMomentChannelResources
open WeightedGlobalMomentWeightBounds WeightedGlobalNativeMomentBounds StageBounds
def scoreBound (B U K : ℕ) : ℕ :=B*leftBound U K*rightBound U K
def coefficient (K : ℕ) : ℕ :=
  1+2*(2^K+1)*2^K+3+2*(TernaryMomentSchedule.channels (K+1)).length*2^K+(K+1)+10
def need (B U K : ℕ) : Light.Need :=
  ⟨coefficient K*(B+1)*(U+1)^(2*K+1),0,0⟩
end ThreeSum.WeightedGlobalMomentChannelResources


