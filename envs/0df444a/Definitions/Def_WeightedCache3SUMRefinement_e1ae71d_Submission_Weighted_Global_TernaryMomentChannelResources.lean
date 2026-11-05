-- Prove2me | Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_TernaryMomentChannelResources
-- name    : WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_TernaryMomentChannelResources
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-04T12:31:31.644278+00:00
-- url     : https://prove2.me/theorems/1bafb035-cb39-42f5-8150-6fbd02158806
-- title:
--   TernaryMomentChannelResources
-- statement:
--   Definitions and structural lemmas for TernaryMomentChannelResources, from the weighted-cache deterministic 3SUM development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/e1ae71db2231f172c6541820e2ce0a54aa14fc64/Submission/Weighted/Global/TernaryMomentChannelResources.lean

import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_GlobalBank
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_TernaryMomentDetectorResources
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_TernaryPhysicalPairWordBounds
import Definitions.Def_Submission_ThreeSum_TernaryMomentSchedule
set_option autoImplicit false
namespace WeightedCache3SUMRefinement_e1ae71d
open _root_.ThreeSum
noncomputable section
namespace ThreeSum.WeightedGlobalMomentChannelResources
open WeightedGlobalMomentWeightBounds WeightedGlobalNativeMomentBounds StageBounds
def scoreBound (B U K : ℕ) : ℕ :=B*leftBound U K*rightBound U K
def coefficient (K : ℕ) : ℕ :=
  1+2*(2^K+1)*2^K+3+2*(TernaryMomentSchedule.channels (K+1)).length*2^K+(K+1)+10
def need (B U K : ℕ) : Light.Need :=
  ⟨coefficient K*(B+1)*(U+1)^(2*K+1),0,0⟩
end ThreeSum.WeightedGlobalMomentChannelResources
end
end WeightedCache3SUMRefinement_e1ae71d


