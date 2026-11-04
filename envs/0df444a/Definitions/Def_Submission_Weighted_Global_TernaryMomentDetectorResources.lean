-- Prove2me | Definitions.Def_Submission_Weighted_Global_TernaryMomentDetectorResources
-- name    : Submission_Weighted_Global_TernaryMomentDetectorResources
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-03T15:14:56.881673+00:00
-- url     : https://prove2.me/theorems/7054852e-48a0-47f6-9b55-7a3bd99a5f19
-- title:
--   Ternary Moment Detector Resources
-- statement:
--   Definitions and structural lemmas for Ternary Moment Detector Resources, from the weighted-cache deterministic 3SUM development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryMomentDetectorResources.lean

import Definitions.Def_Submission_Weighted_GlobalBank
import Definitions.Def_Submission_Weighted_Global_TernaryMomentWeightBounds
import Definitions.Def_Submission_ThreeSum_PolynomialResources
set_option autoImplicit false
noncomputable section
namespace ThreeSum.WeightedGlobalMomentDetectorResources
open WeightedGlobalNativeMomentBounds StageBounds
def input (B U H : ℕ) : ℕ := U+B*(2*U+1)^(2*H)
def need (B U H : ℕ) : Light.Need :=
  ⟨detectorWord (input B U H) H,(2*H+1)*(B+1),5⟩
def coefficient (B H : ℕ) : ℕ :=
  ((LightMomentDeterminant.wordCoefficient H).toNat+1)*
    (B*2^(2*H)+1)^(LightMomentDeterminant.wordDegree H+1)+
  (2*H+1)*(B+1)+5
def degree (H : ℕ) : ℕ :=(2*H+1)*(LightMomentDeterminant.wordDegree H+1)
end ThreeSum.WeightedGlobalMomentDetectorResources


