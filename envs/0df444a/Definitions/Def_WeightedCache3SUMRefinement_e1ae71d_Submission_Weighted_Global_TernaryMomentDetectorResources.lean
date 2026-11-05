-- Prove2me | Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_TernaryMomentDetectorResources
-- name    : WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_TernaryMomentDetectorResources
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-04T12:25:45.969781+00:00
-- url     : https://prove2.me/theorems/eef34d1a-bd7f-4aa4-9629-65e175cc68b8
-- title:
--   TernaryMomentDetectorResources
-- statement:
--   Definitions and structural lemmas for TernaryMomentDetectorResources, from the weighted-cache deterministic 3SUM development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/e1ae71db2231f172c6541820e2ce0a54aa14fc64/Submission/Weighted/Global/TernaryMomentDetectorResources.lean

import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_GlobalBank
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_TernaryMomentWeightBounds
import Definitions.Def_Submission_ThreeSum_PolynomialResources
set_option autoImplicit false
namespace WeightedCache3SUMRefinement_e1ae71d
open _root_.ThreeSum
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
end
end WeightedCache3SUMRefinement_e1ae71d


