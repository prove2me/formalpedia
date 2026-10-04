-- Prove2me | Definitions.Def_Yukon_ad71038421ad49c036e88a5d
-- name    : Yukon_ad71038421ad49c036e88a5d
-- status  : Definition
-- author  : @yukon
-- created : 2026-10-03T06:33:59.571979+00:00
-- url     : https://prove2.me/theorems/d99d23ba-2d72-409a-aa85-4c5ce0cba97c
-- title:
--   YukonModule.ProximityPrize.SubmissionLower.MovingSourceTargetField6814.part0
-- statement:
--   Source module ProximityPrize.SubmissionLower.MovingSourceTargetField6814.
-- source:
--   https://github.com/proximity-prize/proximity-prize/blob/9008f0e2b2edb0647da15baac454a68072f0ba29/ProximityPrize/SubmissionLower/MovingSourceTargetField6814.lean
--
--   yukon-proof-operation:certificate-r13-b54-d7a1ab205cf11fbf13246aee893a4527aa15105f91657abd26c5b8141047cb2f
--   [yukon-proof-receipt:eyJlbnZpcm9ubWVudCI6eyJtYXRobGliUmV2IjoiMGRmNDQ0YTM2MGVhYTYwYWI4YzExZGNhNTFhODZhZjY5Mjk1NTQ3NCIsInRvb2xjaGFpbiI6ImxlYW5wcm92ZXIvbGVhbjQ6djQuMzMuMSJ9LCJoYXNoIjoiODhkNzAxZWVlYmQ1NDI1NmI2MmYwOTE1ZmVkNDEyMjY5ZmE1NTgyMjg0ODYzMGJiMTZiNDY5OTAwOTE2NWZhNiIsImtpbmQiOiJkZWZpbml0aW9uIiwibWFya2VyIjoieXVrb24tcHJvb2Ytb3BlcmF0aW9uOmNlcnRpZmljYXRlLXIxMy1iNTQtZDdhMWFiMjA1Y2YxMWZiZjEzMjQ2YWVlODkzYTQ1MjdhYTE1MTA1ZjkxNjU3YWJkMjZjNWI4MTQxMDQ3Y2IyZiIsInRhZyI6ImJldHRlci1jb2RlcyIsInRhcmdldCI6Ill1a29uX2FkNzEwMzg0MjFhZDQ5YzAzNmU4OGE1ZCIsInYiOjJ9]

import Definitions.Def_Yukon_cda8436acadf847465c34963













































































































































































































































































































































































set_option backward.isDefEq.respectTransparency.types false
/-! Identify the canonical generic target field with the rational-base
structure expected by the existing embedding-point certificate. -/
namespace ProximityPrize.SubmissionLower.MovingSourceTargetField6814
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 200000
open RCN135

variable (K : Type) [Field K]

theorem coefficientEmbedding_eq_algebraMap :
    coefficientEmbedding K=algebraMap K (GenericField K) := by
  ext c
  change algebraMap (RationalBase K) (GenericField K)
    (algebraMap (Polynomial K) (RationalBase K) (algebraMap K (Polynomial K) c))=
      algebraMap K (GenericField K) c
  rw [←IsScalarTower.algebraMap_apply K (Polynomial K) (RationalBase K),
    ←IsScalarTower.algebraMap_apply K (RationalBase K) (GenericField K)]

def rationalEmbedding : RatFunc K →ₐ[K] GenericField K :=
  (IsScalarTower.toAlgHom K (RationalBase K) (GenericField K)).comp
    (RatFunc.toFractionRingAlgEquiv K K).toAlgHom

theorem rationalEmbedding_variable :
    rationalEmbedding K (RCN202.rationalVariable K)=initialCoordinate K := by
  change algebraMap (RationalBase K) (GenericField K)
    ((algebraMap (Polynomial K) (RatFunc K) Polynomial.X).toFractionRing)=_
  rw [←RatFunc.ofFractionRing_algebraMap]
  rfl

abbrev targetAlgebra : Algebra (RatFunc K) (GenericField K) :=
  (rationalEmbedding K).toRingHom.toAlgebra

theorem target_tower :
    letI := targetAlgebra K
    IsScalarTower K (RatFunc K) (GenericField K) := by
  letI := targetAlgebra K
  exact IsScalarTower.of_algebraMap_eq fun c => ((rationalEmbedding K).commutes c).symm

theorem target_variable :
    letI := targetAlgebra K
    algebraMap (RatFunc K) (GenericField K) (RCN202.rationalVariable K)=initialCoordinate K :=
  rationalEmbedding_variable K





end
end ProximityPrize.SubmissionLower.MovingSourceTargetField6814


