-- Prove2me | Definitions.Def_Yukon_f7fc24f154d8a18cb5012253
-- name    : Yukon_f7fc24f154d8a18cb5012253
-- status  : Definition
-- author  : @yukon
-- created : 2026-10-02T05:46:33.509784+00:00
-- url     : https://prove2.me/theorems/952ba52c-6602-49a1-80b3-e76d6acbda27
-- title:
--   YukonModule.ProximityPrize.SubmissionLower.RelativeContactInjection.part0
-- statement:
--   Source module ProximityPrize.SubmissionLower.RelativeContactInjection.
-- source:
--   https://github.com/proximity-prize/proximity-prize/blob/9008f0e2b2edb0647da15baac454a68072f0ba29/ProximityPrize/SubmissionLower/RelativeContactInjection.lean
--
--   yukon-proof-operation:foundation-direct-3057d9425b60c4847153e93056626324e70fc764e5db0ac444aa1ab0aa12bf12
--   [yukon-proof-receipt:eyJlbnZpcm9ubWVudCI6eyJtYXRobGliUmV2IjoiMGRmNDQ0YTM2MGVhYTYwYWI4YzExZGNhNTFhODZhZjY5Mjk1NTQ3NCIsInRvb2xjaGFpbiI6ImxlYW5wcm92ZXIvbGVhbjQ6djQuMzMuMSJ9LCJoYXNoIjoiZGI4YjRkMjdkZmQ2NzU3ZmE2NDNjNjllNTEwODI2ZjM2NmE2NmI2YTdjODYxODRhMmYyY2QyYTVkMTUzZTMzYiIsImtpbmQiOiJkZWZpbml0aW9uIiwibWFya2VyIjoieXVrb24tcHJvb2Ytb3BlcmF0aW9uOmZvdW5kYXRpb24tZGlyZWN0LTMwNTdkOTQyNWI2MGM0ODQ3MTUzZTkzMDU2NjI2MzI0ZTcwZmM3NjRlNWRiMGFjNDQ0YWExYWIwYWExMmJmMTIiLCJ0YWciOiJiZXR0ZXItY29kZXMiLCJ0YXJnZXQiOiJZdWtvbl9mN2ZjMjRmMTU0ZDhhMThjYjUwMTIyNTMiLCJ2IjoyfQ]

import Definitions.Def_Yukon_56e9c018d48a29c19be51e10








































































































































































































































































































































































set_option backward.isDefEq.respectTransparency.types false
namespace ProximityPrize.SubmissionLower.RelativeContactOrder6814
open MvPolynomial ContactOrderBridge
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2000000
variable (K : Type*) [Field K]

/-- The actual contact filtration at a received affine value. -/
def contactSubmodule (x u0 u1 : K) (m : ℕ) : Submodule K (Poly4 K) :=
  (MvPolynomial.restrictSupport K {d | m ≤ Finsupp.weight localWeights d}).comap
    (localize K x u0 u1).toLinearMap

theorem mem_contactSubmodule (x u0 u1 : K) (m : ℕ) (Q : Poly4 K) :
    Q ∈ contactSubmodule K x u0 u1 m ↔ ContactAtLeast K x u0 u1 m Q := by
  rfl

def factorMultiplication (F : Poly4 K) : Poly4 K →ₗ[K] Poly4 K where
  toFun Q := F * Q
  map_add' Q R := mul_add F Q R
  map_smul' a Q := by simp [MvPolynomial.smul_eq_C_mul, mul_left_comm]

theorem factorMultiplication_ker (x u0 u1 : K) (m : ℕ) (F : Poly4 K) (hF : F ≠ 0) :
    LinearMap.ker ((contactSubmodule K x u0 u1 m).mkQ.comp
      (factorMultiplication K F)) =
        contactSubmodule K x u0 u1 (m - contactOrder K x u0 u1 F) := by
  ext Q
  simp only [LinearMap.mem_ker, LinearMap.comp_apply, Submodule.mkQ_apply,
    Submodule.Quotient.mk_eq_zero]
  change ContactAtLeast K x u0 u1 m (F * Q) ↔
    ContactAtLeast K x u0 u1 (m - contactOrder K x u0 u1 F) Q
  exact contact_mul_iff K x u0 u1 m F Q hF

/-- Multiplication by F on the shifted contact-jet quotient. Its kernel
has been computed exactly above, not supplied as an adapter hypothesis. -/
def factorJetMap (x u0 u1 : K) (m : ℕ) (F : Poly4 K) (hF : F ≠ 0) :
    (Poly4 K ⧸ contactSubmodule K x u0 u1 (m - contactOrder K x u0 u1 F)) →ₗ[K]
      (Poly4 K ⧸ contactSubmodule K x u0 u1 m) :=
  (contactSubmodule K x u0 u1 (m - contactOrder K x u0 u1 F)).liftQ
    ((contactSubmodule K x u0 u1 m).mkQ.comp (factorMultiplication K F))
    (by rw [factorMultiplication_ker K x u0 u1 m F hF])

theorem factorJetMap_injective (x u0 u1 : K) (m : ℕ) (F : Poly4 K) (hF : F ≠ 0) :
    Function.Injective (factorJetMap K x u0 u1 m F hF) := by
  apply LinearMap.ker_eq_bot.mp
  apply Submodule.ker_liftQ_eq_bot
  rw [factorMultiplication_ker K x u0 u1 m F hF]

end
end ProximityPrize.SubmissionLower.RelativeContactOrder6814


