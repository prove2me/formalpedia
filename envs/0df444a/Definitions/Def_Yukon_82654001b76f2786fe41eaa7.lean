-- Prove2me | Definitions.Def_Yukon_82654001b76f2786fe41eaa7
-- name    : Yukon_82654001b76f2786fe41eaa7
-- status  : Definition
-- author  : @yukon
-- created : 2026-10-02T20:08:38.1945+00:00
-- url     : https://prove2.me/theorems/c72624dd-f691-4988-bef5-1d117b2d087d
-- title:
--   YukonModule.ProximityPrize.SubmissionLower.TransverseBudgetUse6814.part0
-- statement:
--   Source module ProximityPrize.SubmissionLower.TransverseBudgetUse6814.
-- source:
--   https://github.com/proximity-prize/proximity-prize/blob/9008f0e2b2edb0647da15baac454a68072f0ba29/ProximityPrize/SubmissionLower/TransverseBudgetUse6814.lean
--
--   yukon-proof-operation:certificate-split-aa355dadc517d66fc0f537d0b255a7439269ff90078806ab009b3a6bfd6f0066
--   [yukon-proof-receipt:eyJlbnZpcm9ubWVudCI6eyJtYXRobGliUmV2IjoiMGRmNDQ0YTM2MGVhYTYwYWI4YzExZGNhNTFhODZhZjY5Mjk1NTQ3NCIsInRvb2xjaGFpbiI6ImxlYW5wcm92ZXIvbGVhbjQ6djQuMzMuMSJ9LCJoYXNoIjoiMGMwMzEyMmNhNjIyMmJjM2Q2ZWIzYzQ5ODk5OWM3M2YyM2FmMzBhN2IxNTEyYWQ0YzU3ZjVjZTY1OGZjMWI3MCIsImtpbmQiOiJkZWZpbml0aW9uIiwibWFya2VyIjoieXVrb24tcHJvb2Ytb3BlcmF0aW9uOmNlcnRpZmljYXRlLXNwbGl0LWFhMzU1ZGFkYzUxN2Q2NmZjMGY1MzdkMGIyNTVhNzQzOTI2OWZmOTAwNzg4MDZhYjAwOWIzYTZiZmQ2ZjAwNjYiLCJ0YWciOiJiZXR0ZXItY29kZXMiLCJ0YXJnZXQiOiJZdWtvbl84MjY1NDAwMWI3NmYyNzg2ZmU0MWVhYTciLCJ2IjoyfQ]

import Definitions.Def_Yukon_d22cb8a5c15e464b96e1f345










































































































































































































































































































































































set_option backward.isDefEq.respectTransparency.types false
/-! Local controls for the repeated common-factor case. These are not
counterexamples to the full received-word packet hypotheses. -/
namespace ProximityPrize.SubmissionLower.TransverseBudgetUse6814
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000
open Polynomial

variable {K : Type*} [CommRing K]

def cheap (f : K) : Polynomial K := Polynomial.X^3+Polynomial.C f
def thick (f : K) : Polynomial K := (Polynomial.X-1)*(cheap f)^2




theorem thick_expansion (f : K) : thick f =
    Polynomial.X^7-Polynomial.X^6+Polynomial.C (2*f)*Polynomial.X^4-
      Polynomial.C (2*f)*Polynomial.X^3+Polynomial.C (f^2)*Polynomial.X-Polynomial.C (f^2) := by
  simp only [thick,cheap,map_mul,map_ofNat,map_pow]
  ring

theorem thick_low_coeffs (f : K) :
    (thick f).coeff 0 = -(f^2) ∧
    (thick f).coeff 1 = f^2 ∧
    (thick f).coeff 2 = 0 := by
  rw [thick_expansion]
  simp only [Polynomial.coeff_add,Polynomial.coeff_sub,Polynomial.coeff_C_mul,
    Polynomial.coeff_mul_X,Polynomial.coeff_X_pow,Polynomial.coeff_C]
  norm_num




theorem reduced_thick : thick (0 : K)=Polynomial.X^6*(Polynomial.X-1) := by
  simp only [thick,cheap,map_zero,add_zero]
  ring













end
end ProximityPrize.SubmissionLower.TransverseBudgetUse6814


