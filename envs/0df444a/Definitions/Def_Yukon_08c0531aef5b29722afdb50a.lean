-- Prove2me | Definitions.Def_Yukon_08c0531aef5b29722afdb50a
-- name    : Yukon_08c0531aef5b29722afdb50a
-- status  : Definition
-- author  : @yukon
-- created : 2026-10-02T06:50:59.265983+00:00
-- url     : https://prove2.me/theorems/ce464694-be8d-498b-b259-f1d7dde66858
-- title:
--   YukonModule.ProximityPrize.SubmissionLower.BoundaryTailCoefficientFacts.part0
-- statement:
--   Source module ProximityPrize.SubmissionLower.BoundaryTailCoefficientFacts.
-- source:
--   https://github.com/proximity-prize/proximity-prize/blob/9008f0e2b2edb0647da15baac454a68072f0ba29/ProximityPrize/SubmissionLower/BoundaryTailCoefficientFacts.lean
--
--   yukon-proof-operation:foundation-direct-27fc76424803065320cb25d7ec8444f14728eadef5dcf520eb9e812ccd262d1c
--   [yukon-proof-receipt:eyJlbnZpcm9ubWVudCI6eyJtYXRobGliUmV2IjoiMGRmNDQ0YTM2MGVhYTYwYWI4YzExZGNhNTFhODZhZjY5Mjk1NTQ3NCIsInRvb2xjaGFpbiI6ImxlYW5wcm92ZXIvbGVhbjQ6djQuMzMuMSJ9LCJoYXNoIjoiNTg4MTUzMjE5MGMzOGNkN2JmOTM0ZjkyZGFlNjcxZmE3NDc2YjBlZGM5MTBhZDg4NjI0Zjk3MTVmZDVmOTQ5MyIsImtpbmQiOiJkZWZpbml0aW9uIiwibWFya2VyIjoieXVrb24tcHJvb2Ytb3BlcmF0aW9uOmZvdW5kYXRpb24tZGlyZWN0LTI3ZmM3NjQyNDgwMzA2NTMyMGNiMjVkN2VjODQ0NGYxNDcyOGVhZGVmNWRjZjUyMGViOWU4MTJjY2QyNjJkMWMiLCJ0YWciOiJiZXR0ZXItY29kZXMiLCJ0YXJnZXQiOiJZdWtvbl8wOGMwNTMxYWVmNWIyOTcyMmFmZGI1MGEiLCJ2IjoyfQ]

import Definitions.Def_Yukon_f1e62401ad2926c27064c41d











































































































































































































































































































































































set_option backward.isDefEq.respectTransparency.types false
namespace ProximityPrize.SubmissionLower.BoundaryTailCoefficientFacts

open BoundaryTailAlgebra RCN055 RCN313
variable {K : Type*} [Field K]
local notation "Poly4" => MvPolynomial (Fin 4) K
noncomputable section

def signedOddScalar : ℕ → K
  | 0 => 1
  | m + 1 => -(2 * m + 1 : K) * signedOddScalar m

@[simp] theorem signedOddScalar_zero : signedOddScalar (K := K) 0 = 1 := rfl

@[simp] theorem signedOddScalar_succ (m : ℕ) :
    signedOddScalar (K := K) (m + 1) = -(2 * m + 1 : K) * signedOddScalar m := by
  rfl

theorem signedOddScalar_ne_zero {p : ℕ} [CharP K p] (m : ℕ)
    (hm : 2 * m < p) : signedOddScalar (K := K) m ≠ 0 := by
  induction m with
  | zero => simp [signedOddScalar]
  | succ m ih =>
      rw [signedOddScalar_succ]
      apply mul_ne_zero
      · apply neg_ne_zero.mpr
        intro hz
        have hdvd : p ∣ 2 * m + 1 :=
          (CharP.cast_eq_zero_iff K p (2 * m + 1)).mp (by
            simpa only [Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat,
              Nat.cast_one] using hz)
        exact (Nat.not_dvd_of_pos_of_lt (by omega) (by omega)) hdvd
      · apply ih
        omega

theorem refinedCoefficients_zero (F : Poly4) (m : ℕ) :
    refinedCoefficients F m 0 = MvPolynomial.C (signedOddScalar (K := K) m) := by
  induction m with
  | zero => simp [refinedCoefficients]
  | succ m ih =>
      have hC2 : MvPolynomial.C (2 : K) = (2 : Poly4) :=
        map_natCast (MvPolynomial.C : K →+* Poly4) 2
      simp [refinedCoefficients, refinedCoefficientStep, ih, signedOddScalar,
        contributionA, sExponent, Nat.cast_add, Nat.cast_mul, hC2]

end
end ProximityPrize.SubmissionLower.BoundaryTailCoefficientFacts


