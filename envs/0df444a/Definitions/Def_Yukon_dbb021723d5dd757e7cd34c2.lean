-- Prove2me | Definitions.Def_Yukon_dbb021723d5dd757e7cd34c2
-- name    : Yukon_dbb021723d5dd757e7cd34c2
-- status  : Definition
-- author  : @yukon
-- created : 2026-10-02T04:39:28.868992+00:00
-- url     : https://prove2.me/theorems/10914fbf-c5c1-46d5-9dc6-86cfcb25063a
-- title:
--   YukonModule.ProximityPrize.SubmissionLower.BoundaryTailAlgebra.part0
-- statement:
--   Source module ProximityPrize.SubmissionLower.BoundaryTailAlgebra.
-- source:
--   https://github.com/proximity-prize/proximity-prize/blob/9008f0e2b2edb0647da15baac454a68072f0ba29/ProximityPrize/SubmissionLower/BoundaryTailAlgebra.lean
--
--   yukon-proof-operation:foundation-direct-cf267d3a84d61a30afba459501d2dc6d29b5dd28ecba1e791d5bfa9c0493cecb
--   [yukon-proof-receipt:eyJlbnZpcm9ubWVudCI6eyJtYXRobGliUmV2IjoiMGRmNDQ0YTM2MGVhYTYwYWI4YzExZGNhNTFhODZhZjY5Mjk1NTQ3NCIsInRvb2xjaGFpbiI6ImxlYW5wcm92ZXIvbGVhbjQ6djQuMzMuMSJ9LCJoYXNoIjoiODg1ZjJmOWU3YWM1ZTdjMDA2NWNiNDUyYzY1ODdlNjg5YTVhNTYwOWRmOTNkYmVmYWFjNzIyNjQ4ZjY1MmU0MSIsImtpbmQiOiJkZWZpbml0aW9uIiwibWFya2VyIjoieXVrb24tcHJvb2Ytb3BlcmF0aW9uOmZvdW5kYXRpb24tZGlyZWN0LWNmMjY3ZDNhODRkNjFhMzBhZmJhNDU5NTAxZDJkYzZkMjliNWRkMjhlY2JhMWU3OTFkNWJmYTljMDQ5M2NlY2IiLCJ0YWciOiJiZXR0ZXItY29kZXMiLCJ0YXJnZXQiOiJZdWtvbl9kYmIwMjE3MjNkNWRkNzU3ZTdjZDM0YzIiLCJ2IjoyfQ]

import Definitions.Def_Yukon_196ff1de7425c8d8df8d3a11
import Definitions.Def_Yukon_07bb1fdf83fc478e7c5449e7
import Definitions.Def_Yukon_755f5ab5e1dfa660f8e11f09







































































































































































































































































































































































set_option backward.isDefEq.respectTransparency.types false
/-! Refined coefficient data for the correlated differential-tail recurrence.
Only definitions and elementary exponent side conditions live here. -/

namespace ProximityPrize.SubmissionLower.BoundaryTailAlgebra

open RCN055 RCN056 RCN313
variable {K : Type*} [CommRing K]
noncomputable section
local notation "Poly4" => MvPolynomial (Fin 4) K

def sExponent (m i : ℕ) : ℕ := max (m - 2 * i) 0
def boundaryJ (F : Poly4) : Poly4 := MvPolynomial.pderiv (2 : Fin 4) (polyH K F)

def refinedMonomial (F : Poly4) (m i : ℕ) (C : Poly4) : Poly4 :=
  polyH K F ^ i * polyG K F ^ (m + 1 - i) * boundaryJ F ^ sExponent m i * C

def dZero (P : Poly4) : Poly4 :=
  horizontalDerivation P

def contributionA (F : Poly4) (m i : ℕ) (C : Poly4) : Poly4 :=
  ((i : Poly4) - (2 * m + 1 : ℕ)) *
    boundaryJ F ^ (sExponent m i + 1 - sExponent (m + 1) i) * C

def contributionB (F : Poly4) (m i : ℕ) (C : Poly4) : Poly4 :=
  boundaryJ F ^ (sExponent m i - sExponent (m + 1) (i + 1)) *
    (((i : Poly4) - (2 * m + 1 : ℕ)) * dZero (polyH K F) +
      (m + 1 - i : Poly4) * MvPolynomial.pderiv (2 : Fin 4) (polyG K F)) * C
      + polyG K F * boundaryJ F ^ (sExponent m i - sExponent (m + 1) (i + 1)) *
        MvPolynomial.pderiv (2 : Fin 4) C

def contributionC (F : Poly4) (m i : ℕ) (C : Poly4) : Poly4 :=
  if 0 < sExponent m i then
    (sExponent m i : Poly4) * polyG K F *
      MvPolynomial.pderiv (2 : Fin 4) (boundaryJ F) *
      boundaryJ F ^ (sExponent m i - 1 - sExponent (m + 1) (i + 1)) * C
  else 0

def contributionD (F : Poly4) (m i : ℕ) (C : Poly4) : Poly4 :=
    boundaryJ F ^ (sExponent m i - sExponent (m + 1) (i + 2)) *
    ((m + 1 - i : Poly4) * dZero (polyG K F)) * C +
      polyG K F * boundaryJ F ^ (sExponent m i - sExponent (m + 1) (i + 2)) *
        dZero C

def contributionE (F : Poly4) (m i : ℕ) (C : Poly4) : Poly4 :=
  if 0 < sExponent m i then
    (sExponent m i : Poly4) * polyG K F * dZero (boundaryJ F) *
      boundaryJ F ^ (sExponent m i - 1 - sExponent (m + 1) (i + 2)) * C
  else 0

def contributionF (F : Poly4) (C : Poly4) : Poly4 := polyH K F * dZero C

def refinedCoefficientStep (F : Poly4) (m : ℕ) (C : ℕ → Poly4) (q : ℕ) : Poly4 :=
  ∑ i ∈ Finset.range (m + 2),
    (if q = i then contributionA F m i (C i)
     else if q = i + 1 then
       contributionB F m i (C i) + contributionC F m i (C i) +
         if i = m + 1 then contributionF F (C i) else 0
     else if q = i + 2 ∧ i ≤ m then
       contributionD F m i (C i) + contributionE F m i (C i)
     else 0)

def refinedCoefficients (F : Poly4) : ℕ → ℕ → Poly4
  | 0, i => if i = 0 then 1 else 0
  | m + 1, i => refinedCoefficientStep F m (refinedCoefficients F m) i

theorem expanded_monomial_step (F C : Poly4) (i b s lambda : ℕ) :
    polyH K F * baseDerivation F
        (polyH K F ^ i * polyG K F ^ b * boundaryJ F ^ s * C) -
      (lambda : Poly4) * (polyH K F ^ i * polyG K F ^ b * boundaryJ F ^ s * C) *
        baseDerivation F (polyH K F) =
      ((i : Poly4) - (lambda : ℕ)) * polyH K F ^ i * polyG K F ^ (b + 1) *
          boundaryJ F ^ (s + 1) * C +
      polyH K F ^ (i + 1) * polyG K F ^ b * boundaryJ F ^ s *
        (((i : Poly4) - (lambda : ℕ)) * dZero (polyH K F) +
          (b : Poly4) * MvPolynomial.pderiv (2 : Fin 4) (polyG K F)) * C +
      polyH K F ^ (i + 1) * polyG K F ^ (b + 1) * boundaryJ F ^ s *
        MvPolynomial.pderiv (2 : Fin 4) C +
      (s : Poly4) * polyH K F ^ (i + 1) * polyG K F ^ (b + 1) *
        boundaryJ F ^ (s - 1) * MvPolynomial.pderiv (2 : Fin 4) (boundaryJ F) * C +
      (b : Poly4) * polyH K F ^ (i + 2) * polyG K F ^ (b - 1) *
        boundaryJ F ^ s * dZero (polyG K F) * C +
      polyH K F ^ (i + 2) * polyG K F ^ b * boundaryJ F ^ s * dZero C +
      (s : Poly4) * polyH K F ^ (i + 2) * polyG K F ^ b *
        boundaryJ F ^ (s - 1) * dZero (boundaryJ F) * C := by
  simp only [baseDerivation_apply, dZero, horizontalDerivation,
    Derivation.add_apply, Derivation.smul_apply, smul_eq_mul,
    MvPolynomial.pderiv_mul, Derivation.leibniz_pow, nsmul_eq_mul]
  cases i <;> cases b <;> cases s <;>
    simp only [Nat.cast_succ, Nat.cast_zero, Nat.cast_add, Nat.cast_one,
    Nat.add_sub_cancel, Nat.succ_sub_one, pow_succ, pow_zero,
      zero_mul, mul_zero, one_mul, mul_one, boundaryJ] <;> ring

theorem sExponent_step_same (m i : ℕ) :
    sExponent m i + 1 ≥ sExponent (m + 1) i := by
  unfold sExponent
  omega

theorem sExponent_step_up (m i : ℕ) :
    sExponent m i ≥ sExponent (m + 1) (i + 1) := by
  unfold sExponent
  omega

theorem sExponent_step_up_two (m i : ℕ) :
    sExponent m i ≥ sExponent (m + 1) (i + 2) := by
  unfold sExponent
  omega

theorem sExponent_step_up_sub_one (m i : ℕ) (hs : 0 < sExponent m i) :
    sExponent m i - 1 ≥ sExponent (m + 1) (i + 1) := by
  unfold sExponent at *
  omega

theorem sExponent_step_up_two_sub_one (m i : ℕ) (hs : 0 < sExponent m i) :
    sExponent m i - 1 ≥ sExponent (m + 1) (i + 2) := by
  unfold sExponent at *
  omega

end
end ProximityPrize.SubmissionLower.BoundaryTailAlgebra


