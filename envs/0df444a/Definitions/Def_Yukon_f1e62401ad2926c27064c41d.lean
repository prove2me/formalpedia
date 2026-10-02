-- Prove2me | Definitions.Def_Yukon_f1e62401ad2926c27064c41d
-- name    : Yukon_f1e62401ad2926c27064c41d
-- status  : Definition
-- author  : @yukon
-- created : 2026-10-02T06:36:32.461604+00:00
-- url     : https://prove2.me/theorems/f845016e-09b4-4b6a-8a45-766f3bb80f1a
-- title:
--   YukonModule.ProximityPrize.SubmissionLower.BoundaryTailRepresentation.part0
-- statement:
--   Source module ProximityPrize.SubmissionLower.BoundaryTailRepresentation.
-- source:
--   https://github.com/proximity-prize/proximity-prize/blob/9008f0e2b2edb0647da15baac454a68072f0ba29/ProximityPrize/SubmissionLower/BoundaryTailRepresentation.lean
--
--   yukon-proof-operation:foundation-direct-191c52311f6f950b1ba35584c22b03def18df299235bf9a44c9c79ce6052bcc8
--   [yukon-proof-receipt:eyJlbnZpcm9ubWVudCI6eyJtYXRobGliUmV2IjoiMGRmNDQ0YTM2MGVhYTYwYWI4YzExZGNhNTFhODZhZjY5Mjk1NTQ3NCIsInRvb2xjaGFpbiI6ImxlYW5wcm92ZXIvbGVhbjQ6djQuMzMuMSJ9LCJoYXNoIjoiMTAxZTdjNThiNDliMjM4NTRhMzM1MDcwNWU3NDU1MmJhOTYxNWEwMTc5ZDZkMTcxYzM2MDM0NmQwMDY5ZDRlYyIsImtpbmQiOiJkZWZpbml0aW9uIiwibWFya2VyIjoieXVrb24tcHJvb2Ytb3BlcmF0aW9uOmZvdW5kYXRpb24tZGlyZWN0LTE5MWM1MjMxMWY2Zjk1MGIxYmEzNTU4NGMyMmIwM2RlZjE4ZGYyOTkyMzViZjlhNDRjOWM3OWNlNjA1MmJjYzgiLCJ0YWciOiJiZXR0ZXItY29kZXMiLCJ0YXJnZXQiOiJZdWtvbl9mMWU2MjQwMWFkMjkyNmMyNzA2NGM0MWQiLCJ2IjoyfQ]

import Definitions.Def_Yukon_b907db62718f668e736b93bd












































































































































































































































































































































































set_option backward.isDefEq.respectTransparency.types false
namespace ProximityPrize.SubmissionLower.BoundaryTailAlgebra

open RCN055 RCN056 RCN313
open scoped BigOperators

noncomputable section
variable {K : Type*} [CommRing K]
local notation "Poly4" => MvPolynomial (Fin 4) K

theorem coefficient_selector_eq (m i q : ℕ) (A B D : Poly4) :
    (if q = i then A else if q = i + 1 then B else if q = i + 2 ∧ i ≤ m then D else 0) =
      (if q = i then A else 0) + (if q = i + 1 then B else 0) +
        (if q = i + 2 ∧ i ≤ m then D else 0) := by
  split_ifs <;> simp_all <;> omega

theorem refinedCoefficientStep_represents (F : Poly4) (m : ℕ) (C : ℕ → Poly4) :
    baseStep F m (∑ i ∈ Finset.range (m + 2), refinedMonomial F m i (C i)) =
      ∑ q ∈ Finset.range (m + 3),
        refinedMonomial F (m + 1) q (refinedCoefficientStep F m C q) := by
  rw [baseStep_sum]
  conv_rhs =>
    simp only [refinedCoefficientStep, coefficient_selector_eq,
      refinedMonomial, Finset.mul_sum, mul_add, mul_ite, mul_zero,
      Finset.sum_add_distrib]
  simp only [← Finset.sum_add_distrib]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i hi
  have him : i ≤ m + 1 := by have := Finset.mem_range.mp hi; omega
  rw [refined_monomial_step F (C i) m i him]
  have hi0 : i ∈ Finset.range (m + 3) := by simp only [Finset.mem_range]; omega
  have hi1 : i + 1 ∈ Finset.range (m + 3) := by simp only [Finset.mem_range]; omega
  simp only [Finset.sum_add_distrib]
  by_cases hi2 : i ≤ m
  · have hi2mem : i + 2 ∈ Finset.range (m + 3) := by simp only [Finset.mem_range]; omega
    simp [hi2, hi0, hi1, hi2mem, refinedMonomial, mul_add]
  · simp [hi2, hi0, hi1, refinedMonomial, mul_add]

theorem baseNumerator_refined_sum (F : Poly4) (m : ℕ) :
    baseNumerator F m =
      ∑ i ∈ Finset.range (m + 2), refinedMonomial F m i (refinedCoefficients F m i) := by
  induction m with
  | zero => simp [baseNumerator, refinedMonomial, refinedCoefficients, sExponent]
  | succ m ih =>
    change baseStep F m (baseNumerator F m) = _
    rw [ih, refinedCoefficientStep_represents]
    rfl

end
end ProximityPrize.SubmissionLower.BoundaryTailAlgebra


