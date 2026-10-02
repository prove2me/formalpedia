-- Prove2me | Definitions.Def_Yukon_b907db62718f668e736b93bd
-- name    : Yukon_b907db62718f668e736b93bd
-- status  : Definition
-- author  : @yukon
-- created : 2026-10-02T06:19:53.929063+00:00
-- url     : https://prove2.me/theorems/f7e3a530-6903-4652-bb5c-9add8fe6f0dd
-- title:
--   YukonModule.ProximityPrize.SubmissionLower.BoundaryTailRecurrence.part0
-- statement:
--   Source module ProximityPrize.SubmissionLower.BoundaryTailRecurrence.
-- source:
--   https://github.com/proximity-prize/proximity-prize/blob/9008f0e2b2edb0647da15baac454a68072f0ba29/ProximityPrize/SubmissionLower/BoundaryTailRecurrence.lean
--
--   yukon-proof-operation:foundation-direct-37770d878f40836a64a73edbc8456b331664f7f881e109cc551f550cb98ed819
--   [yukon-proof-receipt:eyJlbnZpcm9ubWVudCI6eyJtYXRobGliUmV2IjoiMGRmNDQ0YTM2MGVhYTYwYWI4YzExZGNhNTFhODZhZjY5Mjk1NTQ3NCIsInRvb2xjaGFpbiI6ImxlYW5wcm92ZXIvbGVhbjQ6djQuMzMuMSJ9LCJoYXNoIjoiZjlhY2FjZmM2ZGRkZTg4MGVmMGFlNWIzMTcyNGJkZGMxMjNjNGI2ZTM4NTFiN2VlY2M5NTkzNjMyYzcwNjU5NSIsImtpbmQiOiJkZWZpbml0aW9uIiwibWFya2VyIjoieXVrb24tcHJvb2Ytb3BlcmF0aW9uOmZvdW5kYXRpb24tZGlyZWN0LTM3NzcwZDg3OGY0MDgzNmE2NGE3M2VkYmM4NDU2YjMzMTY2NGY3Zjg4MWUxMDljYzU1MWY1NTBjYjk4ZWQ4MTkiLCJ0YWciOiJiZXR0ZXItY29kZXMiLCJ0YXJnZXQiOiJZdWtvbl9iOTA3ZGI2MjcxOGY2NjhlNzM2YjkzYmQiLCJ2IjoyfQ]

import Definitions.Def_Yukon_aa49d06014b5907015f56d9e













































































































































































































































































































































































set_option backward.isDefEq.respectTransparency.types false
namespace ProximityPrize.SubmissionLower.BoundaryTailAlgebra

open RCN055 RCN056 RCN313
open scoped BigOperators

noncomputable section
variable {K : Type*} [CommRing K]
local notation "Poly4" => MvPolynomial (Fin 4) K

theorem refined_monomial_step (F P : Poly4) (m i : ℕ) (hi : i ≤ m + 1) :
    baseStep F m (refinedMonomial F m i P) =
      refinedMonomial F (m + 1) i (contributionA F m i P) +
      refinedMonomial F (m + 1) (i + 1)
        (contributionB F m i P + contributionC F m i P +
          if i = m + 1 then contributionF F P else 0) +
      if i ≤ m then refinedMonomial F (m + 1) (i + 2)
        (contributionD F m i P + contributionE F m i P) else 0 := by
  simp only [baseStep, refinedMonomial]
  rw [expanded_monomial_step]
  by_cases htop : i = m + 1
  · subst i
    have hs0 : sExponent m (m + 1) = 0 := by unfold sExponent; omega
    have hs1 : sExponent (m + 1) (m + 1) = 0 := by unfold sExponent; omega
    have hs2 : sExponent (m + 1) (m + 1 + 1) = 0 := by unfold sExponent; omega
    have hGexp : m + 1 + 1 - (m + 1) = 1 := by omega
    simp only [contributionA, contributionB, contributionC, contributionF,
      hs0, hs1, hs2, hGexp, Nat.lt_irrefl, if_false, Nat.le_add_left, if_true,
      show ¬ m + 1 ≤ m by omega, ↓reduceIte]
    simp only [Nat.add_sub_cancel, Nat.sub_self, Nat.zero_sub, Nat.zero_add,
      Nat.sub_zero, Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat, Nat.cast_one,
      Nat.cast_zero, pow_zero, pow_succ, zero_mul, mul_zero, one_mul, mul_one,
      dZero]
    ring
  · have him : i ≤ m := by omega
    have hb0 : m + 1 + 1 - i = (m + 1 - i) + 1 := by omega
    have hb1 : m + 1 + 1 - (i + 1) = m + 1 - i := by omega
    have hb2 : m + 1 + 1 - (i + 2) = m - i := by omega
    have hb3 : m + 1 - i = (m - i) + 1 := by omega
    have hcast : (m + 1 - i : Poly4) = ((m + 1 - i : ℕ) : Poly4) := by
      rw [Nat.cast_sub hi, Nat.cast_add, Nat.cast_one]
    simp only [if_neg htop, if_pos him, contributionA, contributionB,
      contributionC, contributionD, contributionE, hb0, hb1, hb2, hb3, hcast]
    by_cases hs : 2 * i ≤ m
    · obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hs
      have he0 : sExponent (2 * i + d) i = d := by unfold sExponent; omega
      have he1 : sExponent (2 * i + d + 1) i = d + 1 := by unfold sExponent; omega
      have he2 : sExponent (2 * i + d + 1) (i + 1) = d - 1 := by unfold sExponent; omega
      have he3 : sExponent (2 * i + d + 1) (i + 2) = d - 3 := by unfold sExponent; omega
      have he4 : 2 * i + d - i = i + d := by omega
      simp only [he0, he1, he2, he3, he4]
      by_cases hd : d < 3
      · interval_cases d <;>
          norm_num [pow_add, pow_succ, dZero] <;> ring
      · obtain ⟨s, rfl⟩ := Nat.exists_eq_add_of_le (show 3 ≤ d by omega)
        have h1 : 3 + s - 1 = s + 2 := by omega
        have h3 : 3 + s - 3 = s := by omega
        have h4 : 3 + s - (s + 2) = 1 := by omega
        have h5 : 3 + s - 1 - (s + 2) = 0 := by omega
        have h6 : 3 + s - 1 - s = 2 := by omega
        simp only [h1, h3, h4, h5, h6, show 0 < 3 + s by omega, if_true]
        norm_num [pow_add, pow_succ, dZero] <;> ring
    · have he0 : sExponent m i = 0 := by unfold sExponent; omega
      have he1 : sExponent (m + 1) i = 0 := by unfold sExponent; omega
      have he2 : sExponent (m + 1) (i + 1) = 0 := by unfold sExponent; omega
      have he3 : sExponent (m + 1) (i + 2) = 0 := by unfold sExponent; omega
      simp only [he0, he1, he2, he3]
      norm_num [pow_add, pow_succ, dZero] <;> ring

end
end ProximityPrize.SubmissionLower.BoundaryTailAlgebra


