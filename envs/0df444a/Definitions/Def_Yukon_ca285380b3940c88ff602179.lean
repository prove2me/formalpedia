-- Prove2me | Definitions.Def_Yukon_ca285380b3940c88ff602179
-- name    : Yukon_ca285380b3940c88ff602179
-- status  : Definition
-- author  : @yukon
-- created : 2026-10-02T05:11:00.270987+00:00
-- url     : https://prove2.me/theorems/66755e18-bf28-48e7-8138-40ff6c7ead1a
-- title:
--   YukonModule.ProximityPrize.SubmissionLower.BoundaryTailDegrees.part0
-- statement:
--   Source module ProximityPrize.SubmissionLower.BoundaryTailDegrees.
-- source:
--   https://github.com/proximity-prize/proximity-prize/blob/9008f0e2b2edb0647da15baac454a68072f0ba29/ProximityPrize/SubmissionLower/BoundaryTailDegrees.lean
--
--   yukon-proof-operation:foundation-direct-b4ae2792da3113e116aebfca0e8aab38d1ab2f84c180442174c8cde1102e5f83
--   [yukon-proof-receipt:eyJlbnZpcm9ubWVudCI6eyJtYXRobGliUmV2IjoiMGRmNDQ0YTM2MGVhYTYwYWI4YzExZGNhNTFhODZhZjY5Mjk1NTQ3NCIsInRvb2xjaGFpbiI6ImxlYW5wcm92ZXIvbGVhbjQ6djQuMzMuMSJ9LCJoYXNoIjoiYTdlYTFjZDVlZWZmZmNiMzU1N2UzNjk4ZDdjMjFiYmRiMWVkMmM4NGY2YmM2ZWE1MzhiOGQxMDBjZmVhNDc2OSIsImtpbmQiOiJkZWZpbml0aW9uIiwibWFya2VyIjoieXVrb24tcHJvb2Ytb3BlcmF0aW9uOmZvdW5kYXRpb24tZGlyZWN0LWI0YWUyNzkyZGEzMTEzZTExNmFlYmZjYTBlOGFhYjM4ZDFhYjJmODRjMTgwNDQyMTc0YzhjZGUxMTAyZTVmODMiLCJ0YWciOiJiZXR0ZXItY29kZXMiLCJ0YXJnZXQiOiJZdWtvbl9jYTI4NTM4MGIzOTQwYzg4ZmY2MDIxNzkiLCJ2IjoyfQ]

import Definitions.Def_Yukon_dbb021723d5dd757e7cd34c2









































































































































































































































































































































































set_option backward.isDefEq.respectTransparency.types false
namespace ProximityPrize.SubmissionLower.BoundaryTailAlgebra

open RCN055 RCN056 RCN057 RCN313
open scoped BigOperators

noncomputable section
variable {K : Type*} [Field K]
local notation "Poly4" => MvPolynomial (Fin 4) K

theorem weightBound_pow {w : Fin 4 → ℕ} {P : Poly4} {a : ℤ}
    (hP : WeightBound w P a) (n : ℕ) : WeightBound w (P ^ n) ((n : ℤ) * a) := by
  induction n with
  | zero => simpa using (WeightBound.natCast (w := w) (K := K) 1)
  | succ n ih =>
    rw [pow_succ]
    convert ih.mul hP using 1 <;> push_cast <;> ring

theorem weightBound_sum {w : Fin 4 → ℕ} {ι : Type*} [DecidableEq ι] (S : Finset ι)
    (P : ι → Poly4) (a : ℤ) (hP : ∀ i ∈ S, WeightBound w (P i) a) :
    WeightBound w (∑ i ∈ S, P i) a := by
  classical
  induction S using Finset.induction_on with
  | empty => exact Or.inl (by simp)
  | @insert i S hi ih =>
    rw [Finset.sum_insert hi]
    exact (hP i (Finset.mem_insert_self i S)).add
      (ih (fun j hj => hP j (Finset.mem_insert_of_mem hj)))

def coefficientWeight (m i : ℕ) (f t : ℤ) : ℤ :=
  (i : ℤ) * (2 - t) + ((min (2 * i) m : ℕ) : ℤ) * (f - 2)

theorem coefficientWeight_alt (m i : ℕ) (f t : ℤ) :
    coefficientWeight m i f t =
      (i : ℤ) * (2 - t) + ((m : ℤ) - sExponent m i) * (f - 2) := by
  have he : ((min (2 * i) m : ℕ) : ℤ) = (m : ℤ) - sExponent m i := by
    unfold sExponent
    omega
  simp only [coefficientWeight, he]

theorem coefficientWeight_step_same (m i : ℕ) (f t : ℤ) :
    coefficientWeight (m + 1) i f t = coefficientWeight m i f t +
      ((sExponent m i + 1 - sExponent (m + 1) i : ℕ) : ℤ) * (f - 2) := by
  have h := sExponent_step_same m i
  rw [coefficientWeight_alt, coefficientWeight_alt]
  have he : ((sExponent m i + 1 - sExponent (m + 1) i : ℕ) : ℤ) =
      (sExponent m i : ℤ) + 1 - sExponent (m + 1) i := by omega
  rw [he]
  push_cast
  ring

theorem coefficientWeight_step_up (m i : ℕ) (f t : ℤ) :
    coefficientWeight (m + 1) (i + 1) f t = coefficientWeight m i f t +
      (f - t) + ((sExponent m i - sExponent (m + 1) (i + 1) : ℕ) : ℤ) * (f - 2) := by
  have h := sExponent_step_up m i
  rw [coefficientWeight_alt, coefficientWeight_alt]
  have he : ((sExponent m i - sExponent (m + 1) (i + 1) : ℕ) : ℤ) =
      (sExponent m i : ℤ) - sExponent (m + 1) (i + 1) := by omega
  rw [he]
  push_cast
  ring

theorem coefficientWeight_step_up_two (m i : ℕ) (f t : ℤ) :
    coefficientWeight (m + 1) (i + 2) f t = coefficientWeight m i f t +
      (f + 2 - 2 * t) +
      ((sExponent m i - sExponent (m + 1) (i + 2) : ℕ) : ℤ) * (f - 2) := by
  have h := sExponent_step_up_two m i
  rw [coefficientWeight_alt, coefficientWeight_alt]
  have he : ((sExponent m i - sExponent (m + 1) (i + 2) : ℕ) : ℤ) =
      (sExponent m i : ℤ) - sExponent (m + 1) (i + 2) := by omega
  rw [he]
  push_cast
  ring

theorem boundary_polynomial_bounds (w : Fin 4 → ℕ) (t : ℕ)
    (hX : w 0 = 0) (hY : w 1 = t) (hR : w 2 = 1) (ht : t ≤ 1)
    (F : Poly4) (f : ℤ) (hF : WeightBound w F f) :
    WeightBound w (polyH K F) (f - 1) ∧
    WeightBound w (polyG K F) (f + 1 - t) ∧
    WeightBound w (boundaryJ F) (f - 2) := by
  have hH : WeightBound w (polyH K F) (f - 1) := by
    simpa only [polyH, hR, Nat.cast_one] using hF.pderiv (2 : Fin 4)
  refine ⟨hH, ?_, ?_⟩
  · simpa only [polyG, horizontalDerivation, Derivation.add_apply,
      Derivation.smul_apply, smul_eq_mul] using (hF.horizontal t hX hY hR ht).neg
  · have := hH.pderiv (2 : Fin 4)
    simpa only [boundaryJ, hR, Nat.cast_one, sub_sub, Int.reduceAdd] using this

theorem refined_contribution_bounds (w : Fin 4 → ℕ) (t : ℕ)
    (hX : w 0 = 0) (hY : w 1 = t) (hR : w 2 = 1) (ht : t ≤ 1)
    (F P : Poly4) (f : ℤ) (hF : WeightBound w F f)
    (m i : ℕ) (hi : i ≤ m + 1)
    (hP : WeightBound w P (coefficientWeight m i f t)) :
    WeightBound w (contributionA F m i P) (coefficientWeight (m + 1) i f t) ∧
    WeightBound w (contributionB F m i P) (coefficientWeight (m + 1) (i + 1) f t) ∧
    WeightBound w (contributionC F m i P) (coefficientWeight (m + 1) (i + 1) f t) ∧
    WeightBound w (contributionD F m i P) (coefficientWeight (m + 1) (i + 2) f t) ∧
    WeightBound w (contributionE F m i P) (coefficientWeight (m + 1) (i + 2) f t) ∧
    (i = m + 1 → WeightBound w (contributionF F P)
      (coefficientWeight (m + 1) (i + 1) f t)) := by
  obtain ⟨hH, hG, hJ⟩ := boundary_polynomial_bounds w t hX hY hR ht F f hF
  have hDH := hH.horizontal t hX hY hR ht
  have hDG := hG.horizontal t hX hY hR ht
  have hDJ := hJ.horizontal t hX hY hR ht
  have hDP := hP.horizontal t hX hY hR ht
  have hGR := hG.pderiv (2 : Fin 4)
  have hJR := hJ.pderiv (2 : Fin 4)
  have hPR := hP.pderiv (2 : Fin 4)
  simp only [hR, Nat.cast_one] at hGR hJR hPR
  have hscalar : WeightBound w ((i : Poly4) - ((2 * m + 1 : ℕ) : Poly4)) 0 :=
    (WeightBound.natCast i).sub (WeightBound.natCast (2 * m + 1))
  have hb : WeightBound w (m + 1 - i : Poly4) 0 := by
    convert (WeightBound.natCast (w := w) (K := K) (m + 1)).sub
      (WeightBound.natCast i) using 1 <;> push_cast <;> ring
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · unfold contributionA
    rw [coefficientWeight_step_same]
    convert (hscalar.mul (weightBound_pow hJ _)).mul hP using 1 <;> ring
  · unfold contributionB
    rw [coefficientWeight_step_up]
    apply WeightBound.add
    · have hmid : WeightBound w
          (((i : Poly4) - ((2 * m + 1 : ℕ) : Poly4)) * dZero (polyH K F) +
            (m + 1 - i : Poly4) * MvPolynomial.pderiv (2 : Fin 4) (polyG K F))
          (f - t) := by
        apply WeightBound.add
        · convert hscalar.mul hDH using 1 <;> (try dsimp only [dZero]) <;> ring
        · convert hb.mul hGR using 1 <;> ring
      convert ((weightBound_pow hJ _).mul hmid).mul hP using 1 <;> ring
    · convert (hG.mul (weightBound_pow hJ _)).mul hPR using 1 <;> ring
  · unfold contributionC
    split_ifs with hs
    · have he : ((sExponent m i - 1 - sExponent (m + 1) (i + 1) : ℕ) : ℤ) + 1 =
          ((sExponent m i - sExponent (m + 1) (i + 1) : ℕ) : ℤ) := by
        have := sExponent_step_up_sub_one m i hs
        omega
      rw [coefficientWeight_step_up]
      convert ((((WeightBound.natCast (w := w) (K := K) (sExponent m i)).mul hG).mul hJR).mul
        (weightBound_pow hJ _)).mul hP using 1
      nlinarith [congrArg (fun x : ℤ => x * (f - 2)) he]
    · exact Or.inl rfl
  · unfold contributionD
    rw [coefficientWeight_step_up_two]
    apply WeightBound.add
    · convert ((weightBound_pow hJ (sExponent m i - sExponent (m + 1) (i + 2))).mul (hb.mul hDG)).mul hP using 1
        <;> (try dsimp only [dZero]) <;> ring
    · convert (hG.mul (weightBound_pow hJ (sExponent m i - sExponent (m + 1) (i + 2)))).mul hDP using 1
        <;> (try dsimp only [dZero]) <;> ring
  · unfold contributionE
    split_ifs with hs
    · have he : ((sExponent m i - 1 - sExponent (m + 1) (i + 2) : ℕ) : ℤ) + 1 =
          ((sExponent m i - sExponent (m + 1) (i + 2) : ℕ) : ℤ) := by
        have := sExponent_step_up_two_sub_one m i hs
        omega
      rw [coefficientWeight_step_up_two]
      convert ((((WeightBound.natCast (w := w) (K := K) (sExponent m i)).mul hG).mul hDJ).mul
        (weightBound_pow hJ _)).mul hP using 1
      · rfl
      · nlinarith [congrArg (fun x : ℤ => x * (f - 2)) he]
    · exact Or.inl rfl
  · intro htop
    have he : sExponent m i - sExponent (m + 1) (i + 1) = 0 := by
      unfold sExponent
      omega
    rw [coefficientWeight_step_up, he]
    unfold contributionF
    convert hH.mul hDP using 1 <;> (try dsimp only [dZero]) <;> push_cast <;> ring

theorem refinedCoefficients_weightBound (w : Fin 4 → ℕ) (t : ℕ)
    (hX : w 0 = 0) (hY : w 1 = t) (hR : w 2 = 1) (ht : t ≤ 1)
    (F : Poly4) (f : ℤ) (hF : WeightBound w F f) (m i : ℕ) :
    WeightBound w (refinedCoefficients F m i) (coefficientWeight m i f t) := by
  induction m generalizing i with
  | zero =>
    by_cases hi : i = 0
    · subst i
      simpa only [refinedCoefficients, ↓reduceIte, coefficientWeight,
        Nat.mul_zero, min_self, Nat.cast_zero, Nat.cast_one, zero_mul, zero_add] using
        (WeightBound.natCast (w := w) (K := K) 1)
    · exact Or.inl (by simp only [refinedCoefficients, if_neg hi])
  | succ m ih =>
    simp only [refinedCoefficients, refinedCoefficientStep]
    apply weightBound_sum
    intro j hj
    have hjm : j ≤ m + 1 := by have := Finset.mem_range.mp hj; omega
    obtain ⟨hA, hB, hC, hD, hE, htop⟩ := refined_contribution_bounds
      w t hX hY hR ht F (refinedCoefficients F m j) f hF m j hjm (ih j)
    by_cases hi0 : i = j
    · simp only [if_pos hi0]
      simpa only [hi0] using hA
    · rw [if_neg hi0]
      by_cases hi1 : i = j + 1
      · rw [if_pos hi1, hi1]
        apply (hB.add hC).add
        split_ifs with he
        · exact htop he
        · exact Or.inl rfl
      · rw [if_neg hi1]
        split_ifs with he
        · rw [he.1]
          exact hD.add hE
        · exact Or.inl rfl

end
end ProximityPrize.SubmissionLower.BoundaryTailAlgebra


