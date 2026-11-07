-- Prove2me | solution 1 for AaronsonAmbainis.Level.thirdMoment_core
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T22:45:35.533959+00:00
-- url     : https://prove2.me/submissions/f461ad9e-aa0e-49bb-9592-43629fdea3a8

import Definitions.Def_AaronsonAmbainis_Level_Basic
import Definitions.Def_AaronsonAmbainis_Level_AllPairs
import Definitions.Def_AaronsonAmbainis_TwoSided_CauchySchwarz
import Definitions.Def_AaronsonAmbainis_Level_ThirdMoment
import Theorems.Thm_AaronsonAmbainis_Level_four_mul_integrated
import Theorems.Thm_AaronsonAmbainis_Level_pairSum_pos
import Theorems.Thm_AaronsonAmbainis_Level_rowSum_pos
import Theorems.Thm_AaronsonAmbainis_abstract_cs


set_option autoImplicit true
open AaronsonAmbainis
open Finset
open AaronsonAmbainis.Level
variable {ι : Type} [Fintype ι] [DecidableEq ι]
namespace AaronsonAmbainis.Level
theorem _root_.solution (hInt : IntegratedAllPairsInequality) (f : Cube ι → ℝ)
    (a : Cube ι → ι → ℝ) (ha : ∀ x j, 0 ≤ a x j) {K : ℝ} (hsum : ∀ x, ∑ j, a x j ≤ K)
    (hrow : ∀ x y, |f x - f y| ≤ ∑ j ∈ diffSet x y, a x j)
    {M : ℝ} (hM0 : 0 ≤ M) (hM : ∀ j, meanAbsIncr f j ≤ M) (s : ℝ) :
    (∑ x, max (f x - s) 0 ^ 3) * ((univ.filter (fun y : Cube ι => f y ≤ s)).card : ℝ)
      ≤ 3 / 2 * 4 ^ Fintype.card ι * M * K ^ 2 := by
  have hC : 0 ≤ 3 / 2 * (4 : ℝ) ^ Fintype.card ι * M := by positivity
  have hRHS : 0 ≤ 3 / 2 * (4 : ℝ) ^ Fintype.card ι * M * K ^ 2 := by positivity
  -- the two sets
  obtain ⟨A, hA⟩ : ∃ A : Finset (Cube ι), A = univ.filter (fun x : Cube ι => s < f x) := ⟨_, rfl⟩
  obtain ⟨B, hB⟩ : ∃ B : Finset (Cube ι), B = univ.filter (fun y : Cube ι => f y ≤ s) := ⟨_, rfl⟩
  have hmemA : ∀ x, x ∈ A ↔ s < f x := by
    intro x
    rw [hA]
    simp
  have hmemB : ∀ y, y ∈ B ↔ f y ≤ s := by
    intro y
    rw [hB]
    simp
  -- the third moment as a sum over `A`
  have hsumA : ∑ x, max (f x - s) 0 ^ 3 = ∑ x ∈ A, (f x - s) ^ 3 := by
    rw [hA, Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro x _
    by_cases hx : s < f x
    · rw [if_pos hx, max_eq_left (by linarith : 0 ≤ f x - s)]
    · rw [if_neg hx, max_eq_right (by linarith [not_lt.mp hx] : f x - s ≤ 0)]
      norm_num
  rw [← hB, hsumA]
  -- the trivial cases
  rcases A.eq_empty_or_nonempty with hAe | ⟨x0, hx0⟩
  · rw [hAe, Finset.sum_empty, zero_mul]
    exact hRHS
  rcases B.eq_empty_or_nonempty with hBe | ⟨y0, hy0⟩
  · rw [hBe, Finset.card_empty, Nat.cast_zero, mul_zero]
    exact hRHS
  have hx0' := (hmemA x0).mp hx0
  have hy0' := (hmemB y0).mp hy0
  -- positivity of the costs
  have hposA : ∀ x ∈ A, 0 < ∑ j, a x j := fun x hx =>
    rowSum_pos ha hrow (ne_of_gt (lt_of_le_of_lt hy0' ((hmemA x).mp hx)))
  have hposB : ∀ y ∈ B, 0 < ∑ j, a y j := fun y hy =>
    rowSum_pos ha hrow (ne_of_lt (lt_of_le_of_lt ((hmemB y).mp hy) hx0'))
  have hK : 0 < K := lt_of_lt_of_le (hposA x0 hx0) (hsum x0)
  -- the rows on `A`, divided by `(f x - s)^3`
  have hscal : ∀ x ∈ A, ∀ (y : Cube ι) (w : ι → ℝ),
      ∑ j ∈ diffSet x y, w j * (a x j / max (f x - s) 0 ^ 3) * a y j
        = (∑ j ∈ diffSet x y, w j * a x j * a y j) / (f x - s) ^ 3 := by
    intro x hx y w
    have hxs : 0 < f x - s := sub_pos.mpr ((hmemA x).mp hx)
    rw [max_eq_left hxs.le, Finset.sum_div]
    apply Finset.sum_congr rfl
    intro j _
    ring
  have key := abstract_cs A B (fun x j => a x j / max (f x - s) 0 ^ 3) a
    (fun x j => div_nonneg (ha x j) (pow_nonneg (le_max_right _ _) 3)) ha diffSet
    (3 / 2 * 4 ^ Fintype.card ι * M) hC ?_ ?_
  · -- the conclusion of the Cauchy–Schwarz lemma
    have h1 : ∑ x ∈ A, (f x - s) ^ 3 / K
        ≤ ∑ x ∈ A, (∑ j, a x j / max (f x - s) 0 ^ 3)⁻¹ := by
      apply Finset.sum_le_sum
      intro x hx
      have hxs : 0 < f x - s := sub_pos.mpr ((hmemA x).mp hx)
      rw [max_eq_left hxs.le, ← Finset.sum_div, inv_div]
      exact div_le_div_of_nonneg_left (pow_pos hxs 3).le (hposA x hx) (hsum x)
    have h2 : (B.card : ℝ) / K ≤ ∑ y ∈ B, (∑ j, a y j)⁻¹ := by
      have h := Finset.sum_le_sum (s := B) (f := fun _ => K⁻¹) (g := fun y => (∑ j, a y j)⁻¹)
        (fun y hy => inv_anti₀ (hposB y hy) (hsum y))
      rw [Finset.sum_const, nsmul_eq_mul] at h
      rw [div_eq_mul_inv]
      exact h
    have h3 : 0 ≤ ∑ x ∈ A, (f x - s) ^ 3 / K := Finset.sum_nonneg (fun x hx =>
      div_nonneg (pow_nonneg (sub_nonneg.mpr ((hmemA x).mp hx).le) 3) hK.le)
    have h4 : (0 : ℝ) ≤ (B.card : ℝ) / K := div_nonneg (Nat.cast_nonneg _) hK.le
    have h5 := le_trans (mul_le_mul h1 h2 h4 (le_trans h3 h1)) key
    rw [← Finset.sum_div] at h5
    have h6 : (∑ x ∈ A, (f x - s) ^ 3) / K * ((B.card : ℝ) / K)
        = (∑ x ∈ A, (f x - s) ^ 3) * (B.card : ℝ) / K ^ 2 := by ring
    rw [h6, div_le_iff₀ (by positivity)] at h5
    exact h5
  · -- the denominators are positive
    intro x hx y hy w hw
    rw [hscal x hx y w]
    exact div_pos
      (pairSum_pos ha hrow hw (lt_of_le_of_lt ((hmemB y).mp hy) ((hmemA x).mp hx)))
      (pow_pos (sub_pos.mpr ((hmemA x).mp hx)) 3)
  · -- the inequality for the pairs in `A × B`, from the integrated all-pairs inequality
    intro w hw
    have hT1 := four_mul_integrated hInt f a ha hrow w hw
    have hterm : ∀ x ∈ A, ∀ y ∈ B,
        (∑ j ∈ diffSet x y, w j * (a x j / max (f x - s) 0 ^ 3) * a y j)⁻¹
          ≤ 6 * ((f x - f y) ^ 3 / (6 * ∑ j ∈ diffSet x y, w j * a x j * a y j)) := by
      intro x hx y hy
      have hxs : 0 < f x - s := sub_pos.mpr ((hmemA x).mp hx)
      have hys : f y ≤ s := (hmemB y).mp hy
      have hS := pairSum_pos ha hrow hw (lt_of_le_of_lt hys ((hmemA x).mp hx))
      have e : 6 * ((f x - f y) ^ 3 / (6 * ∑ j ∈ diffSet x y, w j * a x j * a y j))
          = (f x - f y) ^ 3 / ∑ j ∈ diffSet x y, w j * a x j * a y j := by
        field_simp
      rw [hscal x hx y w, inv_div, e]
      exact div_le_div_of_nonneg_right
        (pow_le_pow_left₀ hxs.le (by linarith : f x - s ≤ f x - f y) 3) hS.le
    have hsub : ∀ x ∈ A, B ⊆ univ.filter (fun y : Cube ι => f y < f x) := by
      intro x hx y hy
      exact Finset.mem_filter.mpr
        ⟨Finset.mem_univ _, lt_of_le_of_lt ((hmemB y).mp hy) ((hmemA x).mp hx)⟩
    have hGnn : ∀ x : Cube ι, ∀ y ∈ univ.filter (fun y : Cube ι => f y < f x),
        0 ≤ 6 * ((f x - f y) ^ 3 / (6 * ∑ j ∈ diffSet x y, w j * a x j * a y j)) := by
      intro x y hy
      have hlt := (Finset.mem_filter.mp hy).2
      exact mul_nonneg (by norm_num) (div_nonneg (pow_nonneg (by linarith) 3)
        (mul_nonneg (by norm_num) (pairSum_pos ha hrow hw hlt).le))
    have h7 : ∑ j, meanAbsIncr f j / w j ≤ M * ∑ j, (w j)⁻¹ := by
      rw [Finset.mul_sum]
      apply Finset.sum_le_sum
      intro j _
      rw [div_eq_mul_inv]
      exact mul_le_mul_of_nonneg_right (hM j) (inv_pos.mpr (hw j)).le
    have h8 : (0 : ℝ) ≤ 4 ^ Fintype.card ι := by positivity
    have h9 := mul_le_mul_of_nonneg_left h7 h8
    calc ∑ x ∈ A, ∑ y ∈ B,
          (∑ j ∈ diffSet x y, w j * (a x j / max (f x - s) 0 ^ 3) * a y j)⁻¹
        ≤ ∑ x ∈ A, ∑ y ∈ B,
            6 * ((f x - f y) ^ 3 / (6 * ∑ j ∈ diffSet x y, w j * a x j * a y j)) :=
          Finset.sum_le_sum (fun x hx => Finset.sum_le_sum (fun y hy => hterm x hx y hy))
      _ ≤ ∑ x ∈ A, ∑ y ∈ univ.filter (fun y : Cube ι => f y < f x),
            6 * ((f x - f y) ^ 3 / (6 * ∑ j ∈ diffSet x y, w j * a x j * a y j)) :=
          Finset.sum_le_sum (fun x hx => Finset.sum_le_sum_of_subset_of_nonneg (hsub x hx)
            (fun y hy _ => hGnn x y hy))
      _ ≤ ∑ x, ∑ y ∈ univ.filter (fun y : Cube ι => f y < f x),
            6 * ((f x - f y) ^ 3 / (6 * ∑ j ∈ diffSet x y, w j * a x j * a y j)) :=
          Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
            (fun x _ _ => Finset.sum_nonneg (fun y hy => hGnn x y hy))
      _ = 6 * ∑ x, ∑ y ∈ univ.filter (fun y : Cube ι => f y < f x),
            (f x - f y) ^ 3 / (6 * ∑ j ∈ diffSet x y, w j * a x j * a y j) := by
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro x _
          rw [Finset.mul_sum]
      _ ≤ 3 / 2 * 4 ^ Fintype.card ι * M * ∑ j, (w j)⁻¹ := by linarith
end AaronsonAmbainis.Level
