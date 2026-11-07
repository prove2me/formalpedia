-- Prove2me | solution 1 for AaronsonAmbainis.Level.exists_abs_cube_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T23:08:21.213199+00:00
-- url     : https://prove2.me/submissions/88b44180-d502-4970-b62d-d202ce5f834e

import Definitions.Def_AaronsonAmbainis_Level_Basic
import Definitions.Def_AaronsonAmbainis_Level_Median
import Definitions.Def_AaronsonAmbainis_Level_ThirdMoment
import Definitions.Def_AaronsonAmbainis_Level_Increments
import Theorems.Thm_AaronsonAmbainis_Level_card_cube
import Theorems.Thm_AaronsonAmbainis_Level_exists_median
import Theorems.Thm_AaronsonAmbainis_Level_thirdMoment_lower
import Theorems.Thm_AaronsonAmbainis_card_cube


set_option autoImplicit true
open AaronsonAmbainis
open Finset
open AaronsonAmbainis.Level
variable {ι : Type} [Fintype ι] [DecidableEq ι]
namespace AaronsonAmbainis.Level
theorem _root_.solution (hTM : ThirdMomentInequality) (f : Cube ι → ℝ) (a : Cube ι → ι → ℝ)
    (ha : ∀ x j, 0 ≤ a x j) {K : ℝ} (hsum : ∀ x, ∑ j, a x j ≤ K)
    (hrow : ∀ x y, |f x - f y| ≤ ∑ j ∈ diffSet x y, a x j)
    {M : ℝ} (hM0 : 0 ≤ M) (hM : ∀ j, meanAbsIncr f j ≤ M) :
    ∃ m : ℝ, (∑ x, |f x - m| ^ 3) / 2 ^ Fintype.card ι ≤ 6 * K ^ 2 * M := by
  obtain ⟨m, hm1, hm2⟩ := exists_median f
  refine ⟨m, ?_⟩
  have h2 : (0 : ℝ) < 2 ^ Fintype.card ι := by positivity
  have hcard : ((Fintype.card (Cube ι) : ℕ) : ℝ) = 2 ^ Fintype.card ι := card_cube
  -- each of the two sets `{f ≤ m}`, `{m ≤ f}` has measure at least `1/2`
  have hB1 : (1 : ℝ) / 2
      ≤ ((univ.filter (fun y : Cube ι => f y ≤ m)).card : ℝ) / 2 ^ Fintype.card ι := by
    rw [le_div_iff₀ h2]
    have h : ((Fintype.card (Cube ι) : ℕ) : ℝ)
        ≤ 2 * ((univ.filter (fun y : Cube ι => f y ≤ m)).card : ℝ) := by exact_mod_cast hm1
    rw [hcard] at h
    linarith
  have hB2 : (1 : ℝ) / 2
      ≤ ((univ.filter (fun y : Cube ι => m ≤ f y)).card : ℝ) / 2 ^ Fintype.card ι := by
    rw [le_div_iff₀ h2]
    have h : ((Fintype.card (Cube ι) : ℕ) : ℝ)
        ≤ 2 * ((univ.filter (fun y : Cube ι => m ≤ f y)).card : ℝ) := by exact_mod_cast hm2
    rw [hcard] at h
    linarith
  have hup := hTM ι f K a ha hsum hrow M hM0 hM m
  have hlo := thirdMoment_lower hTM f a ha hsum hrow hM0 hM m
  have hPnn : 0 ≤ (∑ x, max (f x - m) 0 ^ 3) / 2 ^ Fintype.card ι :=
    div_nonneg (Finset.sum_nonneg fun x _ => pow_nonneg (le_max_right _ _) 3) h2.le
  have hQnn : 0 ≤ (∑ x, max (m - f x) 0 ^ 3) / 2 ^ Fintype.card ι :=
    div_nonneg (Finset.sum_nonneg fun x _ => pow_nonneg (le_max_right _ _) 3) h2.le
  have hP : (∑ x, max (f x - m) 0 ^ 3) / 2 ^ Fintype.card ι ≤ 3 * K ^ 2 * M := by
    have h := mul_le_mul_of_nonneg_left hB1 hPnn
    linarith
  have hQ : (∑ x, max (m - f x) 0 ^ 3) / 2 ^ Fintype.card ι ≤ 3 * K ^ 2 * M := by
    have h := mul_le_mul_of_nonneg_left hB2 hQnn
    linarith
  have hsplit : ∑ x, |f x - m| ^ 3
      = ∑ x, max (f x - m) 0 ^ 3 + ∑ x, max (m - f x) 0 ^ 3 := by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro x _
    rcases le_total 0 (f x - m) with h | h
    · rw [abs_of_nonneg h, max_eq_left h, max_eq_right (by linarith : m - f x ≤ 0)]
      ring
    · rw [abs_of_nonpos h, max_eq_right h, max_eq_left (by linarith : 0 ≤ m - f x)]
      ring
  rw [hsplit, add_div]
  linarith
end AaronsonAmbainis.Level
