-- Prove2me | solution 1 for AaronsonAmbainis.Level.level_allPairs
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T22:43:27.573588+00:00
-- url     : https://prove2.me/submissions/388a99fc-b942-4ff1-861d-19463bc71ad7

import Definitions.Def_AaronsonAmbainis_Level_Rows
import Definitions.Def_AaronsonAmbainis_TwoSided_Overlap
import Definitions.Def_AaronsonAmbainis_Level_AllPairs
import Theorems.Thm_AaronsonAmbainis_Level_sum_levRow
import Theorems.Thm_AaronsonAmbainis_Level_isRow_levRow


set_option autoImplicit true
open AaronsonAmbainis
open AaronsonAmbainis.Level
open Finset
variable {ι : Type} [Fintype ι] [DecidableEq ι]
namespace AaronsonAmbainis.Level
theorem _root_.solution (hAllPairs : AllPairsInequality) (f : Cube ι → ℝ) (a : Cube ι → ι → ℝ)
    (ha : ∀ x j, 0 ≤ a x j) (hrow : ∀ x y, |f x - f y| ≤ ∑ j ∈ diffSet x y, a x j)
    (w : ι → ℝ) (hw : ∀ j, 0 < w j) (t : ℝ) :
    2 * ∑ x, ∑ y, max (f x - t) 0 * max (t - f y) 0
          * (∑ j ∈ diffSet x y, w j * a x j * a y j)⁻¹
      ≤ 2 ^ Fintype.card ι * ∑ j, (bdry (lev f t) j : ℝ) / w j := by
  have hrows := isRow_levRow ha hrow t
  have h := hAllPairs ι (lev f t) w hw (levRow f a t) hrows
  refine le_trans ?_ h
  apply mul_le_mul_of_nonneg_left _ (by norm_num)
  rw [Finset.sum_filter]
  apply Finset.sum_le_sum
  intro x _
  by_cases hx : t < f x
  · have hlx : lev f t x = true := by simp [lev, hx]
    rw [if_pos hlx, Finset.sum_filter]
    apply Finset.sum_le_sum
    intro y _
    by_cases hy : t < f y
    · have hly : ¬ lev f t y = false := by simp [lev, hy]
      rw [if_neg hly, max_eq_right (by linarith : t - f y ≤ 0), mul_zero, zero_mul]
    · have hly : lev f t y = false := by simp [lev, hy]
      rw [if_pos hly]
      rcases lt_or_eq_of_le (not_lt.mp hy) with hyt | hyt
      · rw [sum_levRow f a w hx hyt, inv_div, max_eq_left (by linarith : 0 ≤ f x - t),
          max_eq_left (by linarith : 0 ≤ t - f y), div_eq_mul_inv]
      · rw [max_eq_right (by linarith : t - f y ≤ 0), mul_zero, zero_mul]
        exact inv_nonneg.mpr (Finset.sum_nonneg fun j _ =>
          mul_nonneg (mul_nonneg (hw j).le ((hrows x).1 j)) ((hrows y).1 j))
  · have hlx : ¬ lev f t x = true := by simp [lev, hx]
    rw [if_neg hlx]
    apply le_of_eq
    apply Finset.sum_eq_zero
    intro y _
    rw [max_eq_right (by linarith [not_lt.mp hx] : f x - t ≤ 0), zero_mul, zero_mul]
end AaronsonAmbainis.Level
