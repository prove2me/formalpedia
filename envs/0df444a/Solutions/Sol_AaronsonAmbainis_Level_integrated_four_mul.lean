-- Prove2me | solution 1 for AaronsonAmbainis.Level.integrated_four_mul
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T22:48:05.013526+00:00
-- url     : https://prove2.me/submissions/8701b387-c08e-4156-aa05-3657f5d7cdfc

import Definitions.Def_AaronsonAmbainis_Level_Basic
import Definitions.Def_AaronsonAmbainis_Level_Integral
import Definitions.Def_AaronsonAmbainis_Level_AllPairs
import Definitions.Def_AaronsonAmbainis_Level_Integrated
import Theorems.Thm_AaronsonAmbainis_Level_integrated_core
import Theorems.Thm_AaronsonAmbainis_Level_sum_posPart_incr

set_option autoImplicit true
open AaronsonAmbainis
open Finset
open AaronsonAmbainis.Level
variable {ι : Type} [Fintype ι] [DecidableEq ι]
namespace AaronsonAmbainis.Level
theorem _root_.solution (hAllPairs : AllPairsInequality) (f : Cube ι → ℝ)
    (a : Cube ι → ι → ℝ) (ha : ∀ x j, 0 ≤ a x j)
    (hrow : ∀ x y, |f x - f y| ≤ ∑ j ∈ diffSet x y, a x j) (w : ι → ℝ) (hw : ∀ j, 0 < w j) :
    4 * ∑ x, ∑ y ∈ univ.filter (fun y => f y < f x),
        (f x - f y) ^ 3 / (6 * ∑ j ∈ diffSet x y, w j * a x j * a y j)
      ≤ 4 ^ Fintype.card ι * ∑ j, meanAbsIncr f j / w j := by
  have h := integrated_core hAllPairs f a ha hrow w hw
  have hL : ∑ x, ∑ y ∈ univ.filter (fun y => f y < f x),
        (f x - f y) ^ 3 / (6 * ∑ j ∈ diffSet x y, w j * a x j * a y j)
      = ∑ x, ∑ y, max (f x - f y) 0 ^ 3 / 6
          * (∑ j ∈ diffSet x y, w j * a x j * a y j)⁻¹ := by
    apply Finset.sum_congr rfl
    intro x _
    rw [Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro y _
    by_cases hxy : f y < f x
    · rw [if_pos hxy, max_eq_left (by linarith : 0 ≤ f x - f y)]
      ring
    · rw [if_neg hxy, max_eq_right (by linarith [not_lt.mp hxy] : f x - f y ≤ 0)]
      ring
  have hRt : ∀ j, (∑ x, max (f x - f (flipSet x {j})) 0) / w j
      = 2 ^ Fintype.card ι / 2 * (meanAbsIncr f j / w j) := by
    intro j
    have h2 : (2 : ℝ) ^ Fintype.card ι ≠ 0 := by positivity
    rw [sum_posPart_incr]
    unfold meanAbsIncr
    field_simp
  have h4 : (4 : ℝ) ^ Fintype.card ι = 2 ^ Fintype.card ι * 2 ^ Fintype.card ι := by
    rw [← mul_pow]
    norm_num
  rw [hL]
  calc 4 * ∑ x, ∑ y, max (f x - f y) 0 ^ 3 / 6
          * (∑ j ∈ diffSet x y, w j * a x j * a y j)⁻¹
      ≤ 2 * (2 ^ Fintype.card ι * ∑ j, (∑ x, max (f x - f (flipSet x {j})) 0) / w j) := by
        linarith
    _ = 4 ^ Fintype.card ι * ∑ j, meanAbsIncr f j / w j := by
        rw [Finset.sum_congr rfl (fun j _ => hRt j), ← Finset.mul_sum, h4]
        ring
end AaronsonAmbainis.Level
