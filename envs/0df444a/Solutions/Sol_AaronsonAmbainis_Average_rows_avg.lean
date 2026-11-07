-- Prove2me | solution 1 for AaronsonAmbainis.Average.rows_avg
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T22:42:07.185222+00:00
-- url     : https://prove2.me/submissions/f61d61de-6256-4e9c-99a5-0aaf68cd720c

import Definitions.Def_AaronsonAmbainis_TwoSided_Basic
import Definitions.Def_AaronsonAmbainis_Average_Coordinate
import Theorems.Thm_AaronsonAmbainis_Average_diffSet_flip

set_option autoImplicit true
open AaronsonAmbainis
open AaronsonAmbainis.Average
open Finset
variable {ι : Type} [Fintype ι] [DecidableEq ι]
namespace AaronsonAmbainis.Average
theorem _root_.solution (j : ι) {f : Cube ι → ℝ} {a : Cube ι → ι → ℝ} {K : ℝ}
    (ha : ∀ x i, 0 ≤ a x i) (hsum : ∀ x, ∑ i, a x i ≤ K)
    (hrow : ∀ x y, |f x - f y| ≤ ∑ i ∈ diffSet x y, a x i) :
    (∀ x i, 0 ≤ (a x i + a (flipSet x {j}) i) / 2) ∧
    (∀ x, ∑ i, (a x i + a (flipSet x {j}) i) / 2 ≤ K) ∧
    ∀ x y, |avg j f x - avg j f y| ≤ ∑ i ∈ diffSet x y, (a x i + a (flipSet x {j}) i) / 2 := by
  refine ⟨fun x i => div_nonneg (add_nonneg (ha x i) (ha _ i)) (by norm_num), fun x => ?_,
    fun x y => ?_⟩
  · rw [← Finset.sum_div, Finset.sum_add_distrib]
    linarith [hsum x, hsum (flipSet x {j})]
  · have h1 := hrow x y
    have h2 := hrow (flipSet x {j}) (flipSet y {j})
    rw [diffSet_flip] at h2
    have e : avg j f x - avg j f y
        = ((f x - f y) + (f (flipSet x {j}) - f (flipSet y {j}))) / 2 := by
      unfold avg
      ring
    rw [e, abs_div, abs_two, ← Finset.sum_div, Finset.sum_add_distrib]
    exact div_le_div_of_nonneg_right (le_trans (abs_add_le _ _) (add_le_add h1 h2))
      (by norm_num)
end AaronsonAmbainis.Average
