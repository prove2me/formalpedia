-- Prove2me | solution 1 for AaronsonAmbainis.Level.pairSum_pos
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T22:43:26.974196+00:00
-- url     : https://prove2.me/submissions/50717d9b-8085-4bc3-8e75-dfdd31832672

import Definitions.Def_AaronsonAmbainis_Level_Rows
import Definitions.Def_AaronsonAmbainis_TwoSided_Overlap
import Definitions.Def_AaronsonAmbainis_Level_AllPairs
import Theorems.Thm_AaronsonAmbainis_Level_sum_levRow
import Theorems.Thm_AaronsonAmbainis_Level_isRow_levRow
import Theorems.Thm_AaronsonAmbainis_overlap_pos


set_option autoImplicit true
open AaronsonAmbainis
open AaronsonAmbainis.Level
open Finset
variable {ι : Type} [Fintype ι] [DecidableEq ι]
namespace AaronsonAmbainis.Level
theorem _root_.solution {f : Cube ι → ℝ} {a : Cube ι → ι → ℝ} (ha : ∀ x j, 0 ≤ a x j)
    (hrow : ∀ x y, |f x - f y| ≤ ∑ j ∈ diffSet x y, a x j) {w : ι → ℝ} (hw : ∀ j, 0 < w j)
    {x y : Cube ι} (hxy : f y < f x) :
    0 < ∑ j ∈ diffSet x y, w j * a x j * a y j := by
  have hx : (f x + f y) / 2 < f x := by linarith
  have hy : f y < (f x + f y) / 2 := by linarith
  have hne : lev f ((f x + f y) / 2) x ≠ lev f ((f x + f y) / 2) y := by
    simp [lev, hx, not_lt.mpr hy.le]
  have h := overlap_pos hne (isRow_levRow ha hrow ((f x + f y) / 2) x)
    (isRow_levRow ha hrow ((f x + f y) / 2) y) hw
  rw [sum_levRow f a w hx hy] at h
  have hden : 0 < (f x - (f x + f y) / 2) * ((f x + f y) / 2 - f y) :=
    mul_pos (by linarith) (by linarith)
  by_contra hcon
  have h0 : (∑ j ∈ diffSet x y, w j * a x j * a y j)
      / ((f x - (f x + f y) / 2) * ((f x + f y) / 2 - f y)) ≤ 0 :=
    div_nonpos_of_nonpos_of_nonneg (not_lt.mp hcon) hden.le
  linarith
end AaronsonAmbainis.Level
