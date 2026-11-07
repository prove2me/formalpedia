-- Prove2me | solution 1 for AaronsonAmbainis.Level.sum_levRow
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T22:34:30.727644+00:00
-- url     : https://prove2.me/submissions/f65b30ec-e30a-4d7f-a2e8-54646db4de38

import Definitions.Def_AaronsonAmbainis_Level_Rows
import Definitions.Def_AaronsonAmbainis_TwoSided_Overlap
import Definitions.Def_AaronsonAmbainis_Level_AllPairs

set_option autoImplicit true
open AaronsonAmbainis
open AaronsonAmbainis.Level
open Finset
variable {ι : Type} [Fintype ι] [DecidableEq ι]
omit [DecidableEq ι]
namespace AaronsonAmbainis.Level
theorem _root_.solution (f : Cube ι → ℝ) (a : Cube ι → ι → ℝ) (w : ι → ℝ) {t : ℝ} {x y : Cube ι}
    (hx : t < f x) (hy : f y < t) :
    ∑ j ∈ diffSet x y, w j * levRow f a t x j * levRow f a t y j
      = (∑ j ∈ diffSet x y, w j * a x j * a y j) / ((f x - t) * (t - f y)) := by
  have hxne : f x ≠ t := ne_of_gt hx
  have hyne : f y ≠ t := ne_of_lt hy
  have h1 : f x - t ≠ 0 := sub_ne_zero.mpr hxne
  have h2 : t - f y ≠ 0 := sub_ne_zero.mpr hyne.symm
  rw [Finset.sum_div]
  apply Finset.sum_congr rfl
  intro j _
  have e1 : levRow f a t x j = a x j / (f x - t) := by
    show (if f x = t then 1 else a x j / |f x - t|) = a x j / (f x - t)
    rw [if_neg hxne, abs_of_pos (sub_pos.mpr hx)]
  have e2 : levRow f a t y j = a y j / (t - f y) := by
    show (if f y = t then 1 else a y j / |f y - t|) = a y j / (t - f y)
    rw [if_neg hyne, abs_of_neg (sub_neg.mpr hy), neg_sub]
  rw [e1, e2]
  field_simp
end AaronsonAmbainis.Level
