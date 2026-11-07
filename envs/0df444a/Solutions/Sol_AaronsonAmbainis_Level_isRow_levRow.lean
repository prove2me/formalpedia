-- Prove2me | solution 1 for AaronsonAmbainis.Level.isRow_levRow
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T22:40:35.926978+00:00
-- url     : https://prove2.me/submissions/fae517ff-a938-4e3c-aad1-e1bd08154030

import Definitions.Def_AaronsonAmbainis_TwoSided_Basic
import Definitions.Def_AaronsonAmbainis_Level_Rows
import Theorems.Thm_AaronsonAmbainis_Level_abs_sub_le_of_lev_ne
import Theorems.Thm_AaronsonAmbainis_diffSet_flipSet
import Theorems.Thm_AaronsonAmbainis_flipSet_empty


set_option autoImplicit true
open AaronsonAmbainis
open AaronsonAmbainis.Level
open Finset
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
namespace AaronsonAmbainis.Level
theorem _root_.solution {f : Cube ι → ℝ} {a : Cube ι → ι → ℝ} (ha : ∀ x j, 0 ≤ a x j)
    (hrow : ∀ x y, |f x - f y| ≤ ∑ j ∈ diffSet x y, a x j) (t : ℝ) (x : Cube ι) :
    IsRow (lev f t) x (levRow f a t x) := by
  refine ⟨fun j => ?_, fun S hS => ?_⟩
  · unfold levRow
    split_ifs
    · exact zero_le_one
    · exact div_nonneg (ha x j) (abs_nonneg _)
  · by_cases hx : f x = t
    · have hne : S.Nonempty := by
        rw [Finset.nonempty_iff_ne_empty]
        rintro rfl
        rw [flipSet_empty] at hS
        exact hS rfl
      have h1 : ∀ j ∈ S, levRow f a t x j = 1 := fun j _ => by simp [levRow, hx]
      rw [Finset.sum_congr rfl h1, Finset.sum_const, nsmul_eq_mul, mul_one]
      exact_mod_cast hne.card_pos
    · have hpos : 0 < |f x - t| := abs_pos.mpr (sub_ne_zero.mpr hx)
      have h1 : |f x - t| ≤ ∑ j ∈ S, a x j := by
        have h2 := hrow x (flipSet x S)
        rw [diffSet_flipSet] at h2
        exact le_trans (abs_sub_le_of_lev_ne hS) h2
      have h3 : ∀ j ∈ S, levRow f a t x j = a x j / |f x - t| :=
        fun j _ => by simp [levRow, hx]
      rw [Finset.sum_congr rfl h3, ← Finset.sum_div, le_div_iff₀ hpos, one_mul]
      exact h1
end AaronsonAmbainis.Level
