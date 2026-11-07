-- Prove2me | solution 1 for AaronsonAmbainis.Level.meanAbsIncr_sq_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T22:51:54.707146+00:00
-- url     : https://prove2.me/submissions/a53f5954-2910-4fe7-8e8e-791847c65e2d

import Definitions.Def_AaronsonAmbainis_TwoSided_Basic
import Definitions.Def_AaronsonAmbainis_Level_Basic
import Theorems.Thm_AaronsonAmbainis_Level_card_cube
import Theorems.Thm_AaronsonAmbainis_Level_inflR_eq_quarter
import Theorems.Thm_AaronsonAmbainis_card_cube


set_option autoImplicit true
open AaronsonAmbainis
open AaronsonAmbainis.Level
open Finset
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
namespace AaronsonAmbainis.Level
theorem _root_.solution (f : Cube ι → ℝ) (j : ι) : meanAbsIncr f j ^ 2 ≤ 4 * inflR f j := by
  have h2 : (0 : ℝ) < 2 ^ Fintype.card ι := by positivity
  have h := sq_sum_le_card_mul_sum_sq (s := (univ : Finset (Cube ι)))
    (f := fun x => |f x - f (flipSet x {j})|)
  simp only [sq_abs] at h
  rw [Finset.card_univ, card_cube] at h
  have e : 4 * inflR f j
      = (2 ^ Fintype.card ι * ∑ x, (f x - f (flipSet x {j})) ^ 2) / (2 ^ Fintype.card ι) ^ 2 := by
    rw [inflR_eq_quarter]
    field_simp
  unfold meanAbsIncr
  rw [e, div_pow]
  exact div_le_div_of_nonneg_right h (by positivity)
end AaronsonAmbainis.Level
