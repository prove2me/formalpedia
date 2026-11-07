-- Prove2me | solution 1 for AaronsonAmbainis.Level.rowSum_pos
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T22:39:53.529375+00:00
-- url     : https://prove2.me/submissions/1991c902-6231-4056-bb76-d212b05c877a

import Definitions.Def_AaronsonAmbainis_TwoSided_Basic
import Definitions.Def_AaronsonAmbainis_Level_Basic
import Theorems.Thm_AaronsonAmbainis_Level_abs_sub_le_rowSum

set_option autoImplicit true
open AaronsonAmbainis
open AaronsonAmbainis.Level
open Finset
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
omit [DecidableEq ι]
namespace AaronsonAmbainis.Level
theorem _root_.solution {f : Cube ι → ℝ} {a : Cube ι → ι → ℝ} (ha : ∀ x j, 0 ≤ a x j)
    (hrow : ∀ x y, |f x - f y| ≤ ∑ j ∈ diffSet x y, a x j) {x y : Cube ι} (hxy : f x ≠ f y) :
    0 < ∑ j, a x j :=
  lt_of_lt_of_le (abs_pos.mpr (sub_ne_zero.mpr hxy)) (abs_sub_le_rowSum ha hrow x y)
end AaronsonAmbainis.Level
