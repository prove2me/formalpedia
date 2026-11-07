-- Prove2me | solution 1 for AaronsonAmbainis.Level.sum_abs_incr_le_of_rows
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T22:40:02.965236+00:00
-- url     : https://prove2.me/submissions/f7052bc7-2186-4227-a272-a4e7f818847a

import Definitions.Def_AaronsonAmbainis_TwoSided_Basic
import Definitions.Def_AaronsonAmbainis_Level_Basic
import Theorems.Thm_AaronsonAmbainis_Level_abs_incr_le_of_rows

set_option autoImplicit true
open AaronsonAmbainis
open AaronsonAmbainis.Level
open Finset
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
namespace AaronsonAmbainis.Level
theorem _root_.solution {f : Cube ι → ℝ} {a : Cube ι → ι → ℝ} {K : ℝ}
    (hsum : ∀ x, ∑ j, a x j ≤ K) (hrow : ∀ x y, |f x - f y| ≤ ∑ j ∈ diffSet x y, a x j)
    (u : Cube ι) : ∑ j, |f u - f (flipSet u {j})| ≤ K :=
  le_trans (Finset.sum_le_sum fun j _ => abs_incr_le_of_rows hrow u j) (hsum u)
end AaronsonAmbainis.Level
