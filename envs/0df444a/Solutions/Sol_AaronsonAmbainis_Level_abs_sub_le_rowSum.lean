-- Prove2me | solution 1 for AaronsonAmbainis.Level.abs_sub_le_rowSum
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T22:37:56.128269+00:00
-- url     : https://prove2.me/submissions/18cbee35-eeae-47da-a735-da87b9cdd6ba

import Definitions.Def_AaronsonAmbainis_TwoSided_Basic
import Definitions.Def_AaronsonAmbainis_Level_Basic

set_option autoImplicit true
open AaronsonAmbainis
open AaronsonAmbainis.Level
open Finset
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
omit [DecidableEq ι]
namespace AaronsonAmbainis.Level
theorem _root_.solution {f : Cube ι → ℝ} {a : Cube ι → ι → ℝ} (ha : ∀ x j, 0 ≤ a x j)
    (hrow : ∀ x y, |f x - f y| ≤ ∑ j ∈ diffSet x y, a x j) (x y : Cube ι) :
    |f x - f y| ≤ ∑ j, a x j :=
  le_trans (hrow x y)
    (Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) (fun j _ _ => ha x j))
end AaronsonAmbainis.Level
