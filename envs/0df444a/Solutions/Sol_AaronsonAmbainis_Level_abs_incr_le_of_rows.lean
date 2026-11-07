-- Prove2me | solution 1 for AaronsonAmbainis.Level.abs_incr_le_of_rows
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T22:38:27.317221+00:00
-- url     : https://prove2.me/submissions/15e72928-1b8f-4efd-8c5b-fa2aa9546187

import Definitions.Def_AaronsonAmbainis_TwoSided_Basic
import Definitions.Def_AaronsonAmbainis_Level_Basic
import Theorems.Thm_AaronsonAmbainis_diffSet_flipSet


set_option autoImplicit true
open AaronsonAmbainis
open AaronsonAmbainis.Level
open Finset
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
namespace AaronsonAmbainis.Level
theorem _root_.solution {f : Cube ι → ℝ} {a : Cube ι → ι → ℝ}
    (hrow : ∀ x y, |f x - f y| ≤ ∑ j ∈ diffSet x y, a x j) (u : Cube ι) (j : ι) :
    |f u - f (flipSet u {j})| ≤ a u j := by
  have h := hrow u (flipSet u {j})
  rwa [diffSet_flipSet, Finset.sum_singleton] at h
end AaronsonAmbainis.Level
