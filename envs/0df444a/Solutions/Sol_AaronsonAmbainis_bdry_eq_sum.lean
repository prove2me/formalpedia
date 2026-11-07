-- Prove2me | solution 1 for AaronsonAmbainis.bdry_eq_sum
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T22:32:34.540011+00:00
-- url     : https://prove2.me/submissions/033d8054-51a2-43c1-9980-a4dd40e66795

import Definitions.Def_AaronsonAmbainis_TwoSided_Glue
import Definitions.Def_AaronsonAmbainis_TwoSided_AllPairsCore

set_option autoImplicit true
open AaronsonAmbainis
open Finset
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
namespace AaronsonAmbainis
theorem _root_.solution (g : Cube ι → Bool) (j : ι) :
    (bdry g j : ℝ) = ∑ x, (if g x = true ∧ g (flipSet x {j}) = false then (1 : ℝ) else 0) := by
  unfold bdry
  rw [Finset.sum_boole]
end AaronsonAmbainis
