-- Prove2me | solution 1 for AaronsonAmbainis.Average.sum_flip
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T22:35:36.580161+00:00
-- url     : https://prove2.me/submissions/3bae055f-c587-4e32-95cb-30282bf245e1

import Definitions.Def_AaronsonAmbainis_TwoSided_Basic
import Definitions.Def_AaronsonAmbainis_Average_Coordinate
import Theorems.Thm_AaronsonAmbainis_flipSet_flipSet_self


set_option autoImplicit true
open AaronsonAmbainis
open AaronsonAmbainis.Average
open Finset
variable {ι : Type} [Fintype ι] [DecidableEq ι]
namespace AaronsonAmbainis.Average
theorem _root_.solution (j : ι) (F : Cube ι → ℝ) : ∑ x, F (flipSet x {j}) = ∑ x, F x := by
  have hinv : Function.Involutive (fun x : Cube ι => flipSet x {j}) :=
    fun x => flipSet_flipSet_self x {j}
  exact Equiv.sum_comp hinv.toPerm F
end AaronsonAmbainis.Average
