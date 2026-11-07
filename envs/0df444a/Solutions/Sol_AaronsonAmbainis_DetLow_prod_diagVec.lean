-- Prove2me | solution 1 for AaronsonAmbainis.DetLow.prod_diagVec
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T22:28:00.638546+00:00
-- url     : https://prove2.me/submissions/f2316458-4b00-4935-af13-8a5e9fbc5625

import Definitions.Def_AaronsonAmbainis_DetLow_Basic
import Definitions.Def_AaronsonAmbainis_DetLow_RowOps

set_option autoImplicit true
open AaronsonAmbainis
open AaronsonAmbainis.DetLow
open Finset MvPolynomial
variable {ι : Type} [Fintype ι] [DecidableEq ι]
namespace AaronsonAmbainis.DetLow
theorem _root_.solution (g : Cube ι → Bool) (j : ι) :
    ∏ x, diagVec g j x = (1 - X j ^ 2) ^ (Up g j).card := by
  unfold diagVec
  rw [Finset.prod_ite_mem, Finset.univ_inter, Finset.prod_const]
end AaronsonAmbainis.DetLow
