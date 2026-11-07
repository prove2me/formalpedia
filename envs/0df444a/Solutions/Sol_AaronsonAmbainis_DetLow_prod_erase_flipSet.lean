-- Prove2me | solution 1 for AaronsonAmbainis.DetLow.prod_erase_flipSet
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T22:27:36.69061+00:00
-- url     : https://prove2.me/submissions/011ac913-ee88-4a53-9897-a1952612f252

import Definitions.Def_AaronsonAmbainis_DetLow_Basic
import Definitions.Def_AaronsonAmbainis_DetLow_RowOps
import Theorems.Thm_AaronsonAmbainis_DetLow_flipSet_singleton_of_ne


set_option autoImplicit true
open AaronsonAmbainis
open AaronsonAmbainis.DetLow
open Finset MvPolynomial
variable {ι : Type} [Fintype ι] [DecidableEq ι]
namespace AaronsonAmbainis.DetLow
theorem _root_.solution (x z : Cube ι) (j : ι) :
    ∏ i ∈ univ.erase j, (if flipSet x {j} i = z i then (X i : MvPolynomial ι ℤ) else 1)
      = ∏ i ∈ univ.erase j, (if x i = z i then (X i : MvPolynomial ι ℤ) else 1) := by
  apply Finset.prod_congr rfl
  intro i hi
  rw [flipSet_singleton_of_ne x (Finset.ne_of_mem_erase hi)]
end AaronsonAmbainis.DetLow
