-- Prove2me | solution 1 for AaronsonAmbainis.DetLow.agMon_of_ne
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T22:29:10.275213+00:00
-- url     : https://prove2.me/submissions/60d1c85c-5022-41de-b24e-79c0098ea945

import Definitions.Def_AaronsonAmbainis_DetLow_Basic
import Definitions.Def_AaronsonAmbainis_DetLow_RowOps
import Theorems.Thm_AaronsonAmbainis_DetLow_agMon_eq_mul_erase
import Theorems.Thm_AaronsonAmbainis_DetLow_prod_erase_flipSet
import Theorems.Thm_AaronsonAmbainis_DetLow_flipSet_flipSet_singleton
import Theorems.Thm_AaronsonAmbainis_DetLow_flipSet_singleton_self
attribute [local simp] AaronsonAmbainis.DetLow.flipSet_flipSet_singleton
attribute [local simp] AaronsonAmbainis.DetLow.flipSet_singleton_self



set_option autoImplicit true
open AaronsonAmbainis
open AaronsonAmbainis.DetLow
open Finset MvPolynomial
variable {ι : Type} [Fintype ι] [DecidableEq ι]
namespace AaronsonAmbainis.DetLow
theorem _root_.solution (x z : Cube ι) (j : ι) (h : x j ≠ z j) :
    agMon (flipSet x {j}) z = X j * agMon x z := by
  have heq : flipSet x {j} j = z j := by
    rw [flipSet_singleton_self]
    revert h
    cases x j <;> cases z j <;> simp
  rw [agMon_eq_mul_erase x z j, agMon_eq_mul_erase (flipSet x {j}) z j, prod_erase_flipSet,
    if_neg h, if_pos heq, one_mul]
end AaronsonAmbainis.DetLow
