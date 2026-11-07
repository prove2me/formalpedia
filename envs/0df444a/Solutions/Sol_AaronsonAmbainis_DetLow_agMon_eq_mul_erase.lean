-- Prove2me | solution 1 for AaronsonAmbainis.DetLow.agMon_eq_mul_erase
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T22:27:35.012067+00:00
-- url     : https://prove2.me/submissions/20d6a8a6-ce60-44b7-9ec7-327df54c26c7

import Definitions.Def_AaronsonAmbainis_DetLow_Basic
import Definitions.Def_AaronsonAmbainis_DetLow_RowOps

set_option autoImplicit true
open AaronsonAmbainis
open AaronsonAmbainis.DetLow
open Finset MvPolynomial
variable {ι : Type} [Fintype ι] [DecidableEq ι]
namespace AaronsonAmbainis.DetLow
theorem _root_.solution (x z : Cube ι) (j : ι) :
    agMon x z = (if x j = z j then X j else 1) *
      ∏ i ∈ univ.erase j, (if x i = z i then (X i : MvPolynomial ι ℤ) else 1) := by
  unfold agMon
  exact (Finset.mul_prod_erase univ _ (mem_univ j)).symm
end AaronsonAmbainis.DetLow
