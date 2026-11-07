-- Prove2me | solution 1 for AaronsonAmbainis.DetBij.fAg_flipSet_of_notMem
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T22:29:57.442201+00:00
-- url     : https://prove2.me/submissions/26839fe6-7e0b-4756-ac72-8b657d4a8cc7

import Definitions.Def_AaronsonAmbainis_DetBij_Basic
import Definitions.Def_AaronsonAmbainis_DetBij_Identity
import Theorems.Thm_AaronsonAmbainis_DetBij_flipSet_apply


set_option autoImplicit true
open AaronsonAmbainis AaronsonAmbainis.DetBij
open Finset MvPolynomial
variable {ι : Type} [Fintype ι] [DecidableEq ι]
omit [Fintype ι]
namespace AaronsonAmbainis.DetBij
theorem _root_.solution (x z : Cube ι) {S : Finset ι} {i : ι} (hi : i ∉ S) :
    fAg (flipSet x S) z i = fAg x z i := by
  unfold fAg
  rw [flipSet_apply, if_neg hi]
end AaronsonAmbainis.DetBij
