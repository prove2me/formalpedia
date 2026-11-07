-- Prove2me | solution 1 for AaronsonAmbainis.DetBij.fAg_flipSet_of_mem
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T22:29:55.814245+00:00
-- url     : https://prove2.me/submissions/b1053db2-0a56-4af1-a21b-d06cfcf03caa

import Definitions.Def_AaronsonAmbainis_DetBij_Basic
import Definitions.Def_AaronsonAmbainis_DetBij_Identity
import Theorems.Thm_AaronsonAmbainis_DetBij_flipSet_apply


set_option autoImplicit true
open AaronsonAmbainis AaronsonAmbainis.DetBij
open Finset MvPolynomial
variable {ι : Type} [Fintype ι] [DecidableEq ι]
omit [Fintype ι]
namespace AaronsonAmbainis.DetBij
theorem _root_.solution (x z : Cube ι) {S : Finset ι} {i : ι} (hi : i ∈ S) :
    fAg (flipSet x S) z i = gAg x z i := by
  unfold fAg gAg
  rw [flipSet_apply, if_pos hi]
  cases x i <;> cases z i <;> simp
end AaronsonAmbainis.DetBij
