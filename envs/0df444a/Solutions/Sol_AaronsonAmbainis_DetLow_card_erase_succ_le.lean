-- Prove2me | solution 1 for AaronsonAmbainis.DetLow.card_erase_succ_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T22:25:58.790035+00:00
-- url     : https://prove2.me/submissions/755f23f8-06fa-40d0-b1fa-735d6182c420

import Definitions.Def_AaronsonAmbainis_DetLow_Basic
import Definitions.Def_AaronsonAmbainis_DetLow_NonZero
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
theorem _root_.solution (g : Cube ι → Bool) (x : Ones g) :
    (univ.erase x).card + 1 ≤ 2 ^ Fintype.card ι := by
  have h2 : (univ.erase x).card < (univ : Finset (Ones g)).card :=
    Finset.card_erase_lt_of_mem (mem_univ x)
  have h3 : (univ : Finset (Ones g)).card ≤ 2 ^ Fintype.card ι := by
    rw [Finset.card_univ]
    calc Fintype.card (Ones g) ≤ Fintype.card (Cube ι) := Fintype.card_subtype_le _
      _ = 2 ^ Fintype.card ι := by simp
  omega
end AaronsonAmbainis.DetLow
