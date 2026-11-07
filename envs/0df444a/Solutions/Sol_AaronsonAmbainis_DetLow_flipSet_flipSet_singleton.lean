-- Prove2me | solution 1 for AaronsonAmbainis.DetLow.flipSet_flipSet_singleton
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T22:23:29.52447+00:00
-- url     : https://prove2.me/submissions/28ceebfb-d664-4302-b31c-3a65a43e9fe9

import Definitions.Def_AaronsonAmbainis_DetDefs
import Definitions.Def_AaronsonAmbainis_DetLow_Basic
import Theorems.Thm_AaronsonAmbainis_DetLow_flipSet_singleton_self
attribute [local simp] AaronsonAmbainis.DetLow.flipSet_singleton_self

set_option autoImplicit true
open AaronsonAmbainis
open AaronsonAmbainis.DetLow
open Finset MvPolynomial
variable {ι : Type} [Fintype ι] [DecidableEq ι]
omit [Fintype ι]
namespace AaronsonAmbainis.DetLow
theorem _root_.solution (x : Cube ι) (j : ι) :
    flipSet (flipSet x {j}) {j} = x := by
  funext i
  by_cases h : i = j
  · subst h; simp [flipSet]
  · simp [flipSet, h]
end AaronsonAmbainis.DetLow
