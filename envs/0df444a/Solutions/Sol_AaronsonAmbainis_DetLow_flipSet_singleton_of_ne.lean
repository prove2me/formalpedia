-- Prove2me | solution 1 for AaronsonAmbainis.DetLow.flipSet_singleton_of_ne
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T22:23:30.008202+00:00
-- url     : https://prove2.me/submissions/8ab6ad38-cb7e-46aa-8eb7-3d379fd7645d

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
theorem _root_.solution (x : Cube ι) {i j : ι} (h : i ≠ j) :
    flipSet x {j} i = x i := by
  simp [flipSet, h]
end AaronsonAmbainis.DetLow
