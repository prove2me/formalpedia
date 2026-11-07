-- Prove2me | solution 1 for AaronsonAmbainis.DetLow.flipSet_singleton_self
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T22:21:34.834845+00:00
-- url     : https://prove2.me/submissions/119269ba-481f-4c3d-9b20-88ef28a261bc

import Definitions.Def_AaronsonAmbainis_DetDefs
import Definitions.Def_AaronsonAmbainis_DetLow_Basic

set_option autoImplicit true
open AaronsonAmbainis
open AaronsonAmbainis.DetLow
open Finset MvPolynomial
variable {ι : Type} [Fintype ι] [DecidableEq ι]
omit [Fintype ι]
namespace AaronsonAmbainis.DetLow
theorem _root_.solution (x : Cube ι) (j : ι) :
    flipSet x {j} j = !(x j) := by
  simp [flipSet]
end AaronsonAmbainis.DetLow
