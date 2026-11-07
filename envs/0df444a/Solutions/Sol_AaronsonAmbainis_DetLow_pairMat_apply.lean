-- Prove2me | solution 1 for AaronsonAmbainis.DetLow.pairMat_apply
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T22:27:32.473864+00:00
-- url     : https://prove2.me/submissions/56d4ed85-0d4d-4d92-8c72-7e461b487afe

import Definitions.Def_AaronsonAmbainis_DetLow_Basic
import Definitions.Def_AaronsonAmbainis_DetLow_RowOps

set_option autoImplicit true
open AaronsonAmbainis
open AaronsonAmbainis.DetLow
open Finset MvPolynomial
variable {ι : Type} [Fintype ι] [DecidableEq ι]
namespace AaronsonAmbainis.DetLow
theorem _root_.solution (g : Cube ι → Bool) (j : ι) (x y : Ones g) :
    pairMat g j x y = if x.1 j = true ∧ y.1 = flipSet x.1 {j} then 1 else 0 := rfl
end AaronsonAmbainis.DetLow
