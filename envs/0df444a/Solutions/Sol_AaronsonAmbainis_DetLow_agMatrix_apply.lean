-- Prove2me | solution 1 for AaronsonAmbainis.DetLow.agMatrix_apply
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T22:27:43.756243+00:00
-- url     : https://prove2.me/submissions/b20c024c-9e34-4239-8d65-affbbfc92bf7

import Definitions.Def_AaronsonAmbainis_DetLow_Basic
import Definitions.Def_AaronsonAmbainis_DetLow_RowOps

set_option autoImplicit true
open AaronsonAmbainis
open AaronsonAmbainis.DetLow
open Finset MvPolynomial
variable {ι : Type} [Fintype ι] [DecidableEq ι]
omit [DecidableEq ι]
namespace AaronsonAmbainis.DetLow
theorem _root_.solution (g : Cube ι → Bool) (x z : Ones g) :
    agMatrix g x z = agMon x.1 z.1 := rfl
end AaronsonAmbainis.DetLow
