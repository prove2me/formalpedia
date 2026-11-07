-- Prove2me | solution 1 for AaronsonAmbainis.DetBij.flipSet_apply
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T22:22:08.991655+00:00
-- url     : https://prove2.me/submissions/021c1466-b3e7-4b33-b286-006853620005

import Definitions.Def_AaronsonAmbainis_DetDefs
import Definitions.Def_AaronsonAmbainis_DetBij_Basic

set_option autoImplicit true
open AaronsonAmbainis AaronsonAmbainis.DetBij
open Finset MvPolynomial
variable {ι : Type} [Fintype ι] [DecidableEq ι]
omit [Fintype ι]
namespace AaronsonAmbainis.DetBij
theorem _root_.solution (x : Cube ι) (S : Finset ι) (i : ι) :
    flipSet x S i = if i ∈ S then !(x i) else x i := rfl
end AaronsonAmbainis.DetBij
