-- Prove2me | solution 1 for AaronsonAmbainis.DetBij.Qmat_apply
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T22:28:53.810441+00:00
-- url     : https://prove2.me/submissions/7f641b99-ce9c-4115-a51c-a280f3fe38cf

import Definitions.Def_AaronsonAmbainis_DetBij_Basic
import Definitions.Def_AaronsonAmbainis_DetBij_Identity

set_option autoImplicit true
open AaronsonAmbainis AaronsonAmbainis.DetBij
open Finset MvPolynomial
variable {ι : Type} [Fintype ι] [DecidableEq ι]
namespace AaronsonAmbainis.DetBij
theorem _root_.solution (g : Cube ι → Bool) (A : Cube ι → Finset ι) (x z : Ones g) :
    Qmat g A x z = if Disjoint (agSet x.1 z.1) (A x.1) then agMon x.1 z.1 else 0 := rfl
end AaronsonAmbainis.DetBij
