-- Prove2me | solution 1 for AaronsonAmbainis.DetBij.agMatrix_apply
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T22:29:51.493227+00:00
-- url     : https://prove2.me/submissions/5b5135d9-75b1-4698-a13f-4c81e4bb176f

import Definitions.Def_AaronsonAmbainis_DetBij_Basic
import Definitions.Def_AaronsonAmbainis_DetBij_Identity

set_option autoImplicit true
open AaronsonAmbainis AaronsonAmbainis.DetBij
open Finset MvPolynomial
variable {ι : Type} [Fintype ι] [DecidableEq ι]
omit [DecidableEq ι]
namespace AaronsonAmbainis.DetBij
theorem _root_.solution (g : Cube ι → Bool) (x z : Ones g) :
    agMatrix g x z = agMon x.1 z.1 := rfl
end AaronsonAmbainis.DetBij
