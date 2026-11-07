-- Prove2me | solution 1 for AaronsonAmbainis.DetBij.agMon_eq_prod
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T22:29:51.983064+00:00
-- url     : https://prove2.me/submissions/b409df22-4a31-48a9-be4d-6502b0618671

import Definitions.Def_AaronsonAmbainis_DetBij_Basic
import Definitions.Def_AaronsonAmbainis_DetBij_Identity

set_option autoImplicit true
open AaronsonAmbainis AaronsonAmbainis.DetBij
open Finset MvPolynomial
variable {ι : Type} [Fintype ι] [DecidableEq ι]
omit [DecidableEq ι]
namespace AaronsonAmbainis.DetBij
theorem _root_.solution (x z : Cube ι) : agMon x z = ∏ i, fAg x z i := rfl
end AaronsonAmbainis.DetBij
