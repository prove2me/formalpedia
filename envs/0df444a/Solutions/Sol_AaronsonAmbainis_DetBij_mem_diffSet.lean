-- Prove2me | solution 1 for AaronsonAmbainis.DetBij.mem_diffSet
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T22:22:09.6102+00:00
-- url     : https://prove2.me/submissions/edc66e4d-fe3f-4a69-8946-36685cba5360

import Definitions.Def_AaronsonAmbainis_DetDefs
import Definitions.Def_AaronsonAmbainis_DetBij_Basic

set_option autoImplicit true
open AaronsonAmbainis AaronsonAmbainis.DetBij
open Finset MvPolynomial
variable {ι : Type} [Fintype ι] [DecidableEq ι]
omit [DecidableEq ι]
namespace AaronsonAmbainis.DetBij
theorem _root_.solution {x z : Cube ι} {i : ι} : i ∈ diffSet x z ↔ x i ≠ z i := by
  simp [diffSet]
end AaronsonAmbainis.DetBij
