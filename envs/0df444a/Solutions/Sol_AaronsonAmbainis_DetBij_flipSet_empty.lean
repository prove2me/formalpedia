-- Prove2me | solution 1 for AaronsonAmbainis.DetBij.flipSet_empty
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T22:24:05.334432+00:00
-- url     : https://prove2.me/submissions/9d99556e-ffbb-49b1-b398-b0af21819eda

import Definitions.Def_AaronsonAmbainis_DetDefs
import Definitions.Def_AaronsonAmbainis_DetBij_Basic
import Theorems.Thm_AaronsonAmbainis_DetBij_flipSet_apply

set_option autoImplicit true
open AaronsonAmbainis AaronsonAmbainis.DetBij
open Finset MvPolynomial
variable {ι : Type} [Fintype ι] [DecidableEq ι]
omit [Fintype ι]
namespace AaronsonAmbainis.DetBij
theorem _root_.solution (x : Cube ι) : flipSet x ∅ = x := by
  funext i
  simp [flipSet_apply]
end AaronsonAmbainis.DetBij
