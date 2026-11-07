-- Prove2me | solution 1 for AaronsonAmbainis.DetBij.mem_agSet
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T22:22:18.948881+00:00
-- url     : https://prove2.me/submissions/3f659b0d-9e5d-4f29-8b1d-e7c5a614cbd6

import Definitions.Def_AaronsonAmbainis_DetDefs
import Definitions.Def_AaronsonAmbainis_DetBij_Basic

set_option autoImplicit true
open AaronsonAmbainis AaronsonAmbainis.DetBij
open Finset MvPolynomial
variable {ι : Type} [Fintype ι] [DecidableEq ι]
omit [DecidableEq ι]
namespace AaronsonAmbainis.DetBij
theorem _root_.solution {x z : Cube ι} {i : ι} : i ∈ agSet x z ↔ x i = z i := by
  simp [agSet]
end AaronsonAmbainis.DetBij
