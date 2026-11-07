-- Prove2me | solution 1 for AaronsonAmbainis.Bridge.extendRows_pos
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T23:27:49.904512+00:00
-- url     : https://prove2.me/submissions/e15e4cb2-236d-49ae-b54f-8e123d9b90b9

import Definitions.Def_AaronsonAmbainis_TwoSided_Overlap
import Definitions.Def_AaronsonAmbainis_Bridge_Basic
import Definitions.Def_AaronsonAmbainis_Bridge_Positivity

set_option autoImplicit true
open AaronsonAmbainis AaronsonAmbainis.Bridge
open Finset
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
namespace AaronsonAmbainis.Bridge
theorem _root_.solution {g : Cube ι → Bool} {lam : Cube ι → ι → ℝ} {x : Cube ι}
    (h : x ∈ zone g ∨ antipode x ∈ zone g) : extendRows g lam x = lam x := by
  unfold extendRows
  exact if_pos h
end AaronsonAmbainis.Bridge
