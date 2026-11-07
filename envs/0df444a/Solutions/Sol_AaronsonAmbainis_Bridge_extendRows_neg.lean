-- Prove2me | solution 1 for AaronsonAmbainis.Bridge.extendRows_neg
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T23:27:55.213196+00:00
-- url     : https://prove2.me/submissions/c0aea6ff-bf69-4472-99e2-0c13eb955ab3

import Definitions.Def_AaronsonAmbainis_TwoSided_Overlap
import Definitions.Def_AaronsonAmbainis_Bridge_Basic
import Definitions.Def_AaronsonAmbainis_Bridge_Positivity

set_option autoImplicit true
open AaronsonAmbainis AaronsonAmbainis.Bridge
open Finset
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
namespace AaronsonAmbainis.Bridge
theorem _root_.solution {g : Cube ι → Bool} {lam : Cube ι → ι → ℝ} {x : Cube ι}
    (h : ¬ (x ∈ zone g ∨ antipode x ∈ zone g)) : extendRows g lam x = fun _ => 1 := by
  unfold extendRows
  exact if_neg h
end AaronsonAmbainis.Bridge
