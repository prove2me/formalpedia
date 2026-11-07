-- Prove2me | solution 1 for AaronsonAmbainis.Bridge.hasDegreeLE_mono
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T22:58:10.677855+00:00
-- url     : https://prove2.me/submissions/2bfdd897-5435-4719-9cb7-bad93f17f12e

import Definitions.Def_AaronsonAmbainis_Statements
import Definitions.Def_AaronsonAmbainis_Bridge_Basic

set_option autoImplicit true
open AaronsonAmbainis AaronsonAmbainis.Bridge
open Finset
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
omit [DecidableEq ι]
namespace AaronsonAmbainis.Bridge
theorem _root_.solution {f : Cube ι → ℝ} {d d' : ℕ} (h : HasDegreeLE f d) (hdd : d ≤ d') :
    HasDegreeLE f d' := by
  obtain ⟨c, hc, hf⟩ := h
  exact ⟨c, fun S hS => hc S (lt_of_le_of_lt hdd hS), hf⟩
end AaronsonAmbainis.Bridge
