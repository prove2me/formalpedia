-- Prove2me | solution 1 for AaronsonAmbainis.Bridge.hasDegreeLE_iff_hasDegLE
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T22:51:49.383194+00:00
-- url     : https://prove2.me/submissions/94f3be0b-13a4-4b98-9c26-c5d6bc02aca4

import Definitions.Def_AaronsonAmbainis_Bridge_Basic
import Definitions.Def_AaronsonAmbainis_Bridge_ZeroOne

set_option autoImplicit true
open AaronsonAmbainis AaronsonAmbainis.Bridge
open Finset
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
omit [DecidableEq ι]
namespace AaronsonAmbainis.Bridge
theorem _root_.solution {f : Cube ι → ℝ} {d : ℕ} :
    HasDegreeLE f d ↔ HasDegLE (fun b => if b then (-1 : ℝ) else 1) f d :=
  Iff.rfl
end AaronsonAmbainis.Bridge
