-- Prove2me | solution 1 for AaronsonAmbainis.Bridge.antipode_antipode
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T23:26:55.250305+00:00
-- url     : https://prove2.me/submissions/215ccf14-ec87-4165-ab2a-f20c17257da7

import Definitions.Def_AaronsonAmbainis_TwoSided_Overlap
import Definitions.Def_AaronsonAmbainis_Bridge_Basic
import Definitions.Def_AaronsonAmbainis_Bridge_Positivity

set_option autoImplicit true
open AaronsonAmbainis AaronsonAmbainis.Bridge
open Finset
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
omit [Fintype ι] [DecidableEq ι]
namespace AaronsonAmbainis.Bridge
theorem _root_.solution (x : Cube ι) : antipode (antipode x) = x := by
  funext i
  simp [antipode]
end AaronsonAmbainis.Bridge
