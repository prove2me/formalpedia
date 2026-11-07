-- Prove2me | solution 1 for AaronsonAmbainis.Bridge.antipode_eq_flipSet_univ
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T23:32:11.068609+00:00
-- url     : https://prove2.me/submissions/1137eaf4-16f4-4df9-a777-8b1773937e7c

import Definitions.Def_AaronsonAmbainis_Statements
import Definitions.Def_AaronsonAmbainis_Bridge_Basic

set_option autoImplicit true
open AaronsonAmbainis AaronsonAmbainis.Bridge
open Finset
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
namespace AaronsonAmbainis.Bridge
theorem _root_.solution (x : Cube ι) : antipode x = flipSet x univ := by
  funext i
  simp [antipode, flipSet]
end AaronsonAmbainis.Bridge
