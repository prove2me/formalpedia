-- Prove2me | solution 1 for AaronsonAmbainis.Bridge.diffSet_antipode
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T23:26:52.39859+00:00
-- url     : https://prove2.me/submissions/4f3c4519-de98-47a6-96c3-b964eb633ccf

import Definitions.Def_AaronsonAmbainis_TwoSided_Overlap
import Definitions.Def_AaronsonAmbainis_Bridge_Basic
import Definitions.Def_AaronsonAmbainis_Bridge_Positivity

set_option autoImplicit true
open AaronsonAmbainis AaronsonAmbainis.Bridge
open Finset
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
omit [DecidableEq ι]
namespace AaronsonAmbainis.Bridge
theorem _root_.solution (u : Cube ι) : diffSet u (antipode u) = univ := by
  ext i
  simp [diffSet, antipode]
end AaronsonAmbainis.Bridge
