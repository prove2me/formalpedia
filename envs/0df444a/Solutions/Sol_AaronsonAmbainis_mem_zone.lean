-- Prove2me | solution 1 for AaronsonAmbainis.mem_zone
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T22:24:07.038089+00:00
-- url     : https://prove2.me/submissions/97e4ff74-ffe2-42cb-92f3-96f5c0ff393c

import Definitions.Def_AaronsonAmbainis_AllPairsDefs
import Definitions.Def_AaronsonAmbainis_TwoSided_Basic

set_option autoImplicit true
open AaronsonAmbainis
open Finset
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
namespace AaronsonAmbainis
theorem _root_.solution {g : Cube ι → Bool} {u : Cube ι} :
    u ∈ zone g ↔ g u = true ∧ g (antipode u) = false := by
  simp [zone]
end AaronsonAmbainis
