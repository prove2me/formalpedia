-- Prove2me | solution 1 for AaronsonAmbainis.Bridge.flipSet_diffSet
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T23:16:00.940445+00:00
-- url     : https://prove2.me/submissions/67a9fb2a-53b6-4098-b829-7b8b0c6ef597

import Definitions.Def_AaronsonAmbainis_Statements
import Definitions.Def_AaronsonAmbainis_Bridge_Basic

set_option autoImplicit true
open AaronsonAmbainis AaronsonAmbainis.Bridge
open Finset
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
namespace AaronsonAmbainis.Bridge
theorem _root_.solution (x y : Cube ι) : flipSet x (diffSet x y) = y := by
  funext i
  by_cases h : x i = y i
  · simp [flipSet, diffSet, h]
  · have h' : (!(x i)) = y i := by
      cases hx : x i <;> cases hy : y i <;> simp_all
    simp [flipSet, diffSet, h, h']
end AaronsonAmbainis.Bridge
