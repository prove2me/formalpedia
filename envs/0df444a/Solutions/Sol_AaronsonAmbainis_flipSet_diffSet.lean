-- Prove2me | solution 1 for AaronsonAmbainis.flipSet_diffSet
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T22:23:36.37296+00:00
-- url     : https://prove2.me/submissions/93a8c3e0-0c24-4d29-b92e-e8af552ed020

import Definitions.Def_AaronsonAmbainis_AllPairsDefs
import Definitions.Def_AaronsonAmbainis_TwoSided_Basic

set_option autoImplicit true
open AaronsonAmbainis
open Finset
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
namespace AaronsonAmbainis
theorem _root_.solution (x y : Cube ι) : flipSet x (diffSet x y) = y := by
  funext i
  by_cases h : x i = y i
  · simp [flipSet, diffSet, h]
  · have h' : (!(x i)) = y i := by
      cases hx : x i <;> cases hy : y i <;> simp_all
    simp [flipSet, diffSet, h, h']
end AaronsonAmbainis
