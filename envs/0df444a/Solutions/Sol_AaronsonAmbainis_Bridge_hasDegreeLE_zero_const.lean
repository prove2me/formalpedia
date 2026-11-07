-- Prove2me | solution 1 for AaronsonAmbainis.Bridge.hasDegreeLE_zero_const
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T22:51:43.830308+00:00
-- url     : https://prove2.me/submissions/f653d13f-fce9-4553-900f-eb63ca181d55

import Definitions.Def_AaronsonAmbainis_Statements
import Definitions.Def_AaronsonAmbainis_Bridge_Basic
import Theorems.Thm_AaronsonAmbainis_Bridge_hasDegreeLE_zero_iff

set_option autoImplicit true
open AaronsonAmbainis AaronsonAmbainis.Bridge
open Finset
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
namespace AaronsonAmbainis.Bridge
theorem _root_.solution {f : Cube ι → ℝ} (h : HasDegreeLE f 0) (x y : Cube ι) :
    f x = f y := by
  obtain ⟨a, ha⟩ := hasDegreeLE_zero_iff.mp h
  rw [ha x, ha y]
end AaronsonAmbainis.Bridge
