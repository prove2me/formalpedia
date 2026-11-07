-- Prove2me | solution 1 for AaronsonAmbainis.Bridge.hasDegreeLE_iff_01
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T23:23:25.083584+00:00
-- url     : https://prove2.me/submissions/2c1c8329-d0c9-46ba-9af6-9fbc12bdab51

import Definitions.Def_AaronsonAmbainis_Bridge_Basic
import Definitions.Def_AaronsonAmbainis_Bridge_ZeroOne
import Theorems.Thm_AaronsonAmbainis_Bridge_hasDegreeLE_iff_hasDegLE
import Theorems.Thm_AaronsonAmbainis_Bridge_hasDegreeLE01_iff_hasDegLE
import Theorems.Thm_AaronsonAmbainis_Bridge_hasDegLE_of_affine

set_option autoImplicit true
open AaronsonAmbainis AaronsonAmbainis.Bridge
open Finset
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
namespace AaronsonAmbainis.Bridge
theorem _root_.solution {f : Cube ι → ℝ} {d : ℕ} : HasDegreeLE f d ↔ HasDegreeLE01 f d := by
  rw [hasDegreeLE_iff_hasDegLE, hasDegreeLE01_iff_hasDegLE]
  constructor
  · -- `(-1)^b = (-2) * b + 1`
    exact hasDegLE_of_affine (α := 1) (β := -2) (fun b => by cases b <;> norm_num)
  · -- `b = (-1/2) * (-1)^b + 1/2`
    exact hasDegLE_of_affine (α := 1 / 2) (β := -1 / 2) (fun b => by cases b <;> norm_num)
end AaronsonAmbainis.Bridge
