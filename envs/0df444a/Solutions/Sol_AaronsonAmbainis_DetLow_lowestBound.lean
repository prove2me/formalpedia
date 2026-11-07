-- Prove2me | solution 1 for AaronsonAmbainis.DetLow.lowestBound
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T23:20:01.338909+00:00
-- url     : https://prove2.me/submissions/d0e40943-81ed-4862-8313-7a376acef636

import Definitions.Def_AaronsonAmbainis_DetLow_Unit
import Definitions.Def_AaronsonAmbainis_DetLow_NonZero
import Definitions.Def_AaronsonAmbainis_DetLow_RowOps
import Definitions.Def_AaronsonAmbainis_DetLow_Degree
import Definitions.Def_AaronsonAmbainis_DetLow_Count
import Definitions.Def_AaronsonAmbainis_DetLow_Main
import Theorems.Thm_AaronsonAmbainis_DetLow_degreeOf_cofactor_le
import Theorems.Thm_AaronsonAmbainis_DetLow_agMatrix_det_ne_zero
import Theorems.Thm_AaronsonAmbainis_DetLow_det_factor
import Theorems.Thm_AaronsonAmbainis_DetLow_flipSet_flipSet_singleton
import Theorems.Thm_AaronsonAmbainis_DetLow_flipSet_singleton_self
import Theorems.Thm_AaronsonAmbainis_DetLow_isLowest_of_unit_mul
attribute [local simp] AaronsonAmbainis.DetLow.flipSet_flipSet_singleton
attribute [local simp] AaronsonAmbainis.DetLow.flipSet_singleton_self



set_option autoImplicit true
open AaronsonAmbainis
open AaronsonAmbainis.DetLow
open Finset MvPolynomial
namespace AaronsonAmbainis.DetLow
theorem _root_.solution : AaronsonAmbainis.LowestBound := by
  intro ι _ _ g
  refine ⟨agMatrix_det_ne_zero g, ?_⟩
  intro m hm j
  obtain ⟨R, hR⟩ := det_factor g j
  have hu : constantCoeff ((1 - X j ^ 2 : MvPolynomial ι ℤ) ^ (Up g j).card) = 1 := by
    simp
  rw [hR] at hm
  have hlow : IsLowest R m := isLowest_of_unit_mul _ R hu m hm
  exact (monomial_le_degreeOf j hlow.1).trans (degreeOf_cofactor_le g j R hR)
end AaronsonAmbainis.DetLow
