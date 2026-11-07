-- Prove2me | solution 1 for AaronsonAmbainis.DetLow.lowestUnit
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T22:58:29.931707+00:00
-- url     : https://prove2.me/submissions/a07b189c-1ac3-4874-9962-582ee77e828a

import Definitions.Def_AaronsonAmbainis_DetLow_Unit
import Definitions.Def_AaronsonAmbainis_DetLow_NonZero
import Definitions.Def_AaronsonAmbainis_DetLow_RowOps
import Definitions.Def_AaronsonAmbainis_DetLow_Degree
import Definitions.Def_AaronsonAmbainis_DetLow_Count
import Definitions.Def_AaronsonAmbainis_DetLow_Main
import Theorems.Thm_AaronsonAmbainis_DetLow_isLowest_of_unit_mul
import Theorems.Thm_AaronsonAmbainis_DetLow_isLowest_unit_mul


set_option autoImplicit true
open AaronsonAmbainis
open AaronsonAmbainis.DetLow
open Finset MvPolynomial
namespace AaronsonAmbainis.DetLow
theorem _root_.solution : AaronsonAmbainis.LowestUnit := by
  intro ι _ u q hu m
  exact ⟨isLowest_of_unit_mul u q hu m, isLowest_unit_mul u q hu m⟩
end AaronsonAmbainis.DetLow
