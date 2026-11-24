-- Prove2me | solution 1 for AddUN.Coding.real_marker
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T07:39:25.925636+00:00
-- url     : https://prove2.me/submissions/e02e80d3-d9d5-4da4-858b-96fd22560e4f

module
public import Definitions.Def_AddUN_SecondMoment
public import Definitions.Def_AddUN_TheoremB
public import Definitions.Def_AddUN_Coding
public import Theorems.Thm_AddUN_Coding_card_markerBlock
public import Theorems.Thm_MeasureTheory_cantorMeasure_real_cylinderOn


set_option autoImplicit false
@[expose] public section
public section
open Set Filter MeasureTheory
open AddUN
open AddUN.Coding
namespace AddUN.Coding
theorem _root_.solution (n k : ℕ) : cantorMeasure.real (marker n k) = (1 / 2) ^ mu n := by
  rw [marker, cantorMeasure_real_cylinderOn, card_markerBlock]
end AddUN.Coding
