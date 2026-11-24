-- Prove2me | solution 1 for AddUN.Coding.stage_coord
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T07:24:02.249084+00:00
-- url     : https://prove2.me/submissions/47924229-a4bc-458c-8a7f-3df01d961ffc

module
public import Definitions.Def_AddUN_SecondMoment
public import Definitions.Def_AddUN_TheoremB
public import Definitions.Def_AddUN_Coding
public import Theorems.Thm_MeasureTheory_flip_apply_self
public import Theorems.Thm_MeasureTheory_flip_flip
attribute [local simp] MeasureTheory.flip_apply_self
attribute [local simp] MeasureTheory.flip_flip



set_option autoImplicit false
@[expose] public section
public section
open Set Filter MeasureTheory
open AddUN
open AddUN.Coding
namespace AddUN.Coding
theorem _root_.solution (n k j : ℕ) : stage (coord n k j) = n := by simp [stage, coord]
end AddUN.Coding
