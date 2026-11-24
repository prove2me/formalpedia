-- Prove2me | solution 1 for AddUN.Coding.pattern_coord_add
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T07:37:58.807813+00:00
-- url     : https://prove2.me/submissions/6d7b4c0b-440b-47e4-b2ed-6d498a913c93

module
public import Definitions.Def_AddUN_SecondMoment
public import Definitions.Def_AddUN_TheoremB
public import Definitions.Def_AddUN_Coding
public import Theorems.Thm_AddUN_Coding_stage_coord
public import Theorems.Thm_MeasureTheory_flip_apply_self
public import Theorems.Thm_MeasureTheory_flip_flip
attribute [local simp] MeasureTheory.flip_apply_self
attribute [local simp] MeasureTheory.flip_flip


attribute [local simp] AddUN.Coding.stage_coord

set_option autoImplicit false
@[expose] public section
public section
open Set Filter MeasureTheory
open AddUN
open AddUN.Coding
namespace AddUN.Coding
theorem _root_.solution (c : ℕ → Bool) (n k i : ℕ) : pattern c (coord n k (mu n + i)) = c i := by
  simp [pattern, coord, stage]
end AddUN.Coding
