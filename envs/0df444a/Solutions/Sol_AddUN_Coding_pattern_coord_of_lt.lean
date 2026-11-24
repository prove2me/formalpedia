-- Prove2me | solution 1 for AddUN.Coding.pattern_coord_of_lt
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T07:37:55.270097+00:00
-- url     : https://prove2.me/submissions/9d2cc1a2-c12e-46bc-8049-6d75f04df6f7

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
theorem _root_.solution (c : ℕ → Bool) {n j : ℕ} (k : ℕ) (h : j < mu n) :
    pattern c (coord n k j) = false := by
  simp [pattern, coord, stage, h]
end AddUN.Coding
