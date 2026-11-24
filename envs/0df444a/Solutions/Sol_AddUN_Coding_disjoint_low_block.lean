-- Prove2me | solution 1 for AddUN.Coding.disjoint_low_block
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T07:37:43.030825+00:00
-- url     : https://prove2.me/submissions/1c250730-e1ad-4398-a2fa-1e4e6d36b890

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
theorem _root_.solution (n k : ℕ) : Disjoint (low n) (block n k : Set ℕ) := by
  rw [Set.disjoint_left]
  intro i hi hb
  obtain ⟨j, -, rfl⟩ := Finset.mem_image.1 (Finset.mem_coe.1 hb)
  simp [low] at hi
end AddUN.Coding
