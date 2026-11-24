-- Prove2me | solution 1 for AddUN.Coding.block_subset_low
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T07:30:08.927357+00:00
-- url     : https://prove2.me/submissions/0c85d61b-0dc3-4bf1-ae8f-9d5d7aa135e1

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
theorem _root_.solution (n k : ℕ) : (block n k : Set ℕ) ⊆ low (n + 1) := by
  intro i hi
  obtain ⟨j, -, rfl⟩ := Finset.mem_image.1 (Finset.mem_coe.1 hi)
  simp [low]
end AddUN.Coding
