-- Prove2me | solution 1 for AddUN.Coding.coord_inj
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T07:24:59.041992+00:00
-- url     : https://prove2.me/submissions/73c62cda-7c39-4ee6-a770-4a434746bc16

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
theorem _root_.solution {n k j n' k' j' : ℕ} :
    coord n k j = coord n' k' j' ↔ n = n' ∧ k = k' ∧ j = j' := by
  simp [coord, Nat.pair_eq_pair, and_assoc]
end AddUN.Coding
