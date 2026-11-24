-- Prove2me | solution 1 for AddUN.measure_smallClopen_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T07:40:51.212539+00:00
-- url     : https://prove2.me/submissions/4cddc88f-1aaa-4701-81f9-783ba30e2268

module
public import Definitions.Def_AddUN_Localisation
public import Definitions.Def_AddUN_Transfer
public import Definitions.Def_AddUN_Uniformity
public import Mathlib.MeasureTheory.Measure.Prod
public import Definitions.Def_AddUN_Grzegorek
public import Theorems.Thm_MeasureTheory_flip_apply_self
public import Theorems.Thm_MeasureTheory_flip_flip
public import Theorems.Thm_MeasureTheory_length_revPrefix
attribute [local simp] MeasureTheory.flip_apply_self
attribute [local simp] MeasureTheory.flip_flip
attribute [local simp] MeasureTheory.length_revPrefix



set_option autoImplicit false
@[expose] public section
public section
open Set Filter Topology TopologicalSpace Cardinal MeasureTheory IdealInvariant
open scoped ENNReal
open AddUN
namespace AddUN
theorem _root_.solution (n k : ℕ) : cantorMeasure (smallClopen n k) ≤ 2⁻¹ ^ n := by
  unfold smallClopen
  split_ifs with h
  · exact h
  · simp
end AddUN
