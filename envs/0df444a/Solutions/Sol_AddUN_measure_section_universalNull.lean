-- Prove2me | solution 1 for AddUN.measure_section_universalNull
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T07:41:59.49738+00:00
-- url     : https://prove2.me/submissions/2699c026-bcd8-4418-acf7-2af724fa4b37

module
public import Definitions.Def_AddUN_Localisation
public import Definitions.Def_AddUN_Transfer
public import Definitions.Def_AddUN_Uniformity
public import Mathlib.MeasureTheory.Measure.Prod
public import Definitions.Def_AddUN_Grzegorek
public import Theorems.Thm_AddUN_measure_smallClopen_le
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
theorem _root_.solution (c : ℕ → ℕ) :
    cantorMeasure {x | (x, c) ∈ universalNull} = 0 := by
  have hsum : ∑' n, cantorMeasure (smallClopen n (c n)) ≠ ⊤ := by
    refine ne_top_of_le_ne_top ?_ (ENNReal.tsum_le_tsum fun n ↦ measure_smallClopen_le n (c n))
    rw [ENNReal.tsum_geometric]
    simp
  refine measure_mono_null (fun x hx ↦ ?_) (measure_limsup_atTop_eq_zero hsum)
  rw [mem_limsup_iff_frequently_mem]
  exact hx
end AddUN
