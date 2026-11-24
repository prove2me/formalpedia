-- Prove2me | solution 1 for AddUN.isUniversallyNull_of_mk_lt_non
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T07:45:16.135739+00:00
-- url     : https://prove2.me/submissions/01b97c2f-0027-4432-a1b3-cecf38c1b08f

module
public import Definitions.Def_AddUN_InitialCylinder
public import Definitions.Def_AddUN_Statements
public import Mathlib.MeasureTheory.Constructions.Polish.EmbeddingReal
public import Definitions.Def_AddUN_Uniformity
public import Theorems.Thm_MeasureTheory_measurable_split
public import Theorems.Thm_MeasureTheory_map_split
public import Theorems.Thm_IdealInvariant_mem_of_lt_non


set_option autoImplicit false
@[expose] public section
public section
open Set Filter Topology Cardinal MeasureTheory IdealInvariant
open scoped ENNReal
open AddUN
namespace AddUN
theorem _root_.solution {A : Set (ℕ → Bool)} (hA : #A < non 𝒩) :
    IsUniversallyNull A := by
  intro μ _ _
  have hnull : cantorMeasure (split μ '' A) = 0 := mem_of_lt_non (mk_image_le.trans_lt hA)
  have h1 : μ.map (split μ) (toMeasurable cantorMeasure (split μ '' A)) = 0 := by
    rw [map_split, Measure.smul_apply, measure_toMeasurable, hnull, smul_zero]
  rw [Measure.map_apply (measurable_split μ) (measurableSet_toMeasurable _ _)] at h1
  exact measure_mono_null (show A ⊆ split μ ⁻¹' toMeasurable cantorMeasure (split μ '' A) from
    fun x hx ↦ subset_toMeasurable _ _ (mem_image_of_mem _ hx)) h1
end AddUN
