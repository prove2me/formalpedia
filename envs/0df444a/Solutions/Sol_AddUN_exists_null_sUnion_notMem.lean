-- Prove2me | solution 1 for AddUN.exists_null_sUnion_notMem
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T07:36:57.532519+00:00
-- url     : https://prove2.me/submissions/2f6c0176-32bb-460b-a16b-b286adac6278

module
public import Definitions.Def_AddUN_CantorMeasure
public import Definitions.Def_AddUN_Statements
public import Mathlib.MeasureTheory.OuterMeasure.BorelCantelli
public import Mathlib.Topology.Separation.Profinite
public import Definitions.Def_AddUN_Localisation
public import Theorems.Thm_MeasureTheory_Determined_univ
public import Theorems.Thm_MeasureTheory_flip_apply_self
public import Theorems.Thm_MeasureTheory_flip_flip
attribute [local simp] MeasureTheory.flip_apply_self
attribute [local simp] MeasureTheory.flip_flip



set_option autoImplicit false
@[expose] public section
public section
open Set Filter Topology TopologicalSpace Cardinal MeasureTheory IdealInvariant
open scoped ENNReal
open AddUN
namespace AddUN
theorem _root_.solution : ∃ 𝒜 ⊆ 𝒩, ⋃₀ 𝒜 ∉ 𝒩 := by
  refine ⟨range fun x ↦ ({x} : Set (ℕ → Bool)), ?_, ?_⟩
  · rintro _ ⟨x, rfl⟩
    exact measure_singleton x
  · have h : ⋃₀ (range fun x ↦ ({x} : Set (ℕ → Bool))) = Set.univ := by
      ext
      simp
    simp [h]
end AddUN
