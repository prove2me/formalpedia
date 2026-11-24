-- Prove2me | solution 1 for AddUN.exists_clopens_iUnion_eq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T07:36:32.328365+00:00
-- url     : https://prove2.me/submissions/831b7a3c-ed26-4227-9753-8c99fde07a40

module
public import Definitions.Def_AddUN_CantorMeasure
public import Definitions.Def_AddUN_Statements
public import Mathlib.MeasureTheory.OuterMeasure.BorelCantelli
public import Mathlib.Topology.Separation.Profinite
public import Definitions.Def_AddUN_Localisation
public import Theorems.Thm_MeasureTheory_Determined_diff
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
theorem _root_.solution (μ : Measure (ℕ → Bool)) {U : Set (ℕ → Bool)} (hU : IsOpen U) :
    ∃ D : ℕ → Clopens (ℕ → Bool), ⋃ r, (D r : Set (ℕ → Bool)) = U ∧ ∑' r, μ (D r) = μ U := by
  obtain ⟨O, hO⟩ := exists_surjective_nat (Clopens (ℕ → Bool))
  classical
  let V : ℕ → Set (ℕ → Bool) := fun r ↦ if (O r : Set (ℕ → Bool)) ⊆ U then O r else ∅
  have hVc : ∀ r, IsClopen (V r) := fun r ↦ by
    by_cases h : (O r : Set (ℕ → Bool)) ⊆ U
    · simpa [V, h] using (O r).isClopen
    · simpa [V, h] using isClopen_empty
  have hVU : ⋃ r, V r = U := by
    apply Subset.antisymm
    · refine iUnion_subset fun r ↦ ?_
      by_cases h : (O r : Set (ℕ → Bool)) ⊆ U <;> simp [V, h]
    · intro x hx
      obtain ⟨s, hs, hxs, hsU⟩ := isTopologicalBasis_isClopen.exists_subset_of_mem_open hx hU
      obtain ⟨r, hr⟩ := hO ⟨s, hs⟩
      have hrs : (O r : Set (ℕ → Bool)) = s := by rw [hr]; rfl
      exact mem_iUnion.2 ⟨r, by simp [V, hrs, hsU, hxs]⟩
  have hDc : ∀ r, IsClopen (disjointed V r) := fun r ↦
    disjointedRec (fun t i ht ↦ ht.diff (hVc i)) (hVc r)
  refine ⟨fun r ↦ ⟨disjointed V r, hDc r⟩, by simpa [iUnion_disjointed] using hVU, ?_⟩
  simp only [Clopens.coe_mk]
  rw [← measure_iUnion (disjoint_disjointed V) fun r ↦ (hDc r).isOpen.measurableSet,
    iUnion_disjointed, hVU]
end AddUN
