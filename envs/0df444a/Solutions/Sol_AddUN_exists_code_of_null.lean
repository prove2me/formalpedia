-- Prove2me | solution 1 for AddUN.exists_code_of_null
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T07:41:12.874453+00:00
-- url     : https://prove2.me/submissions/f12958da-113b-41ed-b71e-1a719f0d62ea

module
public import Definitions.Def_AddUN_Localisation
public import Definitions.Def_AddUN_Transfer
public import Definitions.Def_AddUN_Uniformity
public import Mathlib.MeasureTheory.Measure.Prod
public import Definitions.Def_AddUN_Grzegorek
public import Theorems.Thm_AddUN_clopenEnum_surjective
public import Theorems.Thm_AddUN_exists_clopens_limsup
public import Theorems.Thm_MeasureTheory_Determined_mono
public import Theorems.Thm_MeasureTheory_IsUniversallyNull_mono
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
theorem _root_.solution {G : Set (ℕ → Bool)} (hG : cantorMeasure G = 0) :
    ∃ c : ℕ → ℕ, ∀ x ∈ G, (x, c) ∈ universalNull := by
  obtain ⟨C, hC, hGC⟩ := exists_clopens_limsup cantorMeasure hG (ε := fun n ↦ 2⁻¹ ^ n)
    (fun n ↦ by simp)
  refine ⟨fun n ↦ Function.surjInv clopenEnum_surjective (C n), fun x hx ↦
    (hGC x hx).mono fun n hn ↦ ?_⟩
  have h : clopenEnum (Function.surjInv clopenEnum_surjective (C n)) = C n :=
    Function.surjInv_eq _ _
  simp only [smallClopen]
  rw [h, if_pos (hC n)]
  exact hn
end AddUN
