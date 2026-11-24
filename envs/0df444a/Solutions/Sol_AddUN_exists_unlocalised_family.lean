-- Prove2me | solution 1 for AddUN.exists_unlocalised_family
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T07:39:49.107898+00:00
-- url     : https://prove2.me/submissions/a8950717-7d39-42eb-ad24-30f3b8a18874

module
public import Definitions.Def_AddUN_CantorMeasure
public import Definitions.Def_AddUN_Statements
public import Mathlib.MeasureTheory.OuterMeasure.BorelCantelli
public import Mathlib.Topology.Separation.Profinite
public import Definitions.Def_AddUN_Localisation
public import Theorems.Thm_IdealInvariant_exists_sUnion_notMem_mk_eq_add
public import Theorems.Thm_AddUN_exists_null_sUnion_notMem
public import Theorems.Thm_AddUN_measure_sUnion_null_of_localised

set_option autoImplicit false
@[expose] public section
public section
open Set Filter Topology TopologicalSpace Cardinal MeasureTheory IdealInvariant
open scoped ENNReal
open AddUN
namespace AddUN
theorem _root_.solution (h : ℕ → ℕ) :
    ∃ F : Set (ℕ → ℕ), #F ≤ add 𝒩 ∧
      ∀ S : ℕ → Finset ℕ, (∀ n, (S n).card ≤ h n) → ∃ f ∈ F, ∃ᶠ n in atTop, f n ∉ S n := by
  obtain ⟨𝒢, h𝒢, hU, hcard⟩ := exists_sUnion_notMem_mk_eq_add exists_null_sUnion_notMem
  by_contra hcon
  refine hU (measure_sUnion_null_of_localised cantorMeasure h (fun G hG ↦ h𝒢 hG) fun F hF ↦ ?_)
  by_contra hno
  refine hcon ⟨F, hcard ▸ hF, fun S hS ↦ ?_⟩
  by_contra hf
  exact hno ⟨S, hS, fun f hfF ↦ by_contra fun hev ↦ hf ⟨f, hfF, not_eventually.1 hev⟩⟩
end AddUN
