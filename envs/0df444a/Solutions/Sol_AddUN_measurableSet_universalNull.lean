-- Prove2me | solution 1 for AddUN.measurableSet_universalNull
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T07:41:56.677869+00:00
-- url     : https://prove2.me/submissions/b74d4289-732b-4333-9f21-3a611d478153

module
public import Definitions.Def_AddUN_Localisation
public import Definitions.Def_AddUN_Transfer
public import Definitions.Def_AddUN_Uniformity
public import Mathlib.MeasureTheory.Measure.Prod
public import Definitions.Def_AddUN_Grzegorek
public import Theorems.Thm_AddUN_measurableSet_smallClopen
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
theorem _root_.solution : MeasurableSet universalNull := by
  have h : universalNull = ⋂ N : ℕ, ⋃ n : ℕ, ⋃ (_ : N ≤ n), ⋃ k : ℕ,
      smallClopen n k ×ˢ {c : ℕ → ℕ | c n = k} := by
    ext p
    simp only [universalNull, mem_ofPred_eq, frequently_atTop, mem_iInter, mem_iUnion, mem_prod,
      exists_prop]
    constructor
    · intro h N
      obtain ⟨n, hn, hp⟩ := h N
      exact ⟨n, hn, p.2 n, hp, rfl⟩
    · intro h N
      obtain ⟨n, hn, k, hp, hk⟩ := h N
      exact ⟨n, hn, by rwa [hk]⟩
  rw [h]
  exact .iInter fun N ↦ .iUnion fun n ↦ .iUnion fun _ ↦ .iUnion fun k ↦
    (measurableSet_smallClopen n k).prod
      (measurableSet_eq_fun (measurable_pi_apply n) measurable_const)
end AddUN
