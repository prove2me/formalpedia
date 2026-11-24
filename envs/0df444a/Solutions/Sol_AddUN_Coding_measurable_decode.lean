-- Prove2me | solution 1 for AddUN.Coding.measurable_decode
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T07:38:45.771156+00:00
-- url     : https://prove2.me/submissions/b7bd1d85-b4df-4bf5-b796-e64384554f70

module
public import Definitions.Def_AddUN_SecondMoment
public import Definitions.Def_AddUN_TheoremB
public import Definitions.Def_AddUN_Coding
public import Theorems.Thm_AddUN_Coding_stage_coord
public import Theorems.Thm_AddUN_Coding_isClopen_marker
public import Theorems.Thm_MeasureTheory_Determined_compl
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
theorem _root_.solution (f : ℕ → ℕ) : Measurable (decode f) := by
  refine measurable_pi_lambda _ fun i ↦ measurable_to_bool ?_
  have hset : (fun w ↦ decode f w i) ⁻¹' {true} = ⋃ N : ℕ, ⋂ n : ℕ, ⋂ _ : N ≤ n,
      {w | i < n ∧ w ∈ marker n (f n) → w (coord n (f n) (mu n + i)) = true} := by
    ext w
    simp [decode, eventually_atTop]
  rw [hset]
  refine .iUnion fun N ↦ .iInter fun n ↦ .iInter fun _ ↦ ?_
  by_cases hin : i < n
  · have h : {w : ℕ → Bool | i < n ∧ w ∈ marker n (f n) → w (coord n (f n) (mu n + i)) = true} =
        (marker n (f n))ᶜ ∪ {w | w (coord n (f n) (mu n + i)) = true} := by
      ext w
      simp [hin, imp_iff_not_or]
    rw [h]
    exact (isClopen_marker _ _).isOpen.measurableSet.compl.union
      (measurableSet_eq_fun (measurable_pi_apply _) measurable_const)
  · simp [hin]
end AddUN.Coding
