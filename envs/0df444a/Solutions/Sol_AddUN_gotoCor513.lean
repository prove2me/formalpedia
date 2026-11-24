-- Prove2me | solution 1 for AddUN.gotoCor513
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T07:45:48.062096+00:00
-- url     : https://prove2.me/submissions/9741c3a9-1fe8-4db2-930a-16de6e6c4602

module
public import Definitions.Def_AddUN_Coding
public import Definitions.Def_AddUN_Additivity
public import Theorems.Thm_AddUN_isUniversallyNull_sUnion_of_mk_lt_add
public import Theorems.Thm_AddUN_Coding_stage_coord
public import Theorems.Thm_MeasureTheory_Determined_univ
public import Theorems.Thm_MeasureTheory_flip_apply_self
public import Theorems.Thm_MeasureTheory_flip_flip
public import Theorems.Thm_MeasureTheory_not_isUniversallyNull_univ_cantor
public import Theorems.Thm_Set_Countable_isUniversallyNull
attribute [local simp] AddUN.Coding.stage_coord
attribute [local simp] MeasureTheory.flip_apply_self
attribute [local simp] MeasureTheory.flip_flip



set_option autoImplicit false
@[expose] public section
public section
open Set Filter Cardinal MeasureTheory IdealInvariant
open AddUN
open Coding
namespace AddUN
theorem _root_.solution : GotoCor513 := by
  have hne : Nonempty {𝒜 : Set (Set (ℕ → Bool)) // 𝒜 ⊆ 𝒰𝒩 ∧ ⋃₀ 𝒜 ∉ 𝒰𝒩} := by
    refine ⟨⟨range fun x ↦ ({x} : Set (ℕ → Bool)), ?_, ?_⟩⟩
    · rintro _ ⟨x, rfl⟩
      exact (countable_singleton x).isUniversallyNull
    · have h : ⋃₀ (range fun x ↦ ({x} : Set (ℕ → Bool))) = Set.univ := by
        ext
        simp
      rw [h]
      exact not_isUniversallyNull_univ_cantor
  refine le_ciInf fun 𝒜 ↦ not_lt.1 fun hlt ↦ ?_
  exact 𝒜.2.2 (isUniversallyNull_sUnion_of_mk_lt_add (fun A hA ↦ 𝒜.2.1 hA) hlt)
end AddUN
