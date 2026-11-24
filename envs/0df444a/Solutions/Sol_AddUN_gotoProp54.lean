-- Prove2me | solution 1 for AddUN.gotoProp54
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T07:46:01.817469+00:00
-- url     : https://prove2.me/submissions/e31111b3-8575-43f8-97a4-875ee1612399

module
public import Definitions.Def_AddUN_InitialCylinder
public import Definitions.Def_AddUN_Statements
public import Mathlib.MeasureTheory.Constructions.Polish.EmbeddingReal
public import Definitions.Def_AddUN_Uniformity
public import Theorems.Thm_AddUN_isUniversallyNull_of_mk_lt_non
public import Theorems.Thm_AddUN_non_universallyNull_le_non_null
public import Theorems.Thm_MeasureTheory_Determined_univ
public import Theorems.Thm_MeasureTheory_not_isUniversallyNull_univ_cantor


set_option autoImplicit false
@[expose] public section
public section
open Set Filter Topology Cardinal MeasureTheory IdealInvariant
open scoped ENNReal
open AddUN
namespace AddUN
theorem _root_.solution : GotoProp54 := by
  have hne : Nonempty {A : Set (ℕ → Bool) // A ∉ 𝒰𝒩} := ⟨⟨univ, not_isUniversallyNull_univ_cantor⟩⟩
  exact le_antisymm non_universallyNull_le_non_null
    (le_ciInf fun A ↦ not_lt.1 fun hlt ↦ A.2 (isUniversallyNull_of_mk_lt_non hlt))
end AddUN
