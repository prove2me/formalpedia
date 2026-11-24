-- Prove2me | solution 1 for AddUN.add_universallyNull_le_non_universallyNull
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T07:35:35.928798+00:00
-- url     : https://prove2.me/submissions/806837e1-b6b4-4ef2-affb-47e51f8e1ede

module
public import Definitions.Def_AddUN_UniversallyNull
public import Definitions.Def_AddUN_Statements
public import Theorems.Thm_IdealInvariant_add_le_non
public import Theorems.Thm_MeasureTheory_not_isUniversallyNull_univ_cantor
public import Theorems.Thm_Set_Countable_isUniversallyNull


set_option autoImplicit false
@[expose] public section
public section
open Cardinal MeasureTheory IdealInvariant Filter
open AddUN
namespace AddUN
theorem _root_.solution : add 𝒰𝒩 ≤ non 𝒰𝒩 :=
  add_le_non (fun x ↦ (Set.countable_singleton x).isUniversallyNull)
    ⟨Set.univ, not_isUniversallyNull_univ_cantor⟩
end AddUN
