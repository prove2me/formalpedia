-- Prove2me | solution 1 for AddUN.non_universallyNull_le_non_null
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T07:36:00.833545+00:00
-- url     : https://prove2.me/submissions/c2d615e8-f547-415d-8fb9-5472c5cf7f18

module
public import Definitions.Def_AddUN_UniversallyNull
public import Definitions.Def_AddUN_Statements
public import Theorems.Thm_AddUN_universallyNull_subset_null
public import Theorems.Thm_AddUN_univ_notMem_null
public import Theorems.Thm_IdealInvariant_non_le_non


set_option autoImplicit false
@[expose] public section
public section
open Cardinal MeasureTheory IdealInvariant Filter
open AddUN
namespace AddUN
theorem _root_.solution : non 𝒰𝒩 ≤ non 𝒩 :=
  non_le_non universallyNull_subset_null ⟨Set.univ, univ_notMem_null⟩
end AddUN
