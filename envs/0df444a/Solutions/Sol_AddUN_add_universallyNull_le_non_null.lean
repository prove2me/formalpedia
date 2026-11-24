-- Prove2me | solution 1 for AddUN.add_universallyNull_le_non_null
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T07:37:09.63616+00:00
-- url     : https://prove2.me/submissions/803a56fa-3f10-454c-ae75-43c881d344d0

module
public import Definitions.Def_AddUN_UniversallyNull
public import Definitions.Def_AddUN_Statements
public import Theorems.Thm_AddUN_add_universallyNull_le_non_universallyNull
public import Theorems.Thm_AddUN_non_universallyNull_le_non_null

set_option autoImplicit false
@[expose] public section
public section
open Cardinal MeasureTheory IdealInvariant Filter
open AddUN
namespace AddUN
theorem _root_.solution : add 𝒰𝒩 ≤ non 𝒩 :=
  add_universallyNull_le_non_universallyNull.trans non_universallyNull_le_non_null
end AddUN
