-- Prove2me | solution 1 for AddUN.add_universallyNull_le_min
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T07:49:23.865725+00:00
-- url     : https://prove2.me/submissions/058d795c-0600-45e4-b986-79259ae208c1

module
public import Definitions.Def_AddUN_Additivity
public import Definitions.Def_AddUN_TheoremA
public import Definitions.Def_AddUN_Main
public import Theorems.Thm_AddUN_add_universallyNull_le_non_null
public import Theorems.Thm_AddUN_theoremA


set_option autoImplicit false
@[expose] public section
public section
open Cardinal MeasureTheory IdealInvariant
open AddUN
namespace AddUN
theorem _root_.solution : add 𝒰𝒩 ≤ min dominatingNumber (non 𝒩) :=
  le_min theoremA add_universallyNull_le_non_null
end AddUN
