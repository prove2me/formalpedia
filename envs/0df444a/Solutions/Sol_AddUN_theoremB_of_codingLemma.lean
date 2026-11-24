-- Prove2me | solution 1 for AddUN.theoremB_of_codingLemma
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T07:41:45.123493+00:00
-- url     : https://prove2.me/submissions/79e34adf-3cf3-4456-acef-f3c4e63a0589

module
public import Definitions.Def_AddUN_Localisation
public import Definitions.Def_AddUN_Transfer
public import Definitions.Def_AddUN_TheoremB
public import Theorems.Thm_AddUN_add_universallyNull_le_add_null_of_codingLemma

set_option autoImplicit false
@[expose] public section
public section
open Set Filter Cardinal MeasureTheory IdealInvariant
open AddUN
namespace AddUN
theorem _root_.solution (hC : CodingLemma) (hle : GotoCor513) : TheoremB :=
  fun A hA hcard ↦
    le_antisymm (add_universallyNull_le_add_null_of_codingLemma hC A hA hcard) hle
end AddUN
