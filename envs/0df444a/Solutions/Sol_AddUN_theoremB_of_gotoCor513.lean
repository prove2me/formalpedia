-- Prove2me | solution 1 for AddUN.theoremB_of_gotoCor513
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T07:44:26.742487+00:00
-- url     : https://prove2.me/submissions/176090a2-ef81-43e9-8e08-2bfc871029fb

module
public import Definitions.Def_AddUN_Additivity
public import Definitions.Def_AddUN_TheoremA
public import Definitions.Def_AddUN_Main
public import Theorems.Thm_AddUN_codingLemma
public import Theorems.Thm_AddUN_theoremB_of_codingLemma


set_option autoImplicit false
@[expose] public section
public section
open Cardinal MeasureTheory IdealInvariant
open AddUN
namespace AddUN
theorem _root_.solution (hle : GotoCor513) : TheoremB :=
  theoremB_of_codingLemma codingLemma hle
end AddUN
