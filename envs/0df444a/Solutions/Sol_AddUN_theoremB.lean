-- Prove2me | solution 1 for AddUN.theoremB
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T07:46:34.324786+00:00
-- url     : https://prove2.me/submissions/1b0d4bb6-1c2c-425c-81c9-ca852157131b

module
public import Definitions.Def_AddUN_Additivity
public import Definitions.Def_AddUN_TheoremA
public import Definitions.Def_AddUN_Main
public import Theorems.Thm_AddUN_theoremB_of_gotoCor513
public import Theorems.Thm_AddUN_gotoCor513


set_option autoImplicit false
@[expose] public section
public section
open Cardinal MeasureTheory IdealInvariant
open AddUN
namespace AddUN
theorem _root_.solution : TheoremB := theoremB_of_gotoCor513 gotoCor513
end AddUN
