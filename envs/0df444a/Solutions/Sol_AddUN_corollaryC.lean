-- Prove2me | solution 1 for AddUN.corollaryC
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T07:48:07.635864+00:00
-- url     : https://prove2.me/submissions/923d7529-86d1-42ea-b98d-d07b2b1fc267

module
public import Definitions.Def_AddUN_Additivity
public import Definitions.Def_AddUN_TheoremA
public import Definitions.Def_AddUN_Main
public import Theorems.Thm_AddUN_corollaries_of_cited
public import Theorems.Thm_AddUN_gotoCor513
public import Theorems.Thm_AddUN_grzegorek


set_option autoImplicit false
@[expose] public section
public section
open Cardinal MeasureTheory IdealInvariant
open AddUN
namespace AddUN
theorem _root_.solution : CorollaryC := (corollaries_of_cited grzegorek gotoCor513).2.2
end AddUN
