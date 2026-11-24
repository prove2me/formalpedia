-- Prove2me | solution 1 for AddUN.corollaryA
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T07:48:05.849341+00:00
-- url     : https://prove2.me/submissions/328090f0-d3c5-4fa3-ae27-2a978770857e

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
theorem _root_.solution : CorollaryA := (corollaries_of_cited grzegorek gotoCor513).1
end AddUN
