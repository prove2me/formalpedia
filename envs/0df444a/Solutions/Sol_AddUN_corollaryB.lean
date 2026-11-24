-- Prove2me | solution 1 for AddUN.corollaryB
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T07:48:06.69859+00:00
-- url     : https://prove2.me/submissions/3d2f6716-d0df-4aba-9896-4b9fb801d5fc

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
theorem _root_.solution : CorollaryB := (corollaries_of_cited grzegorek gotoCor513).2.1
end AddUN
