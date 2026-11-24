-- Prove2me | solution 1 for AddUN.corollaries_of_cited
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T07:45:45.39833+00:00
-- url     : https://prove2.me/submissions/50dbe78f-5558-415f-803a-c7ee87f29eff

module
public import Definitions.Def_AddUN_Additivity
public import Definitions.Def_AddUN_TheoremA
public import Definitions.Def_AddUN_Main
public import Theorems.Thm_AddUN_theoremB_of_gotoCor513
public import Theorems.Thm_AddUN_corollaries_of_theoremB


set_option autoImplicit false
@[expose] public section
public section
open Cardinal MeasureTheory IdealInvariant
open AddUN
namespace AddUN
theorem _root_.solution (hG : Grzegorek) (hle : GotoCor513) :
    CorollaryA ∧ CorollaryB ∧ CorollaryC :=
  corollaries_of_theoremB (theoremB_of_gotoCor513 hle) hG hle
end AddUN
