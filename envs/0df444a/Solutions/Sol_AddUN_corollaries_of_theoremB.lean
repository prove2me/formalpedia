-- Prove2me | solution 1 for AddUN.corollaries_of_theoremB
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T07:38:34.314954+00:00
-- url     : https://prove2.me/submissions/e947755a-59f3-4c7f-be76-3e561301f53d

module
public import Definitions.Def_AddUN_UniversallyNull
public import Definitions.Def_AddUN_Statements
public import Theorems.Thm_AddUN_corollaryA_of_theoremB
public import Theorems.Thm_AddUN_corollaryB_of_corollaryA
public import Theorems.Thm_AddUN_corollaryC_of_theoremB

set_option autoImplicit false
@[expose] public section
public section
open Cardinal MeasureTheory IdealInvariant Filter
open AddUN
namespace AddUN
theorem _root_.solution (hB : TheoremB) (hG : Grzegorek) (hle : GotoCor513) :
    CorollaryA ∧ CorollaryB ∧ CorollaryC :=
  have ha := corollaryA_of_theoremB hB hG
  have hb := corollaryB_of_corollaryA ha hle
  ⟨ha, hb, corollaryC_of_theoremB hB ha hb⟩
end AddUN
