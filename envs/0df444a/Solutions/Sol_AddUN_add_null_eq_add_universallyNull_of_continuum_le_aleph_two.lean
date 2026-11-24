-- Prove2me | solution 1 for AddUN.add_null_eq_add_universallyNull_of_continuum_le_aleph_two
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T07:48:08.1567+00:00
-- url     : https://prove2.me/submissions/fd296389-fbb3-4893-97c2-61e9031a9f69

module
public import Definitions.Def_AddUN_Additivity
public import Definitions.Def_AddUN_TheoremA
public import Definitions.Def_AddUN_Main
public import Theorems.Thm_AddUN_theoremB
public import Theorems.Thm_AddUN_gotoCor513
public import Theorems.Thm_AddUN_grzegorek
public import Theorems.Thm_AddUN_question63_of_continuum_le_aleph_two


set_option autoImplicit false
@[expose] public section
public section
open Cardinal MeasureTheory IdealInvariant
open AddUN
namespace AddUN
theorem _root_.solution
    (h : (𝔠 : Cardinal.{0}) ≤ ℵ_ 2) : add 𝒩 = add 𝒰𝒩 :=
  question63_of_continuum_le_aleph_two theoremB grzegorek gotoCor513 h
end AddUN
