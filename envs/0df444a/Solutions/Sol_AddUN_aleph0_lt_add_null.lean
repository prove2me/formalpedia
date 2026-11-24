-- Prove2me | solution 1 for AddUN.aleph0_lt_add_null
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T07:35:25.202831+00:00
-- url     : https://prove2.me/submissions/f51e68ae-d79f-4cee-a57d-0d6af6449850

module
public import Definitions.Def_AddUN_UniversallyNull
public import Definitions.Def_AddUN_Statements
public import Theorems.Thm_MeasureTheory_aleph0_lt_add_nullSets


set_option autoImplicit false
@[expose] public section
public section
open Cardinal MeasureTheory IdealInvariant Filter
open AddUN
namespace AddUN
theorem _root_.solution : ℵ₀ < add 𝒩 :=
  aleph0_lt_add_nullSets cantorMeasure
end AddUN
