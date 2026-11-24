-- Prove2me | solution 1 for AddUN.univ_notMem_null
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T07:22:28.870269+00:00
-- url     : https://prove2.me/submissions/4ec5a988-fc8d-4407-9968-c023f9b3c4d4

module
public import Definitions.Def_AddUN_UniversallyNull
public import Definitions.Def_AddUN_Statements

set_option autoImplicit false
@[expose] public section
public section
open Cardinal MeasureTheory IdealInvariant Filter
open AddUN
namespace AddUN
theorem _root_.solution : Set.univ ∉ 𝒩 := by
  simp
end AddUN
