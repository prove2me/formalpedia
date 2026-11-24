-- Prove2me | solution 1 for AddUN.theoremA
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T07:48:04.455828+00:00
-- url     : https://prove2.me/submissions/3d433583-f514-4d23-9216-aa2d3d1b6766

module
public import Definitions.Def_AddUN_Grzegorek
public import Definitions.Def_AddUN_ZeroOne
public import Definitions.Def_AddUN_TheoremA
public import Theorems.Thm_AddUN_theoremA_of_grzegorek
public import Theorems.Thm_AddUN_grzegorek


set_option autoImplicit false
@[expose] public section
public section
open Set Filter Topology Cardinal MeasureTheory IdealInvariant
open scoped ENNReal
open AddUN
variable {U : Set (ℕ → Bool)}
namespace AddUN
theorem _root_.solution : TheoremA := theoremA_of_grzegorek grzegorek
end AddUN
