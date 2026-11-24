-- Prove2me | solution 1 for AddUN.measurableSet_smallClopen
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T07:40:39.105403+00:00
-- url     : https://prove2.me/submissions/65572c1a-033b-4467-a7ef-b550fc74a342

module
public import Definitions.Def_AddUN_Localisation
public import Definitions.Def_AddUN_Transfer
public import Definitions.Def_AddUN_Uniformity
public import Mathlib.MeasureTheory.Measure.Prod
public import Definitions.Def_AddUN_Grzegorek

set_option autoImplicit false
@[expose] public section
public section
open Set Filter Topology TopologicalSpace Cardinal MeasureTheory IdealInvariant
open scoped ENNReal
open AddUN
namespace AddUN
theorem _root_.solution (n k : ℕ) : MeasurableSet (smallClopen n k) := by
  unfold smallClopen
  split_ifs
  · exact (clopenEnum k).isClopen.isOpen.measurableSet
  · exact .empty
end AddUN
