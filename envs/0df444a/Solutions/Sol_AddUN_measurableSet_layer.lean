-- Prove2me | solution 1 for AddUN.measurableSet_layer
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T07:41:31.158166+00:00
-- url     : https://prove2.me/submissions/55b60cb3-4c5d-4df3-9447-2a50759402f0

module
public import Definitions.Def_AddUN_Grzegorek
public import Definitions.Def_AddUN_ZeroOne
public import Definitions.Def_AddUN_TheoremA
public import Theorems.Thm_AddUN_isOpen_inner
public import Theorems.Thm_MeasureTheory_Determined_diff


set_option autoImplicit false
@[expose] public section
public section
open Set Filter Topology Cardinal MeasureTheory IdealInvariant
open scoped ENNReal
open AddUN
variable {U : Set (ℕ → Bool)}
namespace AddUN
theorem _root_.solution (M : ℕ → ℕ) (k : ℕ) : MeasurableSet (layer U M k) := by
  cases k with
  | zero => exact (isOpen_inner _).measurableSet
  | succ k => exact (isOpen_inner _).measurableSet.diff (isOpen_inner _).measurableSet
end AddUN
