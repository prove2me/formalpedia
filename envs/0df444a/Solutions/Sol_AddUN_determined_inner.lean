-- Prove2me | solution 1 for AddUN.determined_inner
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T07:32:31.528024+00:00
-- url     : https://prove2.me/submissions/16a73b4e-2ad1-4d01-8382-4103a30d65be

module
public import Definitions.Def_AddUN_Grzegorek
public import Definitions.Def_AddUN_ZeroOne
public import Definitions.Def_AddUN_TheoremA

set_option autoImplicit false
@[expose] public section
public section
open Set Filter Topology Cardinal MeasureTheory IdealInvariant
open scoped ENNReal
open AddUN
variable {U : Set (ℕ → Bool)}
namespace AddUN
theorem _root_.solution (n : ℕ) : Determined (↑(Finset.range n)) (inner U n) :=
  fun _ _ h hw _ hy ↦ hw fun i hi ↦ (hy i hi).trans (h i hi).symm
end AddUN
