-- Prove2me | solution 1 for AddUN.inner_subset
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T07:32:23.944313+00:00
-- url     : https://prove2.me/submissions/9079f22b-63f7-45f2-b3cb-dc1408d32596

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
theorem _root_.solution (n : ℕ) : inner U n ⊆ U := fun _ hx ↦ hx fun _ _ ↦ rfl
end AddUN
