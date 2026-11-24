-- Prove2me | solution 1 for AddUN.inner_mono
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T07:32:24.448801+00:00
-- url     : https://prove2.me/submissions/2194c224-7e22-4863-8cd0-f0da91db1e75

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
theorem _root_.solution {m n : ℕ} (h : m ≤ n) : inner U m ⊆ inner U n := fun _ hx _ hy ↦
  hx fun i hi ↦ hy i (Finset.mem_range.2 (lt_of_lt_of_le (Finset.mem_range.1 hi) h))
end AddUN
