-- Prove2me | solution 1 for AddUN.le_spread
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T07:42:22.361867+00:00
-- url     : https://prove2.me/submissions/089cbee0-f5f4-44e6-b161-0addb09995a4

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
theorem _root_.solution (g : ℕ → ℕ) (k₀ k : ℕ) : g (k + k₀) ≤ spread g k₀ k := Nat.right_le_pair _ _
end AddUN
