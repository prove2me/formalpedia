-- Prove2me | solution 1 for AssumptionsOfPhysics.real_orderTopology_eq_rational_intervals
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-03T01:10:48.07516+00:00
-- url     : https://prove2.me/submissions/1d9ee3a0-8e60-4322-8426-a08b0fcaa3b4

import Mathlib
import Definitions.Def_AoP_ExperimentalDomains
import Definitions.Def_AoP_PropertiesQuantities

set_option autoImplicit false

open AssumptionsOfPhysics in
theorem solution :
    Preorder.topology ℝ =
      TopologicalSpace.generateFrom {S : Set ℝ | ∃ a b : ℚ, S = Set.Ioo (a : ℝ) (b : ℝ)} := by
  have h1 : Preorder.topology ℝ = (inferInstance : TopologicalSpace ℝ) :=
    (OrderTopology.topology_eq_generate_intervals (α := ℝ)).symm
  rw [h1]
  apply le_antisymm
  · apply le_generateFrom
    rintro s ⟨a, b, rfl⟩
    exact isOpen_Ioo
  · conv_rhs => rw [Real.isTopologicalBasis_Ioo_rat.eq_generateFrom]
    apply TopologicalSpace.generateFrom_anti
    intro s hs
    simp only [Set.mem_iUnion, Set.mem_singleton_iff] at hs
    obtain ⟨a, b, _, rfl⟩ := hs
    exact ⟨a, b, rfl⟩
