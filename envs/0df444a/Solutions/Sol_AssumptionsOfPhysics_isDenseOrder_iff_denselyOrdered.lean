-- Prove2me | solution 1 for AssumptionsOfPhysics.isDenseOrder_iff_denselyOrdered
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-03T01:18:33.495182+00:00
-- url     : https://prove2.me/submissions/e7657f3f-b7fd-48d3-b5c2-f61e69b7ca5a

import Mathlib
import Definitions.Def_AoP_ExperimentalDomains
import Definitions.Def_AoP_PropertiesQuantities

set_option autoImplicit false

open AssumptionsOfPhysics in
theorem solution (Q : Type*) [LinearOrder Q] :
    IsDenseOrder Q ↔ DenselyOrdered Q := by
  constructor
  · intro h
    refine ⟨fun a b hab => ?_⟩
    by_contra hne
    push_neg at hne
    apply h a b hab
    refine (Set.toFinite ({a, b} : Set Q)).subset ?_
    intro x hx
    rcases hx with ⟨h1, h2⟩
    rcases h1.lt_or_eq with h1 | h1
    · rcases h2.lt_or_eq with h2 | h2
      · exact absurd h2 (not_lt.mpr (hne x h1))
      · simp [h2]
    · simp [h1]
  · intro _ a b hab
    exact Set.Icc_infinite hab
