-- Prove2me | solution 1 for AssumptionsOfPhysics.domainEquiv_equivalence
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-03T02:43:56.077987+00:00
-- url     : https://prove2.me/submissions/ca462c58-5bdb-46b7-82f5-362560903e21

import Mathlib
import Definitions.Def_AoP_ExperimentalDomains
import Definitions.Def_AoP_DomainRelationships

set_option autoImplicit false

open AssumptionsOfPhysics in
theorem solution {Ω : Type*} :
    Equivalence (ExperimentalDomain.DomainEquiv (Ω := Ω)) := by
  refine ⟨fun D => ⟨⟨id, fun _ => rfl⟩, ⟨id, fun _ => rfl⟩⟩, fun h => ⟨h.2, h.1⟩, ?_⟩
  intro A B C hAB hBC
  obtain ⟨⟨r1, h1⟩, ⟨s1, k1⟩⟩ := hAB
  obtain ⟨⟨r2, h2⟩, ⟨s2, k2⟩⟩ := hBC
  exact ⟨⟨r2 ∘ r1, fun s => by simp [Function.comp, h2, h1]⟩,
    ⟨s1 ∘ s2, fun s => by simp [Function.comp, k1, k2]⟩⟩
