-- Prove2me | solution 1 for AssumptionsOfPhysics.causalRel_unique
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-03T02:10:09.847136+00:00
-- url     : https://prove2.me/submissions/aa29604e-bd8a-4f65-9f03-434157e5e9bb

import Mathlib
import Definitions.Def_AoP_ExperimentalDomains
import Definitions.Def_AoP_DomainRelationships

set_option autoImplicit false

open AssumptionsOfPhysics in
theorem c5b111e6_poss_ext {Ω : Type*} {D : ExperimentalDomain Ω}
    (a b : D.Possibility) (h : a.val = b.val) : a = b := by
  cases a
  cases b
  cases h
  rfl

open AssumptionsOfPhysics in
theorem solution {Ω : Type*} (DX DY : ExperimentalDomain Ω)
    (f₁ f₂ : DX.Possibility → DY.Possibility)
    (h₁ : ExperimentalDomain.IsCausalRel DX DY f₁)
    (h₂ : ExperimentalDomain.IsCausalRel DX DY f₂) : f₁ = f₂ := by
  funext x
  obtain ⟨w, hw⟩ := x.isPossibility.2.1
  have hw1 : w ∈ (f₁ x).val := h₁ x hw
  have hw2 : w ∈ (f₂ x).val := h₂ x hw
  apply c5b111e6_poss_ext
  apply Set.Subset.antisymm
  · rcases (f₁ x).isPossibility.2.2 (f₂ x).val (f₂ x).isPossibility.1 with hs | hd
    · exact hs
    · exact absurd hw2 (Set.disjoint_left.mp hd hw1)
  · rcases (f₂ x).isPossibility.2.2 (f₁ x).val (f₁ x).isPossibility.1 with hs | hd
    · exact hs
    · exact absurd hw1 (Set.disjoint_left.mp hd hw2)

#print axioms solution
