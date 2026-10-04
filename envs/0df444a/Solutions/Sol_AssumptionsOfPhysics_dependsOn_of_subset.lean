-- Prove2me | solution 1 for AssumptionsOfPhysics.dependsOn_of_subset
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-03T02:57:22.945261+00:00
-- url     : https://prove2.me/submissions/763f1d6c-c915-4d27-b6ea-471d8e1075a9

import Mathlib
import Definitions.Def_AoP_ExperimentalDomains
import Definitions.Def_AoP_DomainRelationships

set_option autoImplicit false

open AssumptionsOfPhysics in
theorem solution {Ω : Type*} (DX DY : ExperimentalDomain Ω)
    (h : DY.stmts ⊆ DX.stmts) : ExperimentalDomain.DependsOn DY DX := by
  exact ⟨fun s => ⟨s.1, h s.2⟩, fun s => rfl⟩

