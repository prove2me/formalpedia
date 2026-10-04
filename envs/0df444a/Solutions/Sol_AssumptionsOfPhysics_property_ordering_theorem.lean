-- Prove2me | solution 1 for AssumptionsOfPhysics.property_ordering_theorem
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-03T04:41:20.184036+00:00
-- url     : https://prove2.me/submissions/eb028867-57c3-4e72-ba66-26087012fa82

import Mathlib
import Definitions.Def_AoP_ExperimentalDomains
import Definitions.Def_AoP_PropertiesQuantities

set_option autoImplicit false

open AssumptionsOfPhysics in
theorem AoP560_induced_eq {X Q : Type*} [r : LinearOrder X] [LinearOrder Q] [tQ : TopologicalSpace Q]
    [OrderTopology Q] (o : X ≃o Q) :
    TopologicalSpace.induced o tQ = Preorder.topology X := by
  apply StrictMono.induced_topology_eq_preorder o.strictMono
  rw [o.surjective.range_eq]
  exact Set.ordConnected_univ

namespace AssumptionsOfPhysics
theorem AoP560_main {Ω : Type*} (D : ExperimentalDomain Ω) (Q : Type*)
    [LinearOrder Q] [TopologicalSpace Q] [OrderTopology Q] :
    D.IsFullyCharacterizedBy Q ↔
      ∃ r : LinearOrder D.Possibility, D.IsNaturalOrder r ∧
        Nonempty (@OrderIso D.Possibility Q r.toLE _) := by
  constructor
  · rintro ⟨h⟩
    let r : LinearOrder D.Possibility := LinearOrder.lift' h h.injective
    let o : @OrderIso D.Possibility Q r.toLE _ :=
      { toEquiv := h.toEquiv, map_rel_iff' := Iff.rfl }
    refine ⟨r, ?_, ⟨o⟩⟩
    unfold ExperimentalDomain.IsNaturalOrder
    rw [← AoP560_induced_eq o]
    exact h.isInducing.eq_induced.symm
  · rintro ⟨r, hr, ⟨o⟩⟩
    unfold ExperimentalDomain.IsNaturalOrder at hr
    let _ := r
    refine ⟨o.toEquiv.toHomeomorphOfIsInducing ⟨?_⟩⟩
    rw [← hr]
    exact (AoP560_induced_eq o).symm
end AssumptionsOfPhysics

open AssumptionsOfPhysics in
theorem solution {Ω : Type*} (D : ExperimentalDomain Ω) (Q : Type*)
    [LinearOrder Q] [TopologicalSpace Q] [OrderTopology Q] :
    D.IsFullyCharacterizedBy Q ↔
      ∃ r : LinearOrder D.Possibility, D.IsNaturalOrder r ∧
        Nonempty (@OrderIso D.Possibility Q r.toLE _) := by
  exact AoP560_main D Q

