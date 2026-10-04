-- Prove2me | solution 1 for AssumptionsOfPhysics.discrete_ordering_theorem
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-03T08:34:14.782067+00:00
-- url     : https://prove2.me/submissions/48adf2e4-8936-41d7-8084-3830658759c2

import Mathlib
import Definitions.Def_AoP_ExperimentalDomains
import Definitions.Def_AoP_PropertiesQuantities

set_option autoImplicit false
set_option linter.style.haveILetI false

namespace AoPDiscreteA7

open AssumptionsOfPhysics

universe u

lemma sparse_of_orderIso {α β : Type*} [Preorder α] [Preorder β] (e : α ≃o β)
    (h : IsSparseOrder β) : IsSparseOrder α := by
  intro a b
  have : Set.Icc a b = e ⁻¹' Set.Icc (e a) (e b) := by
    ext x; simp [Set.mem_Icc]
  rw [this]
  exact (h (e a) (e b)).preimage e.injective.injOn

lemma orderTop_eq_induced {α β : Type*} [Preorder α] [Preorder β] [tβ : TopologicalSpace β]
    [OrderTopology β] (e : α ≃o β) :
    Preorder.topology α = TopologicalSpace.induced e tβ := by
  letI : TopologicalSpace α := Preorder.topology α
  haveI : OrderTopology α := ⟨rfl⟩
  exact (e.toHomeomorph.induced_eq).symm

lemma backward {Ω : Type u} (D : ExperimentalDomain Ω) (Q : Type) [LinearOrder Q]
    [tQ : TopologicalSpace Q] [OrderTopology Q] (hs : IsSparseOrder Q)
    (h : D.Possibility ≃ₜ Q) :
    ∃ r : LinearOrder D.Possibility, D.IsNaturalOrder r ∧ @IsSparseOrder _ r.toPreorder := by
  classical
  let r : LinearOrder D.Possibility := h.toEquiv.linearOrder
  letI := r
  let e : D.Possibility ≃o Q := { toEquiv := h.toEquiv, map_rel_iff' := Iff.rfl }
  refine ⟨r, ?_, sparse_of_orderIso e hs⟩
  show Preorder.topology D.Possibility = D.naturalTopology
  calc Preorder.topology D.Possibility = TopologicalSpace.induced e tQ := orderTop_eq_induced e
    _ = TopologicalSpace.induced h tQ := rfl
    _ = D.naturalTopology := h.induced_eq

lemma forward {Ω : Type u} (D : ExperimentalDomain Ω) (r : LinearOrder D.Possibility)
    (hnat : D.IsNaturalOrder r) (hsp : @IsSparseOrder _ r.toPreorder) :
    ∃ (Q : Type) (_ : LinearOrder Q) (_ : TopologicalSpace Q) (_ : OrderTopology Q),
        IsSparseOrder Q ∧ D.IsFullyCharacterizedBy Q := by
  classical
  letI := r
  have hnat' : Preorder.topology D.Possibility = D.naturalTopology := hnat
  haveI : LocallyFiniteOrder D.Possibility := LocallyFiniteOrder.ofFiniteIcc hsp
  haveI : Countable D.Possibility := Countable.of_linearOrder_locallyFiniteOrder
  haveI : Small.{0} D.Possibility := Countable.toSmall D.Possibility
  let eq : Shrink.{0} D.Possibility ≃ D.Possibility := (equivShrink D.Possibility).symm
  letI lo : LinearOrder (Shrink.{0} D.Possibility) := eq.linearOrder
  let e' : Shrink.{0} D.Possibility ≃o D.Possibility :=
    { toEquiv := eq, map_rel_iff' := Iff.rfl }
  letI tQ : TopologicalSpace (Shrink.{0} D.Possibility) := Preorder.topology _
  haveI hQ : OrderTopology (Shrink.{0} D.Possibility) := ⟨rfl⟩
  refine ⟨Shrink.{0} D.Possibility, lo, tQ, hQ, sparse_of_orderIso e' hsp, ?_⟩
  haveI : OrderTopology D.Possibility := ⟨hnat'.symm⟩
  exact ⟨e'.symm.toHomeomorph⟩

end AoPDiscreteA7

open AssumptionsOfPhysics in
theorem solution {Ω : Type*} (D : AssumptionsOfPhysics.ExperimentalDomain Ω) :
    (∃ r : LinearOrder D.Possibility, D.IsNaturalOrder r ∧ @IsSparseOrder _ r.toPreorder) ↔
      ∃ (Q : Type) (_ : LinearOrder Q) (_ : TopologicalSpace Q) (_ : OrderTopology Q),
        IsSparseOrder Q ∧ D.IsFullyCharacterizedBy Q := by
  constructor
  · rintro ⟨r, hn, hs⟩
    exact AoPDiscreteA7.forward D r hn hs
  · rintro ⟨Q, lo, t, ot, hs, ⟨h⟩⟩
    exact AoPDiscreteA7.backward D Q hs h
