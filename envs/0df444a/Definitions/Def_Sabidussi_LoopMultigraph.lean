-- Prove2me | Definitions.Def_Sabidussi_LoopMultigraph
-- name    : Sabidussi_LoopMultigraph
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-26T04:09:29.917417+00:00
-- url     : https://prove2.me/theorems/20e35ca2-2f07-4ae0-82f4-a91fe1917945
-- title:
--   Loop Multigraph
-- statement:
--   Definitions and structural lemmas for Loop Multigraph, from Upstream contributors (gexahedron/sabidussi-lean; see pinned Apache-2.0 LICENSE and README.md)'s pinned Sabidussi compatibility conjecture for finite Eulerian loop multigraphs development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/gexahedron/sabidussi-lean/blob/58307d74da99ec6e4fe28e012c30c83e369c54c3/Sabidussi/LoopMultigraph.lean

import Definitions.Def_Sabidussi_Color
import Definitions.Def_Sabidussi_Statement
import Mathlib.Data.Fin.Rev
import Mathlib.Logic.Equiv.Fin.Rotate
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finite.Set
import Mathlib.Data.Fintype.Sets
import Theorems.Thm_Sabidussi_bracketRightHom_apply
import Theorems.Thm_Sabidussi_bracket_self
import Theorems.Thm_Sabidussi_tripleDifference_one
import Theorems.Thm_Sabidussi_tripleDifference_two
import Theorems.Thm_Sabidussi_tripleDifference_zero
attribute [local simp] Sabidussi.bracketRightHom_apply
attribute [local simp] Sabidussi.bracket_self
attribute [local simp] Sabidussi.tripleDifference_one
attribute [local simp] Sabidussi.tripleDifference_two
attribute [local simp] Sabidussi.tripleDifference_zero


set_option autoImplicit true
namespace Sabidussi
open scoped BigOperators
namespace LoopMultigraph
variable {V E : Type*} [Fintype V] [Fintype E]
namespace EulerTour
variable [DecidableEq V] {G : LoopMultigraph V E} (T : G.EulerTour)
def vertexAt (i : T.Pos) : V := G.endAt (T.edge i) (T.depart i)
def arrivalAt (i : T.Pos) : V := G.endAt (T.edge i) (Fin.rev (T.depart i))
@[simp]
theorem next_prev (i : T.Pos) : T.next (T.prev i) = i := by
  simp [next, prev]
@[simp]
theorem prev_next (i : T.Pos) : T.prev (T.next i) = i := by
  simp [next, prev]
theorem arrival_prev_eq_vertexAt (i : T.Pos) : T.arrivalAt (T.prev i) = T.vertexAt i := by
  simpa [arrivalAt, vertexAt, next, prev] using T.continuous (T.prev i)
abbrev Occurrence (v : V) := {i : T.Pos // T.vertexAt i = v}
instance (v : V) : Fintype (T.Occurrence v) :=
  Subtype.fintype fun i : T.Pos ↦ T.vertexAt i = v
def transitionHalfEdge {v : V} (o : T.Occurrence v) : Fin 2 → HalfEdge E
  | 0 => (T.edge o.1, T.depart o.1)
  | 1 => (T.edge (T.prev o.1), Fin.rev (T.depart (T.prev o.1)))
@[simp]
theorem vertex_transitionHalfEdge {v : V} (o : T.Occurrence v) (s : Fin 2) :
    G.vertex (T.transitionHalfEdge o s) = v := by
  fin_cases s
  · exact o.2
  · change T.arrivalAt (T.prev o.1) = v
    exact (T.arrival_prev_eq_vertexAt o.1).trans o.2
def occurrenceSideToHalfEdge (v : V) : T.Occurrence v × Fin 2 → G.halfEdgesAt v :=
  fun os ↦ ⟨T.transitionHalfEdge os.1 os.2, T.vertex_transitionHalfEdge os.1 os.2⟩
def positionSideToHalfEdge : T.Pos × Fin 2 → HalfEdge E
  | (i, 0) => (T.edge i, T.depart i)
  | (i, 1) => (T.edge (T.prev i), Fin.rev (T.depart (T.prev i)))
def halfEdgeToPositionSide (h : HalfEdge E) : T.Pos × Fin 2 :=
  let i := T.edge.symm h.1
  if h.2 = T.depart i then (i, 0) else (T.next i, 1)
theorem rev_ne_self_fin_two (i : Fin 2) : Fin.rev i ≠ i := by
  fin_cases i <;> decide
theorem eq_rev_of_ne_fin_two {i j : Fin 2} (h : i ≠ j) : i = Fin.rev j := by
  fin_cases i <;> fin_cases j <;> simp_all [Fin.rev]
theorem halfEdgeToPositionSide_positionSideToHalfEdge (p : T.Pos × Fin 2) :
    T.halfEdgeToPositionSide (T.positionSideToHalfEdge p) = p := by
  rcases p with ⟨i, s⟩
  fin_cases s
  · simp [positionSideToHalfEdge, halfEdgeToPositionSide]
  · simp [positionSideToHalfEdge, halfEdgeToPositionSide, rev_ne_self_fin_two,
      T.next_prev]
theorem positionSideToHalfEdge_halfEdgeToPositionSide (h : HalfEdge E) :
    T.positionSideToHalfEdge (T.halfEdgeToPositionSide h) = h := by
  rcases h with ⟨e, j⟩
  let i : T.Pos := T.edge.symm e
  by_cases hj : j = T.depart i
  · subst j
    simp [halfEdgeToPositionSide, positionSideToHalfEdge, i]
  · have hrev : j = Fin.rev (T.depart i) := by
      exact eq_rev_of_ne_fin_two hj
    subst j
    simp [halfEdgeToPositionSide, positionSideToHalfEdge, i, rev_ne_self_fin_two,
      T.prev_next]
def positionSideEquivHalfEdge : T.Pos × Fin 2 ≃ HalfEdge E where
  toFun := T.positionSideToHalfEdge
  invFun := T.halfEdgeToPositionSide
  left_inv := T.halfEdgeToPositionSide_positionSideToHalfEdge
  right_inv := T.positionSideToHalfEdge_halfEdgeToPositionSide
theorem vertex_positionSideToHalfEdge (p : T.Pos × Fin 2) :
    G.vertex (T.positionSideToHalfEdge p) = T.vertexAt p.1 := by
  rcases p with ⟨i, s⟩
  fin_cases s
  · rfl
  · change T.arrivalAt (T.prev i) = T.vertexAt i
    exact T.arrival_prev_eq_vertexAt i
def occurrenceSideEquivHalfEdgesAt (v : V) : T.Occurrence v × Fin 2 ≃ G.halfEdgesAt v :=
  (Equiv.prodSubtypeFstEquivSubtypeProd (p := fun i : T.Pos ↦ T.vertexAt i = v)).symm |>.trans
    (T.positionSideEquivHalfEdge.subtypeEquiv fun p ↦ by
      change T.vertexAt p.1 = v ↔ G.vertex (T.positionSideToHalfEdge p) = v
      rw [T.vertex_positionSideToHalfEdge p])
end EulerTour
variable {V E : Type*} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
  (G : LoopMultigraph V E)
def edgeIncidence (v : V) (e : E) : F₂ :=
  (if G.endAt e 0 = v then 1 else 0) +
    (if G.endAt e 1 = v then 1 else 0)
def IsEvenEdgeSet (F : Finset E) : Prop :=
  ∀ v : V, ∑ e ∈ F, G.edgeIncidence v e = 0
structure Cycle where
  edges : Finset E
  nonempty : edges.Nonempty
  even : G.IsEvenEdgeSet edges
  minimal : ∀ D : Finset E, D.Nonempty → D ⊆ edges → G.IsEvenEdgeSet D → D = edges
theorem singleton_loop_even (e : E) (hloop : G.endAt e 0 = G.endAt e 1) :
    G.IsEvenEdgeSet {e} := by
  intro v
  simp only [Finset.sum_singleton]
  change (if G.endAt e 0 = v then 1 else 0) +
      (if G.endAt e 1 = v then 1 else 0) = 0
  rw [← hloop]
  exact CharTwo.add_self_eq_zero _
def loopCycle (e : E) (hloop : G.endAt e 0 = G.endAt e 1) : G.Cycle where
  edges := {e}
  nonempty := ⟨e, by simp⟩
  even := G.singleton_loop_even e hloop
  minimal := by
    intro D hDne hDsub _
    exact hDne.subset_singleton_iff.mp hDsub
open Sabidussi
variable {V E : Type*} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
  (G : LoopMultigraph V E)
structure CircuitDecomposition where
  circuits : List G.Cycle
  coveredOnce : ∀ e : E, (circuits.filter fun C ↦ e ∈ C.edges).length = 1
def CircuitDecomposition.Compatible {G : LoopMultigraph V E}
    (S : G.CircuitDecomposition) (T : G.EulerTour) : Prop :=
  ∀ (i : T.Pos) (C : G.Cycle), C ∈ S.circuits →
    ¬ (T.edge (T.prev i) ∈ C.edges ∧ T.edge i ∈ C.edges)
structure CompatibleFourColoring (T : G.EulerTour) where
  color : E → Color
  transition_ne : ∀ i : T.Pos, color (T.edge (T.prev i)) ≠ color (T.edge i)
  color_even : ∀ z : Color,
    G.IsEvenEdgeSet (Finset.univ.filter fun e ↦ color e = z)
namespace CompatibleFourColoring
end CompatibleFourColoring
end LoopMultigraph
end Sabidussi


