-- Prove2me | Definitions.Def_Sabidussi_Statement
-- name    : Sabidussi_Statement
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-26T04:07:11.781838+00:00
-- url     : https://prove2.me/theorems/c7c6985d-579b-51dd-a7e1-d47b30dafbea
-- title:
--   Statement
-- statement:
--   Definitions and structural lemmas for Statement, from Upstream contributors (gexahedron/sabidussi-lean; see pinned Apache-2.0 LICENSE and README.md)'s pinned Sabidussi compatibility conjecture for finite Eulerian loop multigraphs development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/gexahedron/sabidussi-lean/blob/58307d74da99ec6e4fe28e012c30c83e369c54c3/Sabidussi/Statement.lean

import Mathlib
set_option autoImplicit true
namespace Sabidussi
structure LoopMultigraph (V E : Type*) [Fintype V] [Fintype E] where
  endAt : E → Fin 2 → V
namespace LoopMultigraph
variable {V E : Type*} [Fintype V] [Fintype E] [DecidableEq V]
abbrev HalfEdge (E : Type*) := E × Fin 2
def vertex (G : LoopMultigraph V E) (h : HalfEdge E) : V := G.endAt h.1 h.2
def halfEdgesAt (G : LoopMultigraph V E) (v : V) :=
  {h : HalfEdge E // G.vertex h = v}
instance (G : LoopMultigraph V E) (v : V) : Fintype (G.halfEdgesAt v) :=
  Subtype.fintype fun h : HalfEdge E ↦ G.vertex h = v
def degree (G : LoopMultigraph V E) (v : V) : ℕ :=
  Fintype.card (G.halfEdgesAt v)
variable {V E : Type*} [Fintype V] [Fintype E]
structure EulerTour (G : LoopMultigraph V E) where
  /-- The edge positions are `Fin (n + 1)`. -/
  n : ℕ
  /-- Every edge object occurs at exactly one position. -/
  edge : Fin (n + 1) ≃ E
  /-- The end from which the edge at a position is traversed. -/
  depart : Fin (n + 1) → Fin 2
  /-- The arrival end at a position is the departure vertex at the next position. -/
  continuous : ∀ i,
    G.endAt (edge i) (Fin.rev (depart i)) =
      G.endAt (edge (finRotate (n + 1) i)) (depart (finRotate (n + 1) i))
namespace EulerTour
variable [DecidableEq V] {G : LoopMultigraph V E} (T : G.EulerTour)
abbrev Pos := Fin (T.n + 1)
def next (i : T.Pos) : T.Pos := finRotate (T.n + 1) i
def prev (i : T.Pos) : T.Pos := (finRotate (T.n + 1)).symm i
end EulerTour
variable {V E : Type*} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
  (G : LoopMultigraph V E)
def degreeIn (F : Finset E) (v : V) : ℕ :=
  ((F ×ˢ (Finset.univ : Finset (Fin 2))).filter fun h ↦ G.endAt h.1 h.2 = v).card
def EdgeAdjacent (e f : E) : Prop :=
  ∃ i j : Fin 2, G.endAt e i = G.endAt f j
def EdgeConnected (F : Finset E) : Prop :=
  ∃ root ∈ F, ∀ e ∈ F,
    Relation.ReflTransGen
      (fun x y : E ↦ x ∈ F ∧ y ∈ F ∧ G.EdgeAdjacent x y) root e
def edgeSupport (F : Finset E) : Finset V :=
  Finset.univ.filter fun v ↦ ∃ e ∈ F, ∃ i : Fin 2, G.endAt e i = v
structure OrdinaryCircuit where
  edges : Finset E
  nonempty : edges.Nonempty
  connected : G.EdgeConnected edges
  twoRegular : ∀ v : V, v ∈ G.edgeSupport edges → G.degreeIn edges v = 2
structure OrdinaryCircuitDecomposition where
  circuits : List G.OrdinaryCircuit
  coveredOnce : ∀ e : E, (circuits.filter fun C ↦ e ∈ C.edges).length = 1
def OrdinaryCircuitDecomposition.Compatible {G : LoopMultigraph V E}
    (S : G.OrdinaryCircuitDecomposition) (T : G.EulerTour) : Prop :=
  ∀ (i : T.Pos) (C : G.OrdinaryCircuit), C ∈ S.circuits →
    ¬ (T.edge (T.prev i) ∈ C.edges ∧ T.edge i ∈ C.edges)
end LoopMultigraph
end Sabidussi


