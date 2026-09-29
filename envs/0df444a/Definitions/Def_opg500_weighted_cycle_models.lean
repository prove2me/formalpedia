-- Prove2me | Definitions.Def_opg500_weighted_cycle_models
-- name    : opg500_weighted_cycle_models
-- status  : Definition
-- author  : @hao jia
-- created : 2026-09-07T04:06:28.959086+00:00
-- url     : https://prove2.me/theorems/3ea211fc-47d0-4738-88b2-a9adf0c59e02
-- title:
--   Positive edge weights, geodesic cycles, and peripheral cycles
-- statement:
--   This definition bundle fixes the finite weighted-graph semantics used by the OPG-500 mission.
--
--   For a finite simple graph $G$, an edge weight is a real-valued function on the actual edge subtype $E(G)$, and positivity means $0<\ell(e)$ for every edge. A cycle is a nontrivial simple closed walk. Its weighted length counts every traversed edge, and a shortest path is required to be simple and no longer than every other simple path with the same endpoints.
--
--   A cycle is vertex-geodesic when every pair of its vertices can be joined by a globally shortest simple path using only edges of the cycle. A cycle is peripheral when it is chordless and deleting its vertices leaves a connected induced graph or no vertices. Three-connectivity means that the graph has at least four vertices and remains connected after deleting any set of fewer than three vertices.
--
--   The bundle also defines binary edge-indicator vectors over $\mathbb Z/2\mathbb Z$ and the tight-edge predicate needed by supporting targets.
-- source:
--   Georgakopoulos--Sprüssel, Geodetic topological cycles in locally finite graphs, EJC 16 (2009), R144, https://arxiv.org/abs/0911.3999v1, Section 3.1 and Section 5, Problem 3; Open Problem Garden OPG-500, https://www.openproblemgarden.org/op/geodesic_cycles_and_tuttes_theorem

import Mathlib.Combinatorics.SimpleGraph.Connectivity.Finite
import Mathlib.Combinatorics.SimpleGraph.Walk.Chord
import Mathlib.Data.Real.Basic

open Set
open scoped Sym2

namespace OPG500Counterexample

universe u

abbrev Edge {V : Type u} (G : SimpleGraph V) := G.edgeSet

abbrev EdgeWeight {V : Type u} (G : SimpleGraph V) := Edge G → ℝ

def IsPositive {V : Type u} {G : SimpleGraph V} (ℓ : EdgeWeight G) : Prop :=
  ∀ e, 0 < ℓ e

structure Cycle {V : Type u} (G : SimpleGraph V) where
  base : V
  walk : G.Walk base base
  isCycle : walk.IsCycle

def Walk.edgeList {V : Type u} {G : SimpleGraph V} {u v : V}
    (p : G.Walk u v) : List (Edge G) :=
  p.edges.attach.map fun e => ⟨e.1, p.edges_subset_edgeSet e.2⟩

def Walk.weightedLength {V : Type u} {G : SimpleGraph V} {u v : V}
    (ℓ : EdgeWeight G) (p : G.Walk u v) : ℝ :=
  ((Walk.edgeList p).map ℓ).sum

def Walk.IsShortest {V : Type u} {G : SimpleGraph V} {u v : V}
    (ℓ : EdgeWeight G) (p : G.Walk u v) : Prop :=
  p.IsPath ∧ ∀ q : G.Walk u v, q.IsPath →
    Walk.weightedLength ℓ p ≤ Walk.weightedLength ℓ q

def Cycle.vertexSet {V : Type u} {G : SimpleGraph V} (C : Cycle G) : Set V :=
  {v | v ∈ C.walk.support}

def Cycle.edgeSet {V : Type u} {G : SimpleGraph V} (C : Cycle G) : Set (Sym2 V) :=
  C.walk.edgeSet

def Cycle.edgeVector {V : Type u} [DecidableEq V] {G : SimpleGraph V}
    (C : Cycle G) (e : Sym2 V) : ZMod 2 :=
  if e ∈ C.walk.edges then 1 else 0

def CycleList.edgeVectorSum {V : Type u} [DecidableEq V] {G : SimpleGraph V}
    (cycles : List (Cycle G)) (e : Sym2 V) : ZMod 2 :=
  (cycles.map fun C => C.edgeVector e).sum

/-- A graph edge is tight when its one-edge walk is a globally shortest path
between its endpoints. The existential endpoints make this definition independent
of an orientation chosen for the unordered edge. -/
def Edge.IsTight {V : Type u} {G : SimpleGraph V}
    (ℓ : EdgeWeight G) (e : Edge G) : Prop :=
  ∃ x y : V, ∃ h : G.Adj x y,
    e.1 = s(x, y) ∧ Walk.IsShortest ℓ h.toWalk

/-- A vertex-based weighted geodesic cycle: between any two of its vertices,
there is a globally shortest simple path using only edges of the cycle. -/
def Cycle.IsGeodesic {V : Type u} {G : SimpleGraph V}
    (ℓ : EdgeWeight G) (C : Cycle G) : Prop :=
  ∀ ⦃x y : V⦄, x ∈ C.vertexSet → y ∈ C.vertexSet →
    ∃ p : G.Walk x y, Walk.IsShortest ℓ p ∧ p.edgeSet ⊆ C.edgeSet

/-- An induced cycle whose vertex deletion leaves a connected graph or no vertices. -/
def Cycle.IsPeripheral {V : Type u} {G : SimpleGraph V} (C : Cycle G) : Prop :=
  C.walk.IsChordless ∧
    (IsEmpty {v : V // v ∉ C.vertexSet} ∨
      (G.induce {v | v ∉ C.vertexSet}).Connected)

/-- Vertex 3-connectivity for a finite simple graph: at least four vertices,
and deletion of any set of fewer than three vertices leaves a connected graph. -/
def IsThreeConnected {V : Type u} [Fintype V] (G : SimpleGraph V) : Prop :=
  4 ≤ Fintype.card V ∧
    ∀ s : Finset V, s.card < 3 → (G.induce {v | v ∉ s}).Connected

end OPG500Counterexample


