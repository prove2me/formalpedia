-- Prove2me | Definitions.Def_ChinesePostman_Matching_Setting
-- name    : ChinesePostman_Matching_Setting
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-06T06:25:27.542774+00:00
-- url     : https://prove2.me/theorems/cd72b967-5cb9-4312-9366-807ee6eb968d
-- title:
--   §2–§3, pp. 89–93 — walks, parity solutions, shortest paths, and odd-node matchings
-- statement:
--   This setting defines edge-labelled walks and tours in a finite loopless multigraph $G=(N,E)$, the degree of each node, and the set $T$ of odd-degree nodes. It also defines postman and Euler tours, edge-simple paths, and connectivity.
--
--   For extra traversal counts $x_e\in\mathbb N$, a **parity solution** is one for which there are nonnegative integers $w_v$ satisfying
--
--   $$
--   \sum_{e\ni v}x_e=2w_v+\mathbf1_{v\in T}\qquad(v\in N).
--   $$
--
--   Its cost is $z(x)=\sum_{e\in E}c_ex_e$. A **shortest-path length** $d(u,v)$ has an attaining edge-simple path and bounds below every walk from $u$ to $v$. A **1-matching** pairs every node of $T$ once with a distinct node; its length is $\frac12\sum_{v\in T}d(v,f(v))$.
--
--   These shared objects state the matching reduction using the paper's edge names, parity equations, and nonnegative integral variables.
--
--   **Formalization Note** A matching path family records both orientations of each pair as reversed node and edge lists; paths for different pairs are edge-disjoint. The underlying graph is the referenced published Edmonds 1965 loopless multigraph structure, with finite vertex and edge types; it has exactly the named-edge and parallel-edge conventions used here.
-- source:
--   Edmonds and Johnson, Matching, Euler tours and the Chinese postman, Math. Programming 5 (1973), pp. 89–93, §2–§3, (3.1)–(3.4), https://doi.org/10.1007/BF01580113

import Mathlib
import Definitions.Def_EdmondsMatching65_Polyhedron_Graph

namespace ChinesePostman.Matching


/-- The number of edges incident to a node. -/
def degree {V E : Type*} [Fintype E] [DecidableEq V]
    (G : EdmondsMatching65.Polyhedron.Graph V E) (v : V) : ℕ := by
  classical
  exact (Finset.univ.filter (fun e => v ∈ G.ends e)).card

/-- Nodes of odd degree. -/
def oddNodes {V E : Type*} [Fintype V] [Fintype E] [DecidableEq V]
    (G : EdmondsMatching65.Polyhedron.Graph V E) : Finset V := by
  classical
  exact Finset.univ.filter (fun v => Odd (degree G v))

/-- An alternating node-edge sequence, including the one-node, zero-edge walk. -/
def IsWalk {V E : Type*} (G : EdmondsMatching65.Polyhedron.Graph V E) (ns : List V) (es : List E) : Prop :=
  ns.length = es.length + 1 ∧
    ∀ i : Fin es.length, ∃ u v : V,
      ns[i.val]? = some u ∧ ns[i.val + 1]? = some v ∧ G.ends es[i] = s(u, v)

/-- A walk with prescribed initial and terminal nodes. -/
def IsWalkFrom {V E : Type*} (G : EdmondsMatching65.Polyhedron.Graph V E) (i j : V)
    (ns : List V) (es : List E) : Prop :=
  IsWalk G ns es ∧ ns.head? = some i ∧ ns.getLast? = some j

/-- A closed walk. -/
def IsTour {V E : Type*} (G : EdmondsMatching65.Polyhedron.Graph V E) (ns : List V) (es : List E) : Prop :=
  IsWalk G ns es ∧ ns.head? = ns.getLast?

/-- A tour using every named edge exactly once. -/
def IsEulerTour {V E : Type*} [DecidableEq E] (G : EdmondsMatching65.Polyhedron.Graph V E)
    (ns : List V) (es : List E) : Prop :=
  IsTour G ns es ∧ ∀ e : E, es.count e = 1

/-- A tour using every named edge at least once. -/
def IsPostmanTour {V E : Type*} (G : EdmondsMatching65.Polyhedron.Graph V E)
    (ns : List V) (es : List E) : Prop :=
  IsTour G ns es ∧ ∀ e : E, e ∈ es

/-- A path from i to j with no repeated edge. -/
def IsEdgeSimplePath {V E : Type*} (G : EdmondsMatching65.Polyhedron.Graph V E) (i j : V)
    (ns : List V) (es : List E) : Prop :=
  IsWalkFrom G i j ns es ∧ es.Nodup

/-- Every two nodes are joined by an edge-labelled walk. -/
def Connected {V E : Type*} (G : EdmondsMatching65.Polyhedron.Graph V E) : Prop :=
  ∀ i j : V, ∃ ns : List V, ∃ es : List E, IsWalkFrom G i j ns es

/-- Length of an edge-labelled walk. -/
def walkLength {E : Type*} (c : E → ℝ) (es : List E) : ℝ :=
  (es.map c).sum

/-- Sum of multiplicities on the edges incident to a node. -/
def incidentSum {V E : Type*} [Fintype E] [DecidableEq V]
    (G : EdmondsMatching65.Polyhedron.Graph V E) (x : E → ℕ) (v : V) : ℕ := by
  classical
  exact ∑ e ∈ Finset.univ.filter (fun e => v ∈ G.ends e), x e

/-- Equations (3.1)–(3.3): nonnegative integral extra edge multiplicities. -/
def IsParitySolution {V E : Type*} [Fintype E] [DecidableEq V]
    (G : EdmondsMatching65.Polyhedron.Graph V E) (x : E → ℕ) : Prop :=
  ∃ w : V → ℕ, ∀ v, incidentSum G x v =
    2 * w v + if Odd (degree G v) then 1 else 0

/-- The parity problem's objective (3.4). -/
def cost {E : Type*} [Fintype E] (c : E → ℝ) (x : E → ℕ) : ℝ :=
  ∑ e, c e * (x e : ℝ)

/-- A shortest-path length, with an attaining edge-simple path and a lower bound on every walk. -/
def IsShortestPathLength {V E : Type*} (G : EdmondsMatching65.Polyhedron.Graph V E) (c : E → ℝ)
    (i j : V) (d : ℝ) : Prop :=
  (∃ ns : List V, ∃ es : List E,
    IsEdgeSimplePath G i j ns es ∧ walkLength c es = d) ∧
  (∀ ns : List V, ∀ es : List E, IsWalkFrom G i j ns es → d ≤ walkLength c es)

/-- A 1-matching of the complete graph on the odd nodes, as a fixed-point-free involution. -/
def IsOddPerfectMatching {V E : Type*} [Fintype V] [Fintype E] [DecidableEq V]
    (G : EdmondsMatching65.Polyhedron.Graph V E) (f : V → V) : Prop :=
  (∀ v ∈ oddNodes G, f v ∈ oddNodes G ∧ f v ≠ v ∧ f (f v) = v) ∧
  ∀ v ∉ oddNodes G, f v = v

/-- Sum of shortest-path lengths over matching edges, each counted once. -/
noncomputable def matchingLength {V E : Type*} [Fintype V] [Fintype E] [DecidableEq V]
    (G : EdmondsMatching65.Polyhedron.Graph V E) (d : V → V → ℝ) (f : V → V) : ℝ :=
  (1 / 2 : ℝ) * ∑ v ∈ oddNodes G, d v (f v)

/-- An edge-simple path for each orientation of a matching edge. Opposite orientations
are reversals, and distinct matching edges have edge-disjoint paths. -/
def MatchingPaths {V E : Type*} [Fintype V] [Fintype E] [DecidableEq V]
    (G : EdmondsMatching65.Polyhedron.Graph V E) (f : V → V) (P : V → List V × List E) : Prop :=
  (∀ v ∈ oddNodes G,
    IsEdgeSimplePath G v (f v) (P v).1 (P v).2 ∧
    (P (f v)).1 = (P v).1.reverse ∧
    (P (f v)).2 = (P v).2.reverse) ∧
  (∀ v w : V, v ∈ oddNodes G → w ∈ oddNodes G →
    w ≠ v → w ≠ f v → ∀ e : E, e ∈ (P v).2 → e ∉ (P w).2)

/-- Indicator of the union of paths associated with matching edges. -/
noncomputable def pathIndicator {V E : Type*} [Fintype V] [Fintype E]
    [DecidableEq V] (G : EdmondsMatching65.Polyhedron.Graph V E) (P : V → List V × List E) (e : E) : ℕ := by
  classical
  exact if ∃ v ∈ oddNodes G, e ∈ (P v).2 then 1 else 0

end ChinesePostman.Matching


