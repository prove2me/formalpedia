-- Prove2me | Definitions.Def_OptimumBranchings_Polytope_Graph
-- name    : OptimumBranchings_Polytope_Graph
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-26T20:51:12.828253+00:00
-- url     : https://prove2.me/theorems/82de72d2-99c8-441c-8bcd-48164558b94b
-- title:
--   Directed graphs, forests, branchings and incidence vectors (§1, §5)
-- statement:
--   A **(directed) graph** $G$ consists of a finite set $V$ of nodes and a finite set $E$ of edges; each edge $e$ is directed toward one node $\mathrm{front}(e)$, its *front end*, and directed away from a *different* node $\mathrm{rear}(e)$, its *rear end*. Several edges may join the same pair of nodes (parallel edges), but no edge has both ends at the same node (no loops).
--
--   For a set $F\subseteq E$ of edges and a node $v$, say that $v$ *meets* $k$ edges of $F$ when
--   $$
--   \#\{e\in F:\mathrm{front}(e)=v\}+\#\{e\in F:\mathrm{rear}(e)=v\}=k .
--   $$
--
--   1. A set of edges $B$ is a **forest** if it contains no polygon: there is no nonempty $F\subseteq B$ such that every node meets either no edge or exactly two edges of $F$.
--   2. A set of edges $B$ is a **branching** if it is a forest and no two distinct edges of $B$ are directed toward the same node.
--   3. The **(incidence) vector** of a set of edges $B$ is the vector $x\in\mathbb R^{E}$ with $x_e=1$ for $e\in B$ and $x_e=0$ otherwise.
--
--   These are the combinatorial objects of Edmonds' theorem on the branching polyhedron: the vertices of $P_G$ are exactly the incidence vectors of branchings.
--
--   **Formalization Note** The graph is a structure with maps `front rear : E → V` and a proof that `front e ≠ rear e` for every edge; finiteness and decidable equality of `V` and `E` are typeclass assumptions at every use. A polygon (a connected graph each of whose nodes meets exactly two of its edges) has an edge set of the kind excluded in item 1, and every nonempty edge set in which each node meets zero or two edges is a disjoint union of polygons, so item 1 is exactly "contains no polygon". Two parallel edges form a polygon.
-- source:
--   Edmonds, Optimum branchings, J. Res. Nat. Bur. Standards 71B (1967), p. 233, Section 1 (graph, polygon, forest, branching); p. 235, Section 5 (incidence vector)

import Mathlib

namespace OptimumBranchings.Polytope

/-- A (directed) graph in the sense of Edmonds (1967), §1, p. 233: a finite set of nodes `V`, a
finite set of edges `E`, and for each edge a *front end* (the node it is directed toward) and a
*rear end* (the node it is directed away from), which is "a different one of the nodes".
Parallel edges are allowed; loops are excluded by `front_ne_rear`. Finiteness of `V` and `E`
is supplied by `[Fintype V] [Fintype E]` at every use. -/
structure Graph (V E : Type*) where
  /-- the front end of an edge: the node the edge is directed toward -/
  front : E → V
  /-- the rear end of an edge: the node the edge is directed away from -/
  rear : E → V
  /-- the two ends of an edge are different nodes (no loops) -/
  front_ne_rear : ∀ e, front e ≠ rear e

variable {V E : Type*} [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E]

/-- The number of edges of `F` that the node `v` meets, i.e. of which `v` is an end.
Since an edge has two different ends, it is counted once at its front end and once at its
rear end. -/
def Graph.meetCount (G : Graph V E) (F : Finset E) (v : V) : ℕ :=
  (F.filter (fun e => G.front e = v)).card + (F.filter (fun e => G.rear e = v)).card

/-- A set of edges `B` is a *forest* (contains no polygon; §1, p. 233): there is no nonempty
`F ⊆ B` in which every node meets either no edge or exactly two edges of `F`. Such an `F` is
exactly a vertex-disjoint union of polygons, and the edge set of a polygon is such an `F`. -/
def Graph.IsForest (G : Graph V E) (B : Finset E) : Prop :=
  ∀ F : Finset E, F ⊆ B → F.Nonempty →
    ¬ ∀ v : V, G.meetCount F v = 0 ∨ G.meetCount F v = 2

/-- A set of edges `B` is a *branching* (§1, p. 233): a forest whose edges are directed so that
each is directed toward a different node. -/
def Graph.IsBranching (G : Graph V E) (B : Finset E) : Prop :=
  G.IsForest B ∧ ∀ e ∈ B, ∀ f ∈ B, G.front e = G.front f → e = f

/-- The (incidence) vector of a set of edges `B` (§5, p. 235): the 0–1 vector with `x e = 1`
exactly when `e ∈ B`. -/
def incidenceVector (B : Finset E) : E → ℝ :=
  fun e => if e ∈ B then 1 else 0

end OptimumBranchings.Polytope


