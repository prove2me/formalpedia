-- Prove2me | Definitions.Def_ARTreeCover_WGraph
-- name    : ARTreeCover_WGraph
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T20:51:53.924195+00:00
-- url     : https://prove2.me/theorems/fa64db42-dbe1-4e92-9d05-a383ede235a8
-- title:
--   Undirected weighted graphs, $d_G$ and $d_{G[S]}$ with values in $[0,\infty]$
-- statement:
--   A **weighted graph** $G=(V,E,w)$ is an undirected simple graph with a positive weight on each edge. The **distance** $d_G(u,v)\in[0,\infty]$ is the infimum, over all walks from $u$ to $v$, of the sum of the edge weights along the walk, with $d_G(u,v)=\infty$ when no walk exists. For a vertex set $S$, the distance $d_{G[S]}(u,v)$ in the induced graph is the same infimum over walks all of whose vertices lie in $S$, and it is $\infty$ when $u\notin S$ or $v\notin S$.
--
--   Every other notion of the mission is measured against these two distances. Graphs need not be connected.
--
--   **Formalization Note** The edge set is a `SimpleGraph`; the weight is a real function on unordered pairs, constrained only on edges. Since weights are positive, the infimum over walks is the minimum over paths.
-- source:
--   Elkin, Shabat, Near-Optimal Almost-Ramsey Spanning Tree Covers, via Layered Clusterings, STOC 2027 submission (manuscript sha256 8ce8e6be…), §1, p.1 (PDF p.4); §2, p.9 (PDF p.12)

import Mathlib

open scoped ENNReal

namespace ARTreeCover

/-- An undirected weighted graph `G = (V, E, w)` with a positive weight function `w : E → ℝ₊`.

Elkin, Shabat, *Near-Optimal Almost-Ramsey Spanning Tree Covers, via Layered Clusterings*,
STOC 2027 submission (manuscript sha256 8ce8e6be…), §1, p.1 (PDF p.4), and §2, p.9 (PDF p.12):
"Given an n-vertex undirected weighted graph G = (V, E, w), with a positive weight function
w : E → R+"; "all graphs are undirected and weighted".

**Formalization Note.** The edge set is a `SimpleGraph` on the vertex type `V`; the weight is a
function on unordered pairs, constrained (positive) only on edges. Graphs need not be connected. -/
structure WGraph (V : Type) where
  /-- The underlying simple graph `(V, E)`. -/
  graph : SimpleGraph V
  /-- The weight of an unordered pair; only its values on edges matter. -/
  w : Sym2 V → ℝ
  /-- Weights are positive on edges. -/
  w_pos : ∀ e ∈ graph.edgeSet, 0 < w e

namespace WGraph

variable {V : Type}

/-- The weight of a walk: the sum of the weights of its edges (with multiplicity), in `[0, ∞]`. -/
noncomputable def walkWeight (G : WGraph V) {u v : V} (p : G.graph.Walk u v) : ℝ≥0∞ :=
  (p.edges.map fun e => ENNReal.ofReal (G.w e)).sum

/-- The shortest-path distance `d_G(u, v) ∈ [0, ∞]` (§2, p.9: "the weight of the shortest path
between them"): the infimum of the weights of all walks from `u` to `v`, and `∞` when there is
none (`u`, `v` in different components).

**Formalization Note.** The value `∞` across components is the paper's convention for disconnected
graphs (footnote 13, p.28). Since weights are positive, the infimum over walks equals the minimum
over paths. -/
noncomputable def dist (G : WGraph V) (u v : V) : ℝ≥0∞ :=
  ⨅ p : G.graph.Walk u v, G.walkWeight p

/-- The distance `d_{G[S]}(u, v)` in the induced graph `G[S]` (Definition 2, p.9): the infimum of
the weights of the walks from `u` to `v` all of whose vertices lie in `S`. It is `∞` when no such
walk exists, in particular when `u ∉ S` or `v ∉ S`. -/
noncomputable def distIn (G : WGraph V) (S : Set V) (u v : V) : ℝ≥0∞ :=
  ⨅ (p : G.graph.Walk u v) (_ : ∀ x ∈ p.support, x ∈ S), G.walkWeight p

end WGraph

end ARTreeCover


