-- Prove2me | Definitions.Def_ARTreeCover_WForest
-- name    : ARTreeCover_WForest
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T20:54:17.181215+00:00
-- url     : https://prove2.me/theorems/12d97337-1925-45be-9405-60994390dab9
-- title:
--   Weighted forests with weights in $(0,\infty]$; spanning forests
-- statement:
--   A **weighted forest** on $V$ is an acyclic graph on $V$ with a weight in $(0,\infty]$ on each edge. Its distance $d_F(u,v)$ is the infimum over walks of the sum of the edge weights, which is the weight of the unique path, and $\infty$ when $u,v$ lie in different trees. The value $\infty$ is allowed for edges that do not exist in the graph being covered (footnote 13, p.28).
--
--   $F$ is **spanning** for $G$ if every edge of $F$ is an edge of $G$ and carries $G$'s weight.
--
--   **Formalization Note** A forest is a graph on all of $V$: a vertex outside the paper's $V(F)$ is an isolated vertex, which changes no distance between distinct vertices and gives $d_F(u,u)=0$, as the paper assumes (p.31).
-- source:
--   Elkin, Shabat, Near-Optimal Almost-Ramsey Spanning Tree Covers, via Layered Clusterings, STOC 2027 submission (manuscript sha256 8ce8e6be…), Definition 14 and footnote 13, pp.28–29 (PDF pp.31–32)

import Mathlib
import Definitions.Def_ARTreeCover_WGraph

open scoped ENNReal

namespace ARTreeCover

/-- A weighted forest on the vertex set `V`, with edge weights in `(0, ∞]`.

Elkin, Shabat, *Near-Optimal Almost-Ramsey Spanning Tree Covers, via Layered Clusterings*,
STOC 2027 submission (manuscript sha256 8ce8e6be…), Definition 14 and footnote 13, p.28
(PDF p.31): "a forest cover is a set F of weighted forests, where V(F) ⊆ V"; "In case of a forest
edge that does not exist in the input graph G, we allow any positive edge weight, including ∞".

**Formalization Note.** A forest is a graph on all of `V`: a vertex of `V` outside the paper's
`V(F)` is an isolated vertex. This changes no distance between two distinct vertices and gives
`d_F(u, u) = 0`, which the paper assumes (p.31). Weights are in `ℝ≥0∞`, positive on edges. -/
structure WForest (V : Type) where
  /-- The edge set of the forest. -/
  graph : SimpleGraph V
  /-- The graph has no cycle. -/
  acyclic : graph.IsAcyclic
  /-- Edge weights in `[0, ∞]`; only their values on edges matter. -/
  w : Sym2 V → ℝ≥0∞
  /-- Weights are positive (possibly `∞`) on edges. -/
  w_pos : ∀ e ∈ graph.edgeSet, 0 < w e

namespace WForest

variable {V : Type}

/-- The distance `d_F(u, v) ∈ [0, ∞]` in the weighted forest: the infimum over walks of the sum
of the edge weights (the weight of the unique path), `∞` if `u`, `v` are in different trees. -/
noncomputable def dist (F : WForest V) (u v : V) : ℝ≥0∞ :=
  ⨅ p : F.graph.Walk u v, (p.edges.map F.w).sum

/-- `F` is a spanning forest of `G` (p.29, PDF p.32: "an important special case is when they are
sub-graphs, i.e., E(F) ⊆ E"): every edge of `F` is an edge of `G` and carries `G`'s weight. -/
def IsSpanning (G : WGraph V) (F : WForest V) : Prop :=
  F.graph ≤ G.graph ∧ ∀ e ∈ F.graph.edgeSet, F.w e = ENNReal.ofReal (G.w e)

end WForest

end ARTreeCover


