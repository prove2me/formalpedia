-- Prove2me | Definitions.Def_EulerSparsify_DiGraph
-- name    : EulerSparsify_DiGraph
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T12:31:29.61356+00:00
-- url     : https://prove2.me/theorems/8460f74f-3430-4242-8b5f-c94397ffb1ed
-- title:
--   Weighted directed multigraph $\vec G=(V,E,w)$ (head = source)
-- statement:
--   A **weighted directed graph** $\vec G=(V,E,w)$ on a finite vertex set $V$ and a finite edge set $E$ is given by two endpoint maps $h,t:E\to V$ and weights $w\in\mathbb R^E$. Following the paper, $h(e)$ is the **head**, which is the *source* of $e$, and $t(e)$ is the **tail**, its *target* (the paper notes in a footnote that this differs from the usual convention).
--
--   The same data also describe the undirected graph $G=\mathrm{und}(\vec G)$: it has the same edges and weights, and only the matrices attached to it differ (the Laplacian $L_G$ versus the directed Laplacian $\vec L_{\vec G}$). The helper `withWeights` keeps vertices, edges and endpoints and replaces the weights, which is how a reweighting of $\vec G$ is described.
--
--   **Formalization Note** Edges are labelled, so parallel edges and self-loops can be represented; each statement of the mission says which it allows. Nonnegativity or positivity of the weights is a hypothesis of each statement, not part of the structure.
-- source:
--   Peng, Sachdeva, Zhang, Zhao, Nested Effective Resistance Partitions and Eulerian Sparsification, STOC 2027 submission (manuscript sha256 0cdf0d3973c1d2c682db79c667cac6e49bab79e8912a5fc379a98fe0aece077d), §3, Graphs, pp.8–9 (PDF pp.10–11), footnote 1

import Mathlib

namespace EulerSparsify

/-- **Weighted directed multigraph** (§3, "Graphs", p.8, PDF p.10).
Peng, Sachdeva, Zhang, Zhao, *Nested Effective Resistance Partitions and Eulerian
Sparsification*, STOC 2027 submission (manuscript sha256 0cdf0d39…), §3, pp.8–9 (PDF pp.10–11):
"⃗G = (V, E, w) … weights w ∈ ℝ^E_{≥0}"; "We use h(e) = u for the head (source) and t(e) = v for the
tail (target) of a directed edge e = (u, v)."

A graph on vertex type `V` with edge type `E` is given by the two endpoint maps `head`, `tail` and
the weights `w`. The same structure is used for an undirected graph: `G = und(⃗G)` keeps the edge set
and the weights, and only its matrices change (`DiGraph.lap` versus `DiGraph.dirLap`).

**Formalization Note.**
* Head = source, tail = target, as in the paper's footnote 1 (p.8), which says this differs from the
  usual convention.
* Edges are labelled, so parallel edges and self-loops can be represented; each statement says which
  of them it allows.
* Nonnegativity (or positivity) of the weights is a hypothesis of each statement, not a field, so
  that reweighting is a plain function. -/
structure DiGraph (V E : Type) where
  /-- the head `h(e)`, which is the source of `e` -/
  head : E → V
  /-- the tail `t(e)`, which is the target of `e` -/
  tail : E → V
  /-- the edge weights -/
  w : E → ℝ

/-- The graph with the same vertices, edges and endpoints and new weights `w'` (a reweighting). -/
def DiGraph.withWeights {V E : Type} (G : DiGraph V E) (w' : E → ℝ) : DiGraph V E :=
  { head := G.head, tail := G.tail, w := w' }

end EulerSparsify


