-- Prove2me | Definitions.Def_MetricTSPSublinear_RPoint
-- name    : MetricTSPSublinear_RPoint
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T22:23:46.907475+00:00
-- url     : https://prove2.me/theorems/587cd773-ffc4-4c32-b37d-755696f5efe1
-- title:
--   Points of the continuous extension $R(T)$ of a tree
-- statement:
--   For a tree $T$, the **continuous extension** $R(T)$ consists of the vertices of $T$ together with the interior points of its edges: for an edge $e=(u,v)$ and $\alpha\in(0,1)$ there is an interior point $p$ of $e$ with $d_{R(T)}(u,p)=\alpha\,w_T(e)$ and $d_{R(T)}(v,p)=(1-\alpha)\,w_T(e)$.
--
--   $R(T)$ carries the subtrees of Lemma 3.1 and the map $q$ of Lemma 5.3.
--
--   **Formalization Note.** A point is a node, or a pair (edge $\{a,b\}$ with $a<b$, $\alpha\in(0,1)$) standing for the point at fraction $\alpha$ from $a$; each point has exactly one representative. Distances are given by `rdist`.
-- source:
--   A. Azarmehr, S. Behnezhad, Metric TSP in Sublinear Time: Breaking Two Approximation, arXiv:2611.04283 (held version, sha256 a86ea2397da2e82c8f8baada200e333f32a133395de02943b1fce22946e4a745), https://arxiv.org/abs/2611.04283, §3, p.10 (PDF p.12)

import Mathlib

namespace MetricTSPSublinear

/-- **The points of the continuous extension `R(T)` of a tree.**
Azarmehr, Behnezhad, *Metric TSP in Sublinear Time: Breaking Two Approximation*, arXiv:2611.04283 (held version,
sha256 a86ea239…), §3, p.10 (PDF p.12): "The points in R(T) consist of the vertices of T plus the interior points of
all its edges. That is, for edge e = (u, v) and α ∈ (0, 1), there is an interior point p on e that satisfies
d_{R(T)}(u, p) = α w_T(e) and d_{R(T)}(v, p) = (1 − α) w_T(e)."

A point of `R(G)` for a graph `G` on the nodes `Fin m` is either a node `vtx a`, or an interior point
`inner a b _ _ α _` of an edge `{a, b}` of `G` with `a < b` and `α ∈ (0, 1)`, at fraction `α` of the edge from `a`.

**Formalization Note.** Each point has exactly one representative: an edge is written with its smaller end first,
so the page's point at `α` from `b` is `inner a b _ _ (1 − α) _`. The points carry no weights; the distance is
`rdist`. -/
inductive RPoint {m : ℕ} (G : SimpleGraph (Fin m)) : Type
  /-- The node `a`. -/
  | vtx (a : Fin m)
  /-- The interior point of the edge `{a, b}` (`a < b`) at fraction `α ∈ (0, 1)` from `a`. -/
  | inner (a b : Fin m) (hab : G.Adj a b) (hlt : a < b) (α : ℝ) (hα : 0 < α ∧ α < 1)

end MetricTSPSublinear


