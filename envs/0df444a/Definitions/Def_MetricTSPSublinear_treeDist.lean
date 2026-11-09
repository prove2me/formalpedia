-- Prove2me | Definitions.Def_MetricTSPSublinear_treeDist
-- name    : MetricTSPSublinear_treeDist
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T22:23:57.181598+00:00
-- url     : https://prove2.me/theorems/3983a8cb-5373-4f6b-ad7f-cf8ab136d980
-- title:
--   Distances in a reweighted spanning tree
-- statement:
--   Let $E$ be a spanning tree of the complete graph on $V$ and $w'$ new weights on its edges. For $u,v\in V$, $d_{T'}(u,v)$ is the sum of $w'$ over the edges of the $u$–$v$ path of $E$.
--
--   This is the tree metric of a shortening $T'$ of an MST $T$.
--
--   **Formalization Note.** The edges of the $u$–$v$ path are described as the edges of $E$ whose deletion disconnects $u$ from $v$, which for a tree is exactly the path; no tree hypothesis is needed to state the definition.
-- source:
--   A. Azarmehr, S. Behnezhad, Metric TSP in Sublinear Time: Breaking Two Approximation, arXiv:2611.04283 (held version, sha256 a86ea2397da2e82c8f8baada200e333f32a133395de02943b1fce22946e4a745), https://arxiv.org/abs/2611.04283, §2.1, p.3 (PDF p.5); §3, p.10 (PDF p.12)

import Mathlib

open scoped Classical

namespace MetricTSPSublinear

/-- The edges of a spanning tree `E` on the `u`–`v` path: the edges `e ∈ E` whose deletion disconnects `u` from `v`.
For a tree these are exactly the edges of the unique `u`–`v` path. -/
noncomputable def pathEdges {n : ℕ} (E : Finset (Sym2 (Fin n))) (u v : Fin n) : Finset (Sym2 (Fin n)) :=
  E.filter (fun e => ¬ (SimpleGraph.fromEdgeSet ((E : Set (Sym2 (Fin n))) \ {e})).Reachable u v)

/-- **The tree distance `d_{T′}(u, v)` of a reweighting of a spanning tree.**
Azarmehr, Behnezhad, *Metric TSP in Sublinear Time: Breaking Two Approximation*, arXiv:2611.04283 (held version,
sha256 a86ea239…), §2.1, p.3 (PDF p.5) and §3, p.10 (PDF p.12): "the distance d_T(u, v) is equal to the weight of the
path from u to v in T".

For an edge set `E` (a spanning tree of the complete graph on `Fin n`) and new weights `w'`, `treeDist E w' u v` is
the sum of `w'` over the edges of the `u`–`v` path of `E`.

**Formalization Note.** The path is described by its edges, as the edges of `E` separating `u` from `v`
(`pathEdges`); this needs no proof that `E` is a tree, and agrees with the unique path when it is one. `u = v` gives
`0`. -/
noncomputable def treeDist {n : ℕ} (E : Finset (Sym2 (Fin n))) (w' : Sym2 (Fin n) → ℝ) (u v : Fin n) : ℝ :=
  ∑ e ∈ pathEdges E u v, w' e

end MetricTSPSublinear


