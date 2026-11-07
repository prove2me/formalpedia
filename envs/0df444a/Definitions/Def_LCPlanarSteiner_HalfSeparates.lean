-- Prove2me | Definitions.Def_LCPlanarSteiner_HalfSeparates
-- name    : LCPlanarSteiner_HalfSeparates
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T17:02:21.843407+00:00
-- url     : https://prove2.me/theorems/4fc43cc0-27da-4d29-809e-f8a67220d5e1
-- title:
--   Deletion leaves components of at most half the total weight
-- statement:
--   Let $G$ be a graph with vertex weights $w \ge 0$ and $X$ a set of vertices. Deleting $X$ **leaves components of at most half the total weight** when every connected component $K$ of $G - X$ satisfies
--   $$
--   \sum_{v \in K} w(v) \le \frac{1}{2} \sum_{v} w(v),
--   $$
--   where the right-hand sum is over all vertices, the deleted ones included.
--
--   This is the balance property of the tree-path separator.
--
--   **Formalization Note** $G - X$ keeps all vertices but deletes the edges touching $X$; the component of $u \notin X$ is the set of vertices $v \notin X$ reachable from $u$.
-- source:
--   Mahboub, Rahgoshay, Nearly Exact Length Bounds for Directed Steiner Tree and Forest in Planar Graphs, STOC 2027 submission (manuscript sha256 5af18346c1fe696ca8ed57aa7736510e10e27188695bb15edcbe662315790dda), Lemma 3.1, p.5

import Mathlib

namespace LCPlanarSteiner

/-- **Deleting `X` leaves components of at most half the total weight.**
Mahboub, Rahgoshay, *Nearly Exact Length Bounds for Directed Steiner Tree and Forest in Planar
Graphs*, STOC 2027 submission (manuscript sha256 5af18346…), Lemma 3.1, p.5: "whose deletion leaves weak components of at most half the total weight".

`delVerts G X` is `G` with the vertices of `X` deleted (they become isolated). `HalfSeparates G X w`
says that for every vertex `u ∉ X`, the total weight of the connected component of `u` in
`G − X` is at most half of the total weight `Σ_v w(v)` of all vertices (deleted ones included).

**Formalization Note.** The component of `u` is the set of `v ∉ X` reachable from `u` in
`delVerts G X`. The graph is undirected, so components are the paper's weak components. -/
def delVerts {V : Type} (G : SimpleGraph V) (X : Set V) : SimpleGraph V :=
  SimpleGraph.fromRel fun u v => G.Adj u v ∧ u ∉ X ∧ v ∉ X

open Classical in
/-- Every component of `G − X` has weight at most half the total weight. -/
noncomputable def HalfSeparates {V : Type} [Fintype V] (G : SimpleGraph V) (X : Set V)
    (w : V → ℚ) : Prop :=
  ∀ u, u ∉ X →
    ∑ v ∈ Finset.univ.filter (fun v => v ∉ X ∧ (delVerts G X).Reachable u v), w v ≤
      (∑ v, w v) / 2

end LCPlanarSteiner


