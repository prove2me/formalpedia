-- Prove2me | Definitions.Def_ChvatalPolytopes_SeriesParallel_deleteIdentify
-- name    : ChvatalPolytopes_SeriesParallel_deleteIdentify
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-26T20:24:01.201783+00:00
-- url     : https://prove2.me/theorems/35e22d4f-5c02-434f-baba-383dd83068ca
-- title:
--   Deleting a vertex $u$ and identifying its neighbours $v,w$ (proof of Theorem 7.1, Case 4)
-- statement:
--   Let $G=(V,E)$ be a graph and $u,v,w\in V$ (in the intended use, $u$ has degree two with the non-adjacent neighbours $v\ne w$). The graph $G'$ obtained by **deleting $u$ and identifying $v$ and $w$** has vertex set $V\setminus\{u,w\}$, where $v$ stands for the merged vertex $v\equiv w$. Two distinct vertices $a,b$ of $G'$ are adjacent iff
--   $$
--   ab\in E\quad\text{or}\quad \{a,b\}=\{v,c\}\ \text{with}\ wc\in E .
--   $$
--   Parallel edges created by the identification are merged into one and no loop arises, as all graphs in the paper are simple.
--
--   This is the reduction used in Case 4 of the induction proving Theorem 7.1.
--
--   **Formalization Note** The vertex type is the subtype `{x // x ≠ u ∧ x ≠ w}` and the graph is `SimpleGraph.fromRel` of the relation "adjacent in $G$, or the first vertex is $v$ and the second is adjacent to $w$", which `fromRel` symmetrizes and makes irreflexive.
-- source:
--   Chvátal, On certain polytopes associated with graphs, J. Combin. Theory Ser. B 18 (1975), p. 151, proof of Theorem 7.1, Case 4

import Mathlib

namespace ChvatalPolytopes.SeriesParallel

/-- "Delete `u` and identify its neighbors `v`, `w`" (Chvátal 1975, p. 151, proof of Theorem 7.1,
Case 4). The vertex set of the new graph is `V − {u, w}`; the vertex `v` stands for the merged
vertex `v ≡ w`. Two distinct vertices `a, b` of `V − {u, w}` are adjacent iff they are adjacent in
`G`, or one of them is `v` and the other is adjacent to `w` in `G`. (Parallel edges created by the
identification are merged and no loops arise, as the paper's graphs are simple.) -/
def deleteIdentify {V : Type*} (G : SimpleGraph V) (u v w : V) :
    SimpleGraph {x : V // x ≠ u ∧ x ≠ w} :=
  SimpleGraph.fromRel fun a b => G.Adj a.1 b.1 ∨ (a.1 = v ∧ G.Adj w b.1)

end ChvatalPolytopes.SeriesParallel


