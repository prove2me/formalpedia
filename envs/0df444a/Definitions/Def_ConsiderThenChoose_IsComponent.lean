-- Prove2me | Definitions.Def_ConsiderThenChoose_IsComponent
-- name    : ConsiderThenChoose_IsComponent
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-29T18:31:20.450593+00:00
-- url     : https://prove2.me/theorems/ede5715a-3886-41e9-b888-4d731bce9f4b
-- title:
--   Connected components of $G[S,T]$
-- statement:
--   Let $S \subseteq [N]$, $T \subseteq [K]$, $S' \subseteq [N]$ and $T' \subseteq [K]$. The pair $(S', T')$ is a **connected component** of $G[S,T]$ when
--
--   1. $S' \subseteq S$ and $T' \subseteq T$;
--   2. the induced subgraph $G[S',T']$ is connected (in particular it has at least one vertex);
--   3. no edge of $G[S,T]$ leaves $G[S',T']$: every edge of $G$ from a vertex of $S' \cup T'$ to a vertex of $S \cup T$ ends in $S' \cup T'$.
--
--   This is the paper's notion of a connected component: a set of mutually connected nodes such that no path joins a node outside it to a node inside it. The components of $G[S,T]$ partition the subproblem $(S,T)$ into independent subproblems (Lemma 1 of the paper), which is how the dynamic program decomposes.
--
--   **Formalization Note** Connectedness is Mathlib's `SimpleGraph.Connected` of the induced subgraph, which includes nonemptiness. Connectedness together with condition 3 is exactly maximality among connected vertex sets of $G[S,T]$.
-- source:
--   Aouad, Farias and Levi, Assortment Optimization Under Consider-then-Choose Choice Models, Management Science 67(6) (2021), doi:10.1287/mnsc.2020.3681, §3, footnote 1, p. 12

import Mathlib
import Definitions.Def_ConsiderThenChoose_bipGraph
import Definitions.Def_ConsiderThenChoose_vtx

namespace ConsiderThenChoose

/-- **Connected component of `G[S,T]`.** Aouad, Farias and Levi, Management Science 67(6)
(2021), doi:10.1287/mnsc.2020.3681, §3, footnote 1, p. 12: "A connected component in a
undirected graph (V,E) is a set of nodes S which are all mutually connected (i.e., between
every two nodes i,j ∈ S, there exists a path formed by edges of E), and there does not exists a
path from a node in V \ S to a node in S."

`IsComponent C S T S' T'` says that the vertex set `vtx S' T'` (products `S'`, types `T'`) is a
connected component of `G[S,T]`:
1. `S' ⊆ S` and `T' ⊆ T`;
2. the induced subgraph `G[S',T']` is connected (in Mathlib, `Connected` includes
   nonemptiness);
3. `vtx S' T'` is closed in `G[S,T]`: every edge of `G` from a vertex of `vtx S' T'` to a
   vertex of `vtx S T` ends in `vtx S' T'`.

**Formalization Note** Connected together with closed is exactly "maximal connected", i.e.
footnote 1's "mutually connected, and no path from outside": a path inside `G[S,T]` that enters
`vtx S' T'` would have to use an edge leaving it. Since `G` has no product–product or type–type
edges, the edges of `G[S',T']` are the pairs `(i,j)` with `i ∈ S'`, `j ∈ T'`, `i ∈ C_j`, which
is the paper's `E_{S',T'}`. -/
def IsComponent {N K : ℕ} (C : Fin K → Finset (Fin N)) (S : Finset (Fin N)) (T : Finset (Fin K))
    (S' : Finset (Fin N)) (T' : Finset (Fin K)) : Prop :=
  S' ⊆ S ∧ T' ⊆ T ∧ ((bipGraph C).induce (vtx S' T')).Connected ∧
    ∀ v ∈ vtx S' T', ∀ w ∈ vtx S T, (bipGraph C).Adj v w → w ∈ vtx S' T'

end ConsiderThenChoose


