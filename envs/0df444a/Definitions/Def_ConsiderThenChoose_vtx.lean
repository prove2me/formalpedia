-- Prove2me | Definitions.Def_ConsiderThenChoose_vtx
-- name    : ConsiderThenChoose_vtx
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-29T18:30:50.027026+00:00
-- url     : https://prove2.me/theorems/52461049-0f0a-4b37-9893-02f45916943d
-- title:
--   Vertex set of the subgraph $G[S,T]$
-- statement:
--   For a set of products $S \subseteq [N]$ and a set of customer types $T \subseteq [K]$, the **subproblem** $(S,T)$ asks for the best assortment within $S$ for the customers of $T$. Its graph is the induced subgraph
--
--   $$
--   G[S,T] = (S, T, E_{S,T}), \qquad E_{S,T} = \{(i,j) \in E : i \in S,\ j \in T\},
--   $$
--
--   whose vertices are the products of $S$ and the types of $T$.
--
--   This definition is the vertex set of $G[S,T]$: the product vertices of $S$ together with the type vertices of $T$. The subgraph $G[S,T]$ itself is the subgraph of $G$ induced on it.
--
--   **Formalization Note** `vtx S T` is the subset `inl '' S ∪ inr '' T` of `Fin N ⊕ Fin K`; the paper's $G[S,T]$ is `(bipGraph C).induce (vtx S T)`.
-- source:
--   Aouad, Farias and Levi, Assortment Optimization Under Consider-then-Choose Choice Models, Management Science 67(6) (2021), doi:10.1287/mnsc.2020.3681, §3 "Graph Representation", p. 11

import Mathlib

namespace ConsiderThenChoose

/-- **The vertex set of the subgraph `G[S,T]`.** Aouad, Farias and Levi, Management Science
67(6) (2021), doi:10.1287/mnsc.2020.3681, §3 "Graph Representation", unnumbered, p. 11:
"G[S,T] = (S,T,E_{S,T}), where E_{S,T} = {(i,j) ∈ E : i ∈ S and j ∈ T}".

`vtx S T` is the set of product vertices in `S` together with the type vertices in `T`. The
subgraph `G[S,T]` of the paper is `(bipGraph C).induce (vtx S T)`. -/
def vtx {N K : ℕ} (S : Finset (Fin N)) (T : Finset (Fin K)) : Set (Fin N ⊕ Fin K) :=
  Sum.inl '' (S : Set (Fin N)) ∪ Sum.inr '' (T : Set (Fin K))

end ConsiderThenChoose


