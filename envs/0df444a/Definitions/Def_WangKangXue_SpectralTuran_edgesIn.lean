-- Prove2me | Definitions.Def_WangKangXue_SpectralTuran_edgesIn
-- name    : WangKangXue_SpectralTuran_edgesIn
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-29T14:22:14.357875+00:00
-- url     : https://prove2.me/theorems/69bd27ec-284a-4c7a-a4bd-777535c779de
-- title:
--   e(G[S]): the number of edges of G inside a vertex set S
-- statement:
--   Let $G$ be a finite simple graph and $S \subseteq V(G)$. The **induced subgraph** $G[S]$ has vertex set $S$ and all edges of $G$ with both ends in $S$. We write
--   $$
--   e(G[S]) = \#\{uv \in E(G) : u \in S,\ v \in S\}
--   $$
--   for its number of edges; the paper also writes $e(V_i)$ for $e(G[V_i])$.
--
--   This count measures how far a part of a vertex partition is from being independent, and it appears in Lemmas 3.3, 3.6 and 3.9.
-- source:
--   Wang, Kang, Xue, On a conjecture of spectral extremal problems, arXiv:2203.10831v1, p. 2, Section 2 (notation G[S], e(V_i))

import Mathlib

namespace WangKangXue.SpectralTuran

open Classical in
/-- `e(G[S])` (written `e(S)` in the paper): the number of edges of `G` with both endpoints
in the vertex set `S`, i.e. the number of edges of the induced subgraph `G[S]`. -/
noncomputable def edgesIn {V : Type*} [Fintype V] (G : SimpleGraph V) (S : Finset V) : ℕ :=
  (G.edgeFinset.filter (fun e => ∀ v ∈ e, v ∈ S)).card

end WangKangXue.SpectralTuran


