-- Prove2me | Definitions.Def_SpecExtremalConj_edgesIn
-- name    : SpecExtremalConj_edgesIn
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-30T01:08:49.337657+00:00
-- url     : https://prove2.me/theorems/8e616369-498f-4774-883a-8b1b2d72691b
-- title:
--   Number of edges $e(G[S])$ inside a vertex set
-- statement:
--   For a graph $G$ and a set $S$ of vertices, $G[S]$ is the subgraph induced by $S$: its vertex set is $S$ and its edges are the edges of $G$ with both ends in $S$. The number
--
--   $$e(G[S])=|\{uv\in E(G): u,v\in S\}|$$
--
--   is the number of edges of $G$ inside $S$. The paper writes $e(V_i)$ and $e(G[V_i])$ for this number.
-- source:
--   Wang, Kang, Xue, On a conjecture of spectral extremal problems, arXiv:2203.10831v1, §2, p. 2 (G[S]) and Lemmas 3.3, 3.5, 3.6

import Mathlib
open Finset SimpleGraph

namespace SpecExtremalConj

/-- **e(G[S]), the number of edges inside S.** Wang, Kang, Xue, *On a conjecture of spectral extremal problems*, arXiv:2203.10831v1, §2, p. 2 (unnumbered): "Denote by G[S] the
graph induced by S whose vertex set is S and whose edge set consists of all edges of G which have
both ends in S". The paper writes e(V_i) and e(G[V_i]) for the same number.

`edgesIn G S` is the number of edges of `G` with both ends in the finite set `S`.

**Formalization Note.** Decidability of the filter is classical. -/
noncomputable def edgesIn {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    [DecidableRel G.Adj] (S : Finset V) : ℕ := by
  classical
  exact #{e ∈ G.edgeFinset | ∀ v ∈ e, v ∈ S}

end SpecExtremalConj


