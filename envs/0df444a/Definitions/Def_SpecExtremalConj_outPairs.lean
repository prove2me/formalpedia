-- Prove2me | Definitions.Def_SpecExtremalConj_outPairs
-- name    : SpecExtremalConj_outPairs
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-30T01:10:04.503585+00:00
-- url     : https://prove2.me/theorems/1cfb0d7e-494a-407d-b70d-b8764d2480f5
-- title:
--   Number of edges $e(G_{out})$ of the missing crossing pairs
-- statement:
--   Let $G$ be a graph with a partition $V(G)=V_1\cup\dots\cup V_r$, $|V_i|=n_i$, and let $K=K_r(n_1,\dots,n_r)$ be the complete $r$-partite graph on $V_1,\dots,V_r$. The graph $G_{out}$ has vertex set $V(G)$ and edge set $E(K)\setminus E(G)$, so
--
--   $$e(G_{out})=|\{\{u,v\}: u,v \text{ in different parts},\ uv\notin E(G)\}|.$$
--
--   Together with $G_{in}=\bigcup_i G[V_i]$ it measures how far $G$ is from $K$: $e(G)=e(K)+e(G_{in})-e(G_{out})$.
-- source:
--   Wang, Kang, Xue, On a conjecture of spectral extremal problems, arXiv:2203.10831v1, §3, p. 12 (unnumbered, before Lemma 3.9: "K = K_r(n_1, n_2, …, n_r) … G_out … E(G_out) = E(K) \ E(G)")

import Mathlib
open Finset SimpleGraph

namespace SpecExtremalConj

/-- **e(G_out), the missing crossing pairs.** Wang, Kang, Xue, *On a conjecture of spectral extremal problems*, arXiv:2203.10831v1, §3, p. 12 (unnumbered, just before Lemma 3.9):
"let |V_i| = n_i, K = K_r(n_1, n_2, …, n_r) be the complete r-partite graph on V_1, V_2, …, V_r,
and G_out be the graph with V(G_out) = V(G) and E(G_out) = E(K) \ E(G)."

`outPairs G P` is the number of unordered pairs `{u, v}` with `u, v` in different parts of `P`
(an edge of `K`) that are not edges of `G`; this is e(G_out).

**Formalization Note.** Pairs are elements of `Sym2 V`; a pair with ends in different parts is
automatically not a loop. Decidability is classical. -/
noncomputable def outPairs {V : Type*} [Fintype V] [DecidableEq V] {r : ℕ} (G : SimpleGraph V)
    (P : V → Fin r) : ℕ := by
  classical
  exact #{e : Sym2 V | (∃ u ∈ e, ∃ v ∈ e, P u ≠ P v) ∧ e ∉ G.edgeSet}

end SpecExtremalConj


