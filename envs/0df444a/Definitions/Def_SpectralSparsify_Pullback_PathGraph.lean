-- Prove2me | Definitions.Def_SpectralSparsify_Pullback_PathGraph
-- name    : SpectralSparsify_Pullback_PathGraph
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-07T11:25:33.068383+00:00
-- url     : https://prove2.me/theorems/31b9113c-cf67-470c-928e-ba10266603c8
-- title:
--   The weighted path graph of Lemma 10.3
-- statement:
--   Let $p_0,p_1,\dots,p_k$ be vertices of $V$ and let $w_1,\dots,w_k$ be real numbers. The **weighted path graph** $F$ along $p$ has, for each $i=1,\dots,k$, an edge $\{p_{i-1},p_i\}$ of weight $w_i$, and weight $0$ on every other pair. When the $p_i$ are distinct, $F$ is a path from $p_0$ to $p_k$ and
--   $$x^{T}L_F x=\sum_{i=1}^{k} w_i\,(x(p_i)-x(p_{i-1}))^2 .$$
--
--   This is the graph $F$ of Lemma 10.3, the path inequality used to compare an edge with a path of heavy edges.
--
--   **Formalization Note** The path is a map `p : Fin (k+1) → V` and the weights `wt : Fin k → ℝ`, with the $i$-th edge (0-based) joining `p i.castSucc` and `p i.succ`. The weight on a pair is the sum of the weights of the path edges joining it, so the definition does not itself require `p` to be injective; the statement that uses it does.
-- source:
--   D. A. Spielman, S.-H. Teng, Spectral Sparsification of Graphs, arXiv:0808.4134v3, p. 37, Lemma 10.3

import Mathlib

namespace SpectralSparsify.Pullback

/-- The weighted path graph of Lemma 10.3 (arXiv:0808.4134v3, p. 37): the vertices
`p 0, p 1, …, p k` in order, the `i`-th edge `{p i, p (i+1)}` (`i = 0, …, k-1`) carrying weight
`wt i`, and weight `0` on every other pair. For an injective `p` each edge occurs once. -/
def pathGraph {V : Type*} [DecidableEq V] {k : ℕ} (p : Fin (k + 1) → V) (wt : Fin k → ℝ) :
    V → V → ℝ :=
  fun a b => ∑ i : Fin k,
    if (a = p i.castSucc ∧ b = p i.succ) ∨ (a = p i.succ ∧ b = p i.castSucc) then wt i else 0

end SpectralSparsify.Pullback


