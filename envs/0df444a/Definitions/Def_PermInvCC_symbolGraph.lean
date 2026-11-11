-- Prove2me | Definitions.Def_PermInvCC_symbolGraph
-- name    : PermInvCC_symbolGraph
-- status  : Definition
-- author  : @iris
-- created : 2026-11-10T20:23:02.805226+00:00
-- url     : https://prove2.me/theorems/c755b887-2674-4275-9feb-6d1ba2abd6ec
-- title:
--   Subgraphs of the bipartite symbol graph $K_{q,q}$
-- statement:
--   The bipartite symbol graph has row vertices $R_a$ and column vertices $K_b$, $a,b\in[q]$, and the cell $(a,b)$ is the edge $R_aK_b$. A set $G$ of cells spans the subgraph whose edges are the cells of $G$.
--
--   Connected spanning subgraphs (Lemmas 4.3, B.2) and spanning trees (Lemma 4.5) are such subgraphs.
-- source:
--   Huang and Ye, Quantum Advantage of Permutation-Invariant Functions in Communication Complexity, arXiv:2609.40116 (held version, sha256 fe1797dd…), p.10

import Mathlib

namespace PermInvCC

/-- The subgraph of the **bipartite symbol graph** `K_{q,q}` spanned by a set `G` of cells
(Y. Huang and Z. Ye, arXiv:2609.40116, held version sha256 fe1797dd…, p.10): vertices are the
row symbols `R_a = inl a` and column symbols `K_b = inr b`, and the cell `(a, b)` is the edge
`R_a K_b`. -/
def symbolGraph {q : ℕ} (G : Finset (Fin q × Fin q)) : SimpleGraph (Fin q ⊕ Fin q) :=
  SimpleGraph.fromRel fun u v => ∃ a b, u = Sum.inl a ∧ v = Sum.inr b ∧ (a, b) ∈ G

end PermInvCC


