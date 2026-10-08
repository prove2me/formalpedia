-- Prove2me | Definitions.Def_SpectralSparsify_Decomp_cutEdges
-- name    : SpectralSparsify_Decomp_cutEdges
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-07T09:33:37.656134+00:00
-- url     : https://prove2.me/theorems/a173ab25-c0a0-4c5a-aea2-b02af6128fab
-- title:
--   Number of edges |E(S, T)| between two vertex sets (§4, p. 4)
-- statement:
--   Let $G=(V,E)$ be a simple graph and let $S,T\subseteq V$ be disjoint. Then $E(S,T)$ denotes the set of edges of $G$ connecting one vertex of $S$ with one vertex of $T$, and
--   $$|E(S,T)|=\#\{(s,t)\in S\times T : \{s,t\}\in E\}.$$
--
--   This edge count is the numerator of every conductance in the mission: $|E(S,B-S)|$ is the size of the boundary $\partial_B(S)$ of $S$ inside $B$.
--
--   **Formalization Note** `cutEdges G S T` counts the ordered pairs $(s,t)\in S\times T$ with $s$ adjacent to $t$. For disjoint $S$ and $T$, the only case the paper uses, each edge between them is counted exactly once. For overlapping sets the count is still defined but is not the paper's $|E(S,T)|$.
-- source:
--   D. A. Spielman, S.-H. Teng, Spectral Sparsification of Graphs, arXiv:0808.4134v3, p. 4, Section 4 (definition of E(S,T))

import Mathlib

namespace SpectralSparsify.Decomp

/-- `|E(S, T)|` (arXiv:0808.4134v3, §4, p. 4): the number of edges of `G` connecting a vertex of
`S` with a vertex of `T`, counted as the ordered pairs `(s, t) ∈ S × T` with `s ~ t`. For disjoint
`S` and `T` (the only case the paper uses) each such edge is counted exactly once. -/
def cutEdges {V : Type*} (G : SimpleGraph V) [DecidableRel G.Adj] (S T : Finset V) : ℕ :=
  ((S ×ˢ T).filter (fun p => G.Adj p.1 p.2)).card

end SpectralSparsify.Decomp


