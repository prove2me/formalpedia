-- Prove2me | Definitions.Def_RobertsonSeymour1991_GM10_Minimax_CompleteHypergraph
-- name    : RobertsonSeymour1991_GM10_Minimax_CompleteHypergraph
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-06T14:44:47.739133+00:00
-- url     : https://prove2.me/theorems/827adec4-1209-4dd3-a6e7-b5f92f51a58d
-- title:
--   (4.4), p. 166 — the complete graph K_n as a hypergraph
-- statement:
--   For $n\ge0$, $K_n$ is the complete graph on $n$ vertices, regarded as a hypergraph: its vertex set is $\{0,\dots,n-1\}$, it has one edge for each unordered pair of distinct vertices, and that edge is incident exactly with its two ends.
--
--   It is the example of (4.4), whose tangle number and branch-width are both $\lceil 2n/3\rceil$.
--
--   **Formalization Note** The edge type is the edge set of the complete simple graph on `Fin n` (unordered pairs of distinct vertices), and an edge is incident with $v$ when $v$ belongs to the pair.
-- source:
--   Robertson, Seymour, Graph Minors. X. Obstructions to Tree-Decomposition, J. Combin. Theory Ser. B 52 (1991), p. 166, (4.4)

import Mathlib
import Definitions.Def_RobertsonSeymour1991_GM10_Minimax_Hypergraph

namespace RobertsonSeymour1991.GM10.Minimax

/-- p. 166: the complete graph `K_n` as a hypergraph: vertex set `Fin n`, one edge for each unordered
pair of distinct vertices (the edge set of the complete simple graph), incident with its two ends. -/
def completeHypergraph (n : ℕ) : Hypergraph (Fin n) (⊤ : SimpleGraph (Fin n)).edgeSet :=
  ⟨fun e v => v ∈ (e : Sym2 (Fin n))⟩

end RobertsonSeymour1991.GM10.Minimax


