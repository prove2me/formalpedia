-- Prove2me | Definitions.Def_ResourceScheduling_Graph_WordReduction
-- name    : ResourceScheduling_Graph_WordReduction
-- status  : Definition
-- author  : @arexychen
-- created : 2026-10-02T06:05:31.842605+00:00
-- url     : https://prove2.me/theorems/b5d5bdb2-63fb-4fae-98a8-41711bfc1b9f
-- title:
--   A total word transformation for the graph-to-Q2 reduction
-- statement:
--   Define a word transformation $F$ on every string over the scheduling alphabet. If the graph parser returns a graph $G$, let $F$ output the original resource-constrained scheduling encoding of the non-edge construction with speeds $2,1$ and threshold $|V(G)|/3$. If parsing fails, let $F$ output the empty word. This extends the construction from graph instances to all words, as required by the definition of many-one reduction. Semantic correctness and polynomial-time computability are separate theorems.
-- source:
--   New elementary encoding lemma for the exact Prove2Me ResourceScheduling.Graph encodings (ResourceScheduling_Graph_Complexity, ResourceScheduling_Graph_GraphPartition, ResourceScheduling_Graph_ResDot11, ResourceScheduling_Graph_Construction). Construction: Blazewicz, Lenstra and Rinnooy Kan, Discrete Applied Mathematics 5 (1983), p. 15, Theorems 2-3, https://doi.org/10.1016/0166-218X(83)90012-4; author preprint https://ir.cwi.nl/pub/9642/9642D.pdf, printed pp. 5-6. The numerical encoding bound and parser lemmas are auxiliary results for the platform encoding, not numbered claims of the paper.

import Definitions.Def_ResourceScheduling_Graph_Decoder
import Definitions.Def_ResourceScheduling_Graph_Construction

set_option autoImplicit false

namespace ResourceScheduling.Graph

/-- Extend the exact graph-to-schedule construction to all words. Malformed graph codes
are mapped to the empty word, which is not an encoding of a Q2 instance. -/
def reduceWord (w : List Letter) : List Letter :=
  match decodeGraph w with
  | none => []
  | some d => encQ2 (![2, 1], reduce d)

end ResourceScheduling.Graph


