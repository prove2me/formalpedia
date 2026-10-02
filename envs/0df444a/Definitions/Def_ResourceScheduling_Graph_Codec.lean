-- Prove2me | Definitions.Def_ResourceScheduling_Graph_Codec
-- name    : ResourceScheduling_Graph_Codec
-- status  : Definition
-- author  : @arexychen
-- created : 2026-10-02T05:27:37.959743+00:00
-- url     : https://prove2.me/theorems/961fa293-fdb6-41b7-bb5b-e140a947e349
-- title:
--   A parser for separator-terminated unary codes
-- statement:
--   The alphabet and unary convention are those of the scheduling mission: $u(n)=1^n0$, where $0$ is the separator. The total function `readUnary` scans one such prefix and returns its natural number and the unconsumed suffix, or fails if no separator is present. The function `encNatList` concatenates the original unary codes of a finite list of natural numbers. These definitions prepare the parsing and injectivity layer for reductions on all input strings. No correctness or time-complexity theorem is assumed here.
-- source:
--   New elementary encoding lemma for the exact Prove2Me ResourceScheduling.Graph encodings (ResourceScheduling_Graph_Complexity, ResourceScheduling_Graph_GraphPartition, ResourceScheduling_Graph_ResDot11, ResourceScheduling_Graph_Construction). Construction: Blazewicz, Lenstra and Rinnooy Kan, Discrete Applied Mathematics 5 (1983), p. 15, Theorems 2-3, https://doi.org/10.1016/0166-218X(83)90012-4; author preprint https://ir.cwi.nl/pub/9642/9642D.pdf, printed pp. 5-6. The numerical encoding bound and parser lemmas are auxiliary results for the platform encoding, not numbered claims of the paper.

import Definitions.Def_ResourceScheduling_Graph_Complexity

set_option autoImplicit false

namespace ResourceScheduling.Graph

/-- Read one separator-terminated unary natural. A missing separator is rejected. -/
def readUnary : List Letter → Option (ℕ × List Letter)
  | [] => none
  | Letter.sep :: xs => some (0, xs)
  | Letter.one :: xs => do
    let (n, rest) ← readUnary xs
    return (n + 1, rest)

/-- Encode a finite list of naturals using the mission's original unary convention. -/
def encNatList (xs : List ℕ) : List Letter := xs.flatMap unary

end ResourceScheduling.Graph


