-- Prove2me | Definitions.Def_DoublyEffIP_Supplement_proverWord
-- name    : DoublyEffIP_Supplement_proverWord
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T01:33:35.892281+00:00
-- url     : https://prove2.me/theorems/82ceb393-ce9e-490b-b41b-77176d5731e7
-- title:
--   The prover's input in round $j$
-- statement:
--   In round $j$ the prover machine receives the word made of its input $x$, the round index $j$, the queries $q_1,\dots,q_j$ received so far (each self-delimited) and the public parameters $\mathrm{pp}$.
--
--   This carries the arguments of the next-message function $a_j=P(x,j,(q_1,\dots,q_j))$.
--
--   **Formalization Note** The public parameters come last: they contain the description $\langle\Phi\rangle$, which the paper's prover-time bounds do not charge for, so the prover need not scan them to reach $x$ and the queries.
-- source:
--   Chen–Hong–Kalai–Xi, Towards a Doubly Efficient IP = PSPACE, arXiv:2606.21799 (version of 2026-11-02, sha256 14d170db…), Section 3.4, pp.10–11

import Mathlib
import Definitions.Def_DoublyEffIP_encBin
import Definitions.Def_SubexponentialSAT

set_option autoImplicit false

open OAI.Algorithms.SubexponentialSAT

namespace DoublyEffIP.Supplement

/-- **The prover's input in round `j`** — the arguments of the next-message function
`a_j := P(x, j, (q_1, …, q_j))` together with the public parameters `pp`, Chen–Hong–Kalai–Xi, *Towards a Doubly Efficient IP = PSPACE*, arXiv:2606.21799
(version of 2026-11-02, sha256 14d170db…), Section 3.4,
pp.10–11.

The input `x`, the round index `j` and the queries received so far, each self-delimited, followed
by `pp`.

**Formalization Note.** Same data as the published `DoublyEffIP.proverInput`, with `pp` placed last:
the public parameters of Theorems 4 and 7 contain the description `⟨Φ⟩`, which the source's
prover-time bounds do not charge for, so `pp` is placed where the prover need not read it. -/
def proverWord (pp x : List Bool) (j : ℕ) (qs : List (List Bool)) : List Bool :=
  Encoding.frame x ++ encBin j ++ Encoding.encodeList id qs ++ pp

end DoublyEffIP.Supplement


