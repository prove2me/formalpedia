-- Prove2me | Definitions.Def_DoublyEffIP_proverInput
-- name    : DoublyEffIP_proverInput
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T17:17:10.303017+00:00
-- url     : https://prove2.me/theorems/5900f7c2-1f32-4926-ad8f-e9fd14fce592
-- title:
--   The prover's input in round $j$
-- statement:
--   In round $j$ the prover's next-message machine is run on the word
--
--   $$
--   \mathrm{pp}\;\cdot\;\lceil x\rceil\;\cdot\;\langle j\rangle\;\cdot\;\lceil(q_0,\dots,q_j)\rceil ,
--   $$
--
--   the public parameters, the input $x$, the round index and the queries received so far, each written in a self-delimiting way. Its output is the answer $a_j=P(x,j,(q_0,\dots,q_j))$.
--
--   The word determines $(\mathrm{pp},x,j,q_0,\dots,q_j)$, so the prover is exactly a next-message function of these arguments.
-- source:
--   Chen–Hong–Kalai–Xi, Towards a Doubly Efficient IP = PSPACE, arXiv:2606.21799 (version of 2026-11-02, sha256 14d170db…), Section 3.4, p.11 (next-message function)

import Mathlib
import Definitions.Def_DoublyEffIP_encBin

set_option autoImplicit false

open OAI.Algorithms.SubexponentialSAT

namespace DoublyEffIP

/-- **The prover's input in round `j`** — the arguments of the next-message function
`a_j := P(x, j, (q_1, …, q_j))` of Chen–Hong–Kalai–Xi, *Towards a Doubly Efficient IP = PSPACE*,
arXiv:2606.21799 (version of 2026-11-02, sha256 14d170db…), Section 3.4, p.11.

The public parameters `pp`, then the input `x`, the round index `j` and the queries received so
far, each self-delimited.

**Formalization Note.** `frame` and `encodeList` (published `SubexponentialSAT`) are
self-delimiting, so the word determines `x`, `j` and the queries once `pp` is known. -/
def proverInput (pp x : List Bool) (j : ℕ) (qs : List (List Bool)) : List Bool :=
  pp ++ Encoding.frame x ++ encBin j ++ Encoding.encodeList id qs

end DoublyEffIP


