-- Prove2me | Definitions.Def_DoublyEffIP_verifierInput
-- name    : DoublyEffIP_verifierInput
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T17:16:01.802368+00:00
-- url     : https://prove2.me/theorems/b046d45a-a6d2-42cd-9ccc-39dede8c213f
-- title:
--   The verifier's input
-- statement:
--   The verifier's decision machine is run on the word
--
--   $$
--   \mathrm{pp}\;\cdot\;\lceil x\rceil\;\cdot\;\lceil(q_1,\dots,q_\ell)\rceil\;\cdot\;\lceil(a_1,\dots,a_\ell)\rceil ,
--   $$
--
--   the public parameters, the input (the paper's $y=x$ for an IP), its public coins and the answers, each written in a self-delimiting way. The word determines all four components.
-- source:
--   Chen–Hong–Kalai–Xi, Towards a Doubly Efficient IP = PSPACE, arXiv:2606.21799 (version of 2026-11-02, sha256 14d170db…), Section 3.4, pp.10–11; Definition 7, p.11

import Mathlib
import Definitions.Def_SubexponentialSAT

set_option autoImplicit false

open OAI.Algorithms.SubexponentialSAT

namespace DoublyEffIP

/-- **The verifier's input** — `V(y; q)[pp]` together with the answers it received, in
Chen–Hong–Kalai–Xi, *Towards a Doubly Efficient IP = PSPACE*, arXiv:2606.21799 (version of
2026-11-02, sha256 14d170db…), Section 3.4, pp.10–11.

The public parameters `pp`, then the input `x` (the paper's `y = x`, Definition 7), the queries
(the verifier's public random coins) and the answers, each self-delimited.

**Formalization Note.** `frame` and `encodeList` (published `SubexponentialSAT`) are
self-delimiting, so the word determines `x`, the queries and the answers once `pp` is known. -/
def verifierInput (pp x : List Bool) (qs as : List (List Bool)) : List Bool :=
  pp ++ Encoding.frame x ++ Encoding.encodeList id qs ++ Encoding.encodeList id as

end DoublyEffIP


