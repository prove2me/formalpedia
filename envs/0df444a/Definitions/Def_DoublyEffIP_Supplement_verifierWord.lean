-- Prove2me | Definitions.Def_DoublyEffIP_Supplement_verifierWord
-- name    : DoublyEffIP_Supplement_verifierWord
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T01:34:00.913006+00:00
-- url     : https://prove2.me/theorems/5844739a-1b04-4b67-ac2f-815a82153c4d
-- title:
--   The verifier's input
-- statement:
--   The verifier machine receives the word made of the queries (its public coins) and the answers, each self-delimited, followed by the public parameters $\mathrm{pp}$. It receives no input $x$.
--
--   **Formalization Note** The public parameters come last, so that the transcript can be read without scanning parameters the verifier-time bounds do not charge for (for instance $k$ in binary).
-- source:
--   Chen–Hong–Kalai–Xi, Towards a Doubly Efficient IP = PSPACE, arXiv:2606.21799 (version of 2026-11-02, sha256 14d170db…), Definition 8, p.11 (the verifier receives no input except the protocol's parameters)

import Mathlib
import Definitions.Def_SubexponentialSAT

set_option autoImplicit false

open OAI.Algorithms.SubexponentialSAT

namespace DoublyEffIP.Supplement

/-- **The verifier's input** — `V[pp]` with its public coins and the answers it received, for the
protocols of Definitions 8 and 9 of Chen–Hong–Kalai–Xi, *Towards a Doubly Efficient IP = PSPACE*, arXiv:2606.21799
(version of 2026-11-02, sha256 14d170db…) (pp.11–12), whose verifier "receives no input (except the
protocol's parameters)".

The queries (the verifier's public random coins) and the answers, each self-delimited, followed by
the public parameters `pp`.

**Formalization Note.** Same data as the published `DoublyEffIP.verifierInput` with `x` empty, with
`pp` placed last, so that reading the transcript does not require scanning parameters (such as `k`
in binary) that the source's verifier-time bounds do not charge for. -/
def verifierWord (pp : List Bool) (qs as : List (List Bool)) : List Bool :=
  Encoding.encodeList id qs ++ Encoding.encodeList id as ++ pp

end DoublyEffIP.Supplement


