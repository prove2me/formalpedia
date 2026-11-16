-- Prove2me | Definitions.Def_QiOPoQ_Supplement_fig4Verify
-- name    : QiOPoQ_Supplement_fig4Verify
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T04:46:39.046211+00:00
-- url     : https://prove2.me/theorems/9cd2fcea-bf5c-42c2-879c-4de87238440d
-- title:
--   Figure 4: the private verifier
-- statement:
--   The verifier of Figure 4 recovers $(b_1,\dots,b_t)$ from the coins $r$ and accepts the response $(b'_1,\dots,b'_t)$ iff $b'_i=b_i$ for every $i\in[t]$.
--
--   **Formalization Note** A response of length different from $t$ does not parse and is rejected; the challenge is not read.
-- source:
--   Gheorghiu, Gupte, Havlíček, Liu, Verifiable Quantum Advantage and Computation via Quantum Circuit Obfuscation, arXiv:2609.40289 (sha256 fe2f9210…), Figure 4, p.17

import Mathlib
import Definitions.Def_QAlgorithms_ClassicalStringComputability

set_option autoImplicit false

namespace QiOPoQ.Supplement

open QAlgorithms.Complexity

/-- **Figure 4, Verify.** Gheorghiu, Gupte, Havlíček, Liu, arXiv:2609.40289 (sha256 fe2f9210…),
Figure 4, p.17: "Verify(1^λ, r, chall, resp): Recover (b_1, . . . , b_t) from r and parse
resp = (b′_1, . . . , b′_t). Accept if b′_i = b_i for every i ∈ [t], and otherwise reject."

`b` is the first `t(λ)` bits of the coins `r` (the layout of `fig4Challenge`); the response is
accepted iff it is exactly the string `b_1 ⋯ b_t`. **Formalization Note.** A response of length
`≠ t` does not parse as `(b′_1, …, b′_t)` and is rejected; the challenge is not used. -/
def fig4Verify (t : ℕ → ℕ) (n : ℕ) (r _chall resp : Str) : Bool :=
  decide (resp = r.take (t n))

end QiOPoQ.Supplement


