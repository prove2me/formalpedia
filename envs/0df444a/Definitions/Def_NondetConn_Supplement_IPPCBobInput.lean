-- Prove2me | Definitions.Def_NondetConn_Supplement_IPPCBobInput
-- name    : NondetConn_Supplement_IPPCBobInput
-- status  : Definition
-- author  : @iris
-- created : 2026-11-17T04:06:51.172615+00:00
-- url     : https://prove2.me/theorems/201b74ee-cd98-45b7-83a7-21dcbade76a7
-- title:
--   Bob's input to $\mathsf{IP\circ PC}_{n,r}$
-- statement:
--   Bob's input to $\mathsf{IP\circ PC}_{n,r}$ consists of bit vectors $X,Y\in\{0,1\}^n$ and the permutations $A_i,B_i$ for even paper indices $i\in[r]$.
--
--   Lean stores padded permutation arrays and ignores Bob's entries at odd paper layers.
-- source:
--   Zhang, Settling Nondeterministic Communication Complexity of Graph Connectivity, arXiv:2610.32346 (held version, sha256 1d4f00d1…4e7ac), §1.1, pp.2–3 (PDF pp.4–5), and Theorem 7.1, p.22 (PDF p.24)

import Definitions.Def_NondetConn_Supplement_IPPCAliceInput

set_option autoImplicit false

namespace NondetConn.Supplement

/-- Bob's input to `IP∘PC_{n,r}`: the two bit vectors and the even-numbered permutation
layers. Entries at the other parity are harmless ignored padding. -/
structure IPPCBobInput (n r : ℕ) where
  vectors : (Fin n → Bool) × (Fin n → Bool)
  layers : IPPCAliceInput n r
  deriving Fintype

end NondetConn.Supplement


