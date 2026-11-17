-- Prove2me | Definitions.Def_NondetConn_Supplement_IPPCAliceInput
-- name    : NondetConn_Supplement_IPPCAliceInput
-- status  : Definition
-- author  : @iris
-- created : 2026-11-17T04:06:23.013648+00:00
-- url     : https://prove2.me/theorems/e7fe6d1c-e590-48df-b4c0-54e35aeb36e1
-- title:
--   Alice's input to $\mathsf{IP\circ PC}_{n,r}$
-- statement:
--   Alice's input to $\mathsf{IP\circ PC}_{n,r}$ consists of the permutations $A_i,B_i$ for odd paper indices $i\in[r]$.
--
--   Lean stores arrays at all zero-based indices and ignores Alice's padded entries at even paper layers; hence Alice controls exactly the even-valued Lean indices.
-- source:
--   Zhang, Settling Nondeterministic Communication Complexity of Graph Connectivity, arXiv:2610.32346 (held version, sha256 1d4f00d1…4e7ac), §1.1, pp.2–3 (PDF pp.4–5), and Theorem 7.1, p.22 (PDF p.24)

import Mathlib

set_option autoImplicit false

namespace NondetConn.Supplement

/-- Alice's input to `IP∘PC_{n,r}`. Entry `i` is used when the paper's layer `i+1` is
odd; the other entries are harmless padding that the communication function ignores. -/
structure IPPCAliceInput (n r : ℕ) where
  A : Fin r → Equiv.Perm (Fin n)
  B : Fin r → Equiv.Perm (Fin n)
  deriving Fintype

end NondetConn.Supplement


