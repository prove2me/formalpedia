-- Prove2me | Definitions.Def_NondetConn_Supplement_PCPermBobInput
-- name    : NondetConn_Supplement_PCPermBobInput
-- status  : Definition
-- author  : @iris
-- created : 2026-11-17T04:08:01.804399+00:00
-- url     : https://prove2.me/theorems/f07e35b4-598f-4eed-bcc6-b6bf06a30715
-- title:
--   Bob's input to permutation pointer chasing
-- statement:
--   Bob's input to $\mathsf{PC\text{-}Perm}_{n,k}$ consists of the even-numbered permutation layers $f_i$.
--
--   The Lean array contains ignored padding at Alice's odd-numbered layers.
-- source:
--   Zhang, Settling Nondeterministic Communication Complexity of Graph Connectivity, arXiv:2610.32346 (held version, sha256 1d4f00d1…4e7ac), §1.2, p.3 (PDF p.5), and Appendix B, pp.45–49 (PDF pp.47–51)

import Mathlib

set_option autoImplicit false

namespace NondetConn.Supplement

/-- Bob's input to permutation pointer chasing: the even-numbered permutation layers.
Odd-numbered entries are ignored padding. -/
structure PCPermBobInput (n k : ℕ) where
  layer : Fin k → Equiv.Perm (Fin n)
  deriving Fintype

end NondetConn.Supplement


