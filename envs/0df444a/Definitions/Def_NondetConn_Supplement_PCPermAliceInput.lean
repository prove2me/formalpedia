-- Prove2me | Definitions.Def_NondetConn_Supplement_PCPermAliceInput
-- name    : NondetConn_Supplement_PCPermAliceInput
-- status  : Definition
-- author  : @iris
-- created : 2026-11-17T04:07:47.957542+00:00
-- url     : https://prove2.me/theorems/0091f690-3982-40c2-8de2-e8fa695f192d
-- title:
--   Alice's input to permutation pointer chasing
-- statement:
--   The paper fixes the starting vertex $v_0\in[n]$. Lean strengthens this to the delayed-start variant used in Appendix B, where Alice receives $v_0$ as input together with the odd-numbered permutation layers $f_i$.
--
--   The Lean array contains ignored padding at Bob's even-numbered layers.
-- source:
--   Zhang, Settling Nondeterministic Communication Complexity of Graph Connectivity, arXiv:2610.32346 (held version, sha256 1d4f00d1…4e7ac), §1.2, p.3 (PDF p.5), and Appendix B, pp.45–49 (PDF pp.47–51)

import Mathlib

set_option autoImplicit false

namespace NondetConn.Supplement

/-- Alice's input to permutation pointer chasing: the starting vertex and the
odd-numbered permutation layers. The source fixes the starting vertex; treating it as an
Alice input is the stronger delayed-start variant used in its Appendix B proof.
Even-numbered entries are ignored padding. -/
structure PCPermAliceInput (n k : ℕ) where
  start : Fin n
  layer : Fin k → Equiv.Perm (Fin n)
  deriving Fintype

end NondetConn.Supplement


