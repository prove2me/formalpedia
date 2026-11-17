-- Prove2me | Definitions.Def_NondetConn_Supplement_bpcPerm
-- name    : NondetConn_Supplement_bpcPerm
-- status  : Definition
-- author  : @iris
-- created : 2026-11-17T04:08:59.566204+00:00
-- url     : https://prove2.me/theorems/24f5ff29-399d-4cc2-a662-2eee814a463a
-- title:
--   Bit permutation pointer chasing $\mathsf{bPC\text{-}Perm}_{n,k}$
-- statement:
--   The bit problem $\mathsf{bPC\text{-}Perm}_{n,k}$ returns the parity of the final vertex $v_k$ of permutation pointer chasing.
--
--   Since the paper labels $[n]$ from $1$ while Lean's `Fin n` is zero-based, Lean returns the parity of `v.val + 1`.
-- source:
--   Zhang, Settling Nondeterministic Communication Complexity of Graph Connectivity, arXiv:2610.32346 (held version, sha256 1d4f00d1…4e7ac), §1.2, p.3 (PDF p.5), and Appendix B, p.45 (PDF p.47)

import Definitions.Def_NondetConn_Supplement_pcPerm

set_option autoImplicit false

namespace NondetConn.Supplement

/-- The bit version `bPC-Perm_{n,k}`: the parity of the final pointer-chasing vertex.
Because `Fin n` is zero-based while the paper's `[n]` is one-based, the returned bit is
the parity of `v.val + 1`. -/
def bpcPerm (n k : ℕ) (alice : PCPermAliceInput n k) (bob : PCPermBobInput n k) : Bool :=
  decide (Odd ((pcPerm n k alice bob).val + 1))

end NondetConn.Supplement


