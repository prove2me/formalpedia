-- Prove2me | Definitions.Def_NondetConn_Supplement_pcPerm
-- name    : NondetConn_Supplement_pcPerm
-- status  : Definition
-- author  : @iris
-- created : 2026-11-17T04:08:28.420258+00:00
-- url     : https://prove2.me/theorems/60c7929b-93ee-4179-9d7d-e5859bacf38f
-- title:
--   Permutation pointer chasing $\mathsf{PC\text{-}Perm}_{n,k}$
-- statement:
--   Starting from $v_0\in[n]$, permutation pointer chasing recursively sets $v_i=f_i(v_{i-1})$ through $k$ alternatingly owned permutation layers and outputs $v_k$:
--   $$
--   \mathsf{PC\text{-}Perm}_{n,k}=f_k\circ\cdots\circ f_1(v_0).
--   $$
--
--   This is the permutation-restricted pointer-chasing problem used in Appendix B.
-- source:
--   Zhang, Settling Nondeterministic Communication Complexity of Graph Connectivity, arXiv:2610.32346 (held version, sha256 1d4f00d1…4e7ac), §1.2, p.3 (PDF p.5), and Appendix B, p.45 (PDF p.47)

import Definitions.Def_NondetConn_Supplement_PCPermAliceInput
import Definitions.Def_NondetConn_Supplement_PCPermBobInput

set_option autoImplicit false

namespace NondetConn.Supplement

/-- Permutation pointer chasing `PC-Perm_{n,k}`: starting at `v₀`, apply the `k`
alternatingly owned permutation layers in order and return the final vertex. -/
def pcPerm (n k : ℕ) (alice : PCPermAliceInput n k) (bob : PCPermBobInput n k) : Fin n :=
  let layer : Fin k → Equiv.Perm (Fin n) :=
    fun i ↦ if Even i.val then alice.layer i else bob.layer i
  (List.ofFn layer).foldl (fun v p ↦ p v) alice.start

end NondetConn.Supplement


