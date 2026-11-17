-- Prove2me | Definitions.Def_AvgCaseTI_Supplement_Ls
-- name    : AvgCaseTI_Supplement_Ls
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T11:33:13.691409+00:00
-- url     : https://prove2.me/theorems/fd903c46-f10e-40b8-8e4a-be8b395da096
-- title:
--   The enumeration bound $L_s=24(n+1)^{s+1}$
-- statement:
--   For a positive integer $s$ and $n$, the enumeration bound of the algorithm $\mathcal A_s$ is
--   $$
--   L_s:=\lceil 24(n+1)^{s+1}\rceil=24(n+1)^{s+1}.
--   $$
--   A successful run of $\mathcal A_s$ outputs at most $2L_s$ orthogonal isomorphisms (Theorem 5.6).
-- source:
--   Li, Li, Qiao, Tao, Wang, On the average-case complexity landscape for Tensor-Isomorphism-complete problems over finite fields, arXiv:2604.00591 (held version sha256 baf552e1…), Eq. (32), p.32 (PDF p.34)

import Mathlib

set_option autoImplicit false

namespace AvgCaseTI.Supplement

/-- **The enumeration bound `L_s = 24 (n + 1)^{s+1}`**, Eq. (32), p.32 (PDF p.34):
"Fix a positive integer s and choose L_s := ⌈24(n + 1)^{s+1}⌉".

**Formalization Note.** `24(n + 1)^{s+1}` is an integer, so the ceiling is the identity. -/
def Ls (n s : ℕ) : ℕ := 24 * (n + 1) ^ (s + 1)

end AvgCaseTI.Supplement


