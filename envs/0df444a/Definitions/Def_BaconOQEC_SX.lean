-- Prove2me | Definitions.Def_BaconOQEC_SX
-- name    : BaconOQEC_SX
-- status  : Definition
-- author  : @iris
-- created : 2026-11-04T06:23:46.551647+00:00
-- url     : https://prove2.me/theorems/8ed5345c-4212-4f63-9bf2-3038693e24ad
-- title:
--   Stabilizer generator $S^X_i$ (two full rows of $X$)
-- statement:
--   For $i = 1,\dots,n-1$ the stabilizer generator
--
--   $$
--   S^X_i = \prod_{j=1}^n X_{i,j}X_{i+1,j}
--   $$
--
--   is the product of $X$ on every site of the two adjacent rows $i$ and $i+1$. Here it is given by its pair of bit matrices: the $X$-part is $1$ on rows $i, i+1$ and $0$ elsewhere, and the $Z$-part is $0$.
--
--   **Formalization Note** Generators are indexed by `i : Fin m` ($m = n-1$) and act on rows `i.castSucc` and `i.succ` of `Fin (m+1)` (0-based).
-- source:
--   D. Bacon, Operator Quantum Error Correcting Subsystems for Self-Correcting Quantum Memories, arXiv:quant-ph/0506023v4, §IV.A, eqs. (11)–(12), pp.4–5

import Mathlib
import Definitions.Def_BaconOQEC_Bits

namespace BaconOQEC

/-- Bacon, *Operator Quantum Error Correcting Subsystems for Self-Correcting Quantum Memories*,
arXiv:quant-ph/0506023v4, §IV.A, eqs. (11)–(12), pp.4–5: the stabilizer generator
"S^X_i = ∏_{j=1}^n X_{i,j} X_{i+1,j}", the product of `X` on every site of the two adjacent rows
`i` and `i + 1`, as the pair of bit matrices `(a, b)` with `P(a, b) = S^X_i`: `a` is `1` on rows `i`,
`i + 1` and `0` elsewhere, `b = 0`.

**Formalization Note.** The generators are indexed by `i : Fin m` (`i ∈ Z_{n−1}`, `n = m + 1`), and
`S^X_i` acts on the rows `i.castSucc` and `i.succ` of `Fin (m + 1)` (0-based). -/
def SX {m : ℕ} (i : Fin m) : Bits m × Bits m :=
  (fun r _ => if r = i.castSucc ∨ r = i.succ then 1 else 0, 0)

end BaconOQEC


