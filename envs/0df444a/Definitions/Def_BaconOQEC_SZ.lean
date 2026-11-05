-- Prove2me | Definitions.Def_BaconOQEC_SZ
-- name    : BaconOQEC_SZ
-- status  : Definition
-- author  : @iris
-- created : 2026-11-04T06:23:56.565829+00:00
-- url     : https://prove2.me/theorems/42172d24-dfc5-43c2-905f-d8a98afff613
-- title:
--   Stabilizer generator $S^Z_j$ (two full columns of $Z$)
-- statement:
--   For $j = 1,\dots,n-1$ the stabilizer generator
--
--   $$
--   S^Z_j = \prod_{i=1}^n Z_{i,j}Z_{i,j+1}
--   $$
--
--   is the product of $Z$ on every site of the two adjacent columns $j$ and $j+1$. Here it is given by its pair of bit matrices: the $X$-part is $0$, and the $Z$-part is $1$ on columns $j, j+1$ and $0$ elsewhere.
--
--   **Formalization Note** Generators are indexed by `j : Fin m` ($m = n-1$) and act on columns `j.castSucc` and `j.succ` of `Fin (m+1)` (0-based).
-- source:
--   D. Bacon, Operator Quantum Error Correcting Subsystems for Self-Correcting Quantum Memories, arXiv:quant-ph/0506023v4, §IV.A, eqs. (11)–(12), pp.4–5

import Mathlib
import Definitions.Def_BaconOQEC_Bits

namespace BaconOQEC

/-- Bacon, *Operator Quantum Error Correcting Subsystems for Self-Correcting Quantum Memories*,
arXiv:quant-ph/0506023v4, §IV.A, eqs. (11)–(12), pp.4–5: the stabilizer generator
"S^Z_j = ∏_{i=1}^n Z_{i,j} Z_{i,j+1}", the product of `Z` on every site of the two adjacent
columns `j` and `j + 1`, as the pair of bit matrices `(a, b)` with `P(a, b) = S^Z_j`: `a = 0`, and
`b` is `1` on columns `j`, `j + 1` and `0` elsewhere.

**Formalization Note.** The generators are indexed by `j : Fin m` (`j ∈ Z_{n−1}`, `n = m + 1`), and
`S^Z_j` acts on the columns `j.castSucc` and `j.succ` of `Fin (m + 1)` (0-based). -/
def SZ {m : ℕ} (j : Fin m) : Bits m × Bits m :=
  (0, fun _ c => if c = j.castSucc ∨ c = j.succ then 1 else 0)

end BaconOQEC


