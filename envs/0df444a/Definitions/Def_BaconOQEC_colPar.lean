-- Prove2me | Definitions.Def_BaconOQEC_colPar
-- name    : BaconOQEC_colPar
-- status  : Definition
-- author  : @iris
-- created : 2026-11-04T06:23:38.102973+00:00
-- url     : https://prove2.me/theorems/857b0fd1-f9ce-485b-acfb-c01f6a75a607
-- title:
--   Column parity $e_j(a)$
-- statement:
--   For a bit matrix $a$ (the $X$-part of a Pauli error $P(a,b)$) and a column $j$, the **error string** entry
--
--   $$
--   e_j(a) = \bigoplus_{i=1}^n a_{i,j}
--   $$
--
--   is the parity of the number of $X$'s in column $j$. As $j$ varies, $e(a)$ is an $n$-bit string.
--
--   **Formalization Note** The sum is taken in `ZMod 2`; columns are 0-based.
-- source:
--   D. Bacon, Operator Quantum Error Correcting Subsystems for Self-Correcting Quantum Memories, arXiv:quant-ph/0506023v4, §IV.C, eq. (20), p.7

import Mathlib
import Definitions.Def_BaconOQEC_Bits

namespace BaconOQEC

/-- Bacon, *Operator Quantum Error Correcting Subsystems for Self-Correcting Quantum Memories*,
arXiv:quant-ph/0506023v4, §IV.C, eq. (20), p.7: the error string
"e_j(a) = ⊕_{i=1}^n a_{i,j}", the parity of the number of `X`'s of `P(a, b)` in column `j`.

**Formalization Note.** Columns are 0-based (`Fin (m + 1)`, `n = m + 1`); the sum is in `ZMod 2`, so
it is the exclusive-or of (20). As a function of `j`, `colPar a` is the `n`-bit string `e(a)`. -/
def colPar {m : ℕ} (a : Bits m) (j : Fin (m + 1)) : ZMod 2 :=
  ∑ i, a i j

end BaconOQEC


