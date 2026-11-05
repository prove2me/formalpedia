-- Prove2me | Definitions.Def_BaconOQEC_rowPar
-- name    : BaconOQEC_rowPar
-- status  : Definition
-- author  : @iris
-- created : 2026-11-04T06:23:45.080004+00:00
-- url     : https://prove2.me/theorems/70d91d7a-8646-439c-9fcf-55ae717322fd
-- title:
--   Row parity $f_i(b)$
-- statement:
--   For a bit matrix $b$ (the $Z$-part of a Pauli error $P(a,b)$) and a row $i$, the **error string** entry
--
--   $$
--   f_i(b) = \bigoplus_{j=1}^n b_{i,j}
--   $$
--
--   is the parity of the number of $Z$'s in row $i$. As $i$ varies, $f(b)$ is an $n$-bit string.
--
--   **Formalization Note** The sum is taken in `ZMod 2`; rows are 0-based.
-- source:
--   D. Bacon, Operator Quantum Error Correcting Subsystems for Self-Correcting Quantum Memories, arXiv:quant-ph/0506023v4, §IV.C, eq. (20), p.7

import Mathlib
import Definitions.Def_BaconOQEC_Bits

namespace BaconOQEC

/-- Bacon, *Operator Quantum Error Correcting Subsystems for Self-Correcting Quantum Memories*,
arXiv:quant-ph/0506023v4, §IV.C, eq. (20), p.7: the error string
"f_i(b) = ⊕_{j=1}^n b_{i,j}", the parity of the number of `Z`'s of `P(a, b)` in row `i`.

**Formalization Note.** Rows are 0-based (`Fin (m + 1)`, `n = m + 1`); the sum is in `ZMod 2`, so it
is the exclusive-or of (20). As a function of `i`, `rowPar b` is the `n`-bit string `f(b)`. -/
def rowPar {m : ℕ} (b : Bits m) (i : Fin (m + 1)) : ZMod 2 :=
  ∑ j, b i j

end BaconOQEC


