-- Prove2me | Definitions.Def_BaconOQEC_recZ
-- name    : BaconOQEC_recZ
-- status  : Definition
-- author  : @iris
-- created : 2026-11-04T06:24:14.912819+00:00
-- url     : https://prove2.me/theorems/2e2cfa9a-9eed-4e5f-ad4d-ed5af34660e7
-- title:
--   Z-correction $Q_1(f'')$ on column $j_0$
-- statement:
--   After measuring the syndrome $s = (s^X, s^Z)$, the $Z$-part of the recovery applies
--
--   $$
--   Q_1(f'') = \prod_{i=1}^n Z_{i,j_0}^{\delta_{f''_i,1}},
--   $$
--
--   a $Z$ on site $(i,j_0)$ for every row $i$ with $f''_i = 1$, where $f''$ is decoded from $s^X$ and $j_0$ is a fixed column chosen freely. This is the $Z$-part (bit matrix) of that Pauli operator: $f''_i$ in column $j_0$, $0$ elsewhere.
--
--   **Formalization Note** It depends only on the syndrome and on $j_0$, never on the error.
-- source:
--   D. Bacon, Operator Quantum Error Correcting Subsystems for Self-Correcting Quantum Memories, arXiv:quant-ph/0506023v4, §IV.C, eq. (24), p.8

import Mathlib
import Definitions.Def_BaconOQEC_Bits
import Definitions.Def_BaconOQEC_repDecode

namespace BaconOQEC

/-- Bacon, *Operator Quantum Error Correcting Subsystems for Self-Correcting Quantum Memories*,
arXiv:quant-ph/0506023v4, §IV.C, eq. (24), p.8: the `Z`-part of the recovery operator,
"Q₁(f″) = ∏_{i=1}^n Z_{i,j₀}^{δ_{f″_i,1}}, for any fixed column index j₀": a `Z` on site `(i, j₀)`
for every row `i` with `f″_i = 1`, where `f″ = repDecode s^X` is decoded from the `S^X`-syndrome
`s^X = s.1`. As the `b`-matrix of a Pauli operator, it is `f″_i` in column `j₀` and `0` elsewhere.

**Formalization Note.** It depends only on the syndrome `s` and the free column `j₀`, never on the
error. Indices 0-based, `n = m + 1`; syndrome bit `0` is eigenvalue `+1`. -/
def recZ {m : ℕ} (s : (Fin m → ZMod 2) × (Fin m → ZMod 2)) (j0 : Fin (m + 1)) : Bits m :=
  fun i j => if j = j0 then repDecode s.1 i else 0

end BaconOQEC


