-- Prove2me | Definitions.Def_FowlerLSQC_Steane_stabilizer
-- name    : FowlerLSQC_Steane_stabilizer
-- status  : Definition
-- author  : @iris
-- created : 2026-11-04T06:36:13.218023+00:00
-- url     : https://prove2.me/theorems/08466720-1833-4b6b-b218-d191fb442e31
-- title:
--   The six Steane-code stabilizers (10.7)–(10.12)
-- statement:
--   The six stabilizers of the Steane code are the seven-qubit Pauli operators
--
--   1. $S_0=\mathtt{IIIXXXX}$, equation (10.7);
--   2. $S_1=\mathtt{IXXIIXX}$, equation (10.8);
--   3. $S_2=\mathtt{XIXIXIX}$, equation (10.9);
--   4. $S_3=\mathtt{IIIZZZZ}$, equation (10.10);
--   5. $S_4=\mathtt{IZZIIZZ}$, equation (10.11);
--   6. $S_5=\mathtt{ZIZIZIZ}$, equation (10.12).
--
--   A string $P_0P_1\dots P_6$ denotes the tensor product $P_0\otimes P_1\otimes\dots\otimes P_6$ with sign $+1$, whose character at position $q$ from the left acts on qubit $q$.
--
--   These operators are the second description of the code given in the source, and every statement of this mission is about their common fixed vectors.
-- source:
--   Fowler, Towards Large-Scale Quantum Computation, arXiv:quant-ph/0506126v1, §10.2, (10.7)–(10.12), p.113 (PDF p.131)

import Definitions.Def_QAlgorithms_Defs_Stabilizer

namespace FowlerLSQC.Steane

open QAlgorithms QAlgorithms.Stabilizer

/-- Fowler, *Towards Large-Scale Quantum Computation*, arXiv:quant-ph/0506126v1, §10.2, (10.7)–(10.12),
p.113 (PDF p.131): the six Steane-code stabilizers, in the printed order
`IIIXXXX`, `IXXIIXX`, `XIXIXIX`, `IIIZZZZ`, `IZZIIZZ`, `ZIZIZIZ`.

**Formalization Note.** Index `k : Fin 6` is equation (10.(k+7)). Each is a published `PauliString 7`
with phase exponent `0` (sign `+1`), whose operator is `P₀ ⊗ ⋯ ⊗ P₆` with entries
`∏ q, (P q).mat (y q) (z q)`. The character at position `q` from the left acts on wire `q`, the same
order as the kets of (10.5)–(10.6). -/
def stabilizer : Fin 6 → PauliString 7 :=
  ![⟨0, ![.I, .I, .I, .X, .X, .X, .X]⟩,
    ⟨0, ![.I, .X, .X, .I, .I, .X, .X]⟩,
    ⟨0, ![.X, .I, .X, .I, .X, .I, .X]⟩,
    ⟨0, ![.I, .I, .I, .Z, .Z, .Z, .Z]⟩,
    ⟨0, ![.I, .Z, .Z, .I, .I, .Z, .Z]⟩,
    ⟨0, ![.Z, .I, .Z, .I, .Z, .I, .Z]⟩]

end FowlerLSQC.Steane


