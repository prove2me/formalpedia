-- Prove2me | Definitions.Def_AKNMixed_FQP_toffoliGate
-- name    : AKNMixed_FQP_toffoliGate
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T03:18:07.199544+00:00
-- url     : https://prove2.me/theorems/f2f3ad07-ef44-4262-b85d-e3e13a2c4ce9
-- title:
--   Toffoli gate (added to the gate set of Theorem 2)
-- statement:
--   The **Toffoli gate** is the unitary gate on three qubits with
--
--   $$|c_1,c_2,t\rangle\mapsto|c_1,c_2,t\oplus(c_1\wedge c_2)\rangle ,$$
--
--   wires $0,1$ being the controls and wire $2$ the target.
--
--   It is not in the paper's printed gate set $\mathcal U_{\mathcal G}\cup\mathcal U^{\dagger}_{\mathcal G}\cup\mathcal C$. The proof of Theorem 2 needs a garbage flag (an OR of bits) and a copy of the input conditioned on that flag; this gate supplies both, and it is added to the gate set as the correction of Theorem 2.
--
--   **Formalization Note** `QAlgorithms.controlled QAlgorithms.cnot`, reindexed to three-qubit strings.
-- source:
--   Aharonov, Kitaev, Nisan, Quantum Circuits with Mixed States, arXiv:quant-ph/9806029v1, Theorem 2 and its proof, p. 11 (garbage control bit; copy conditioned on it); not in the printed gate set

import Mathlib
import Definitions.Def_QAlgorithms_Defs_Basic
import Definitions.Def_QAlgorithms_Defs_Gates
import Definitions.Def_AKNMixed_FQP_QGate
import Definitions.Def_AKNMixed_FQP_unitaryGate

namespace AKNMixed.FQP

open QAlgorithms

/-- **The Toffoli (controlled-controlled-not) gate on three qubits.**
Not in the paper's gate set as printed: Aharonov, Kitaev, Nisan, *Quantum Circuits with Mixed
States*, arXiv:quant-ph/9806029v1, Theorem 2, p. 11, uses "U_G ∪ U_G† ∪ C". The proof of
Theorem 2 (p. 11) needs a garbage flag ("if the string written on the qubits other than the main
qubits is different from zero, … we change the garbage control bit to |1⟩") and a copy of the
input "conditioned that the garbage control bit is one"; this gate supplies them. It is added to
the gate set as the correction of Theorem 2 (see `AKNMixed.FQP.fqp_fqp_eq_fqp`).

`toffoliGate` is the unitary gate of order `(3, 3)` of the matrix
`|c₁, c₂, t⟩ ↦ |c₁, c₂, t ⊕ (c₁ ∧ c₂)⟩`, with wires `0, 1` the controls and wire `2` the target
(`QAlgorithms.controlled QAlgorithms.cnot`, reindexed by `x ↦ (x 0, (x 1, x 2))`). -/
noncomputable def toffoliGate : QGate :=
  unitaryGate (Matrix.of fun (x y : Qubits 3) => controlled cnot (x 0, (x 1, x 2)) (y 0, (y 1, y 2)))

end AKNMixed.FQP


