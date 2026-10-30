-- Prove2me | Definitions.Def_AKNMixed_FQP_cnotGate
-- name    : AKNMixed_FQP_cnotGate
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T03:17:58.980077+00:00
-- url     : https://prove2.me/theorems/4cd279c4-3ec2-4949-b10c-53c32851002a
-- title:
--   Controlled-not gate $C$
-- statement:
--   The **controlled-not gate** $C$ is the unitary gate on two qubits with $C|c,t\rangle=|c,t\oplus c\rangle$; in particular $C|00\rangle=|00\rangle$ and $C|10\rangle=|11\rangle$, so it serves as a copying gate. Wire $0$ is the control and wire $1$ the target.
--
--   **Formalization Note** `QAlgorithms.cnot`, reindexed from pairs of bits to two-qubit strings, as a gate $\rho\mapsto C\rho C^\dagger$.
-- source:
--   Aharonov, Kitaev, Nisan, Quantum Circuits with Mixed States, arXiv:quant-ph/9806029v1, §4.2, unnumbered, p. 11 ("C is a special unitary gate on two qubits, the controlled not gate")

import Mathlib
import Definitions.Def_QAlgorithms_Defs_Basic
import Definitions.Def_QAlgorithms_Defs_Gates
import Definitions.Def_AKNMixed_FQP_QGate
import Definitions.Def_AKNMixed_FQP_unitaryGate

namespace AKNMixed.FQP

open QAlgorithms

/-- **The controlled-not gate `C` on two qubits.**
Aharonov, Kitaev, Nisan, *Quantum Circuits with Mixed States*, arXiv:quant-ph/9806029v1, §4.2,
unnumbered, p. 11: "C is a special unitary gate on two qubits, the controlled not gate. It
satisfies C|00⟩ = |00⟩, C|10⟩ = |11⟩, and thus serves as a copying gate."

`cnotGate` is the unitary gate of order `(2, 2)` of the matrix `|c, t⟩ ↦ |c, t ⊕ c⟩`, with wire
`0` the control and wire `1` the target (`QAlgorithms.cnot`, reindexed from `Bool × Bool` to
`Qubits 2` by `x ↦ (x 0, x 1)`). -/
noncomputable def cnotGate : QGate :=
  unitaryGate (Matrix.of fun (x y : Qubits 2) => cnot (x 0, x 1) (y 0, y 1))

end AKNMixed.FQP


