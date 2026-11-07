-- Prove2me | Definitions.Def_QuantumLTF_Membership_gates12
-- name    : QuantumLTF_Membership_gates12
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T02:32:10.422022+00:00
-- url     : https://prove2.me/theorems/5b97d8ca-3f58-44db-8f2d-e3431f73778c
-- title:
--   The gate model: unitaries on one or two qubits
-- statement:
--   The elementary gates are the arbitrary unitaries acting on one or two qubits, with all-to-all connectivity and clean ancillas.
--
--   **Formalization Note** The paper states this model in its §C.5 for §4 and names no other for §3; the mission adopts it. All-to-all connectivity is the arbitrary embedding of a gate's wires, and clean ancillas are extra wires starting in $|0\rangle$. The oracle is not a gate.
-- source:
--   Krivcenko, Nguyen, de Wolf, Fast Quantum Algorithms for Learning Linear Threshold Functions, arXiv:2609.40331, §C.5, unnumbered, p. 95 (PDF p. 96)

import Mathlib
import Definitions.Def_QAlgorithms_Defs_Circuit

namespace QuantumLTF.Membership

open QAlgorithms

/-- **The gate model: arbitrary unitaries on one or two qubits.** Krivcenko, Nguyen, de Wolf, *Fast Quantum Algorithms for Learning Linear Threshold Functions*,
arXiv:2609.40331, §C.5, p. 95 (PDF p. 96):
"all-to-all connectivity with arbitrary unitaries acting on one or two qubits. We also assume that
we have access to clean ancillas."

**Formalization Note.** §C.5 writes this for §4; §3 names no other model, and this mission adopts it.
All-to-all connectivity is `GateApp.wires`, an arbitrary embedding; clean ancillas are extra wires
of the circuit, all starting in `|0⟩`. The oracle is not a gate: it is reached only through
`OracleStep.query`. -/
def gates12 : Set Gate :=
  {g | g.IsUnitary ∧ 1 ≤ g.arity ∧ g.arity ≤ 2}

end QuantumLTF.Membership


