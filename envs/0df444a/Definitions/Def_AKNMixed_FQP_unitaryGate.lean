-- Prove2me | Definitions.Def_AKNMixed_FQP_unitaryGate
-- name    : AKNMixed_FQP_unitaryGate
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T03:16:50.514706+00:00
-- url     : https://prove2.me/theorems/2239963e-f3ef-4dac-a247-7a4923bdc032
-- title:
--   Gate $U\cdot U^\dagger$ of a $k$-qubit matrix
-- statement:
--   For a $k$-qubit matrix $U$, the gate $U\cdot U^{\dagger}$ is the gate of order $(k,k)$ given by
--
--   $$\rho\mapsto U\rho\,U^{\dagger}.$$
--
--   For unitary $U$ it is the super-operator corresponding to the unitary transformation $|\alpha\rangle\mapsto U|\alpha\rangle$.
--
--   **Formalization Note** Defined for every square matrix (`QAlgorithms.conjSuperop`).
-- source:
--   Aharonov, Kitaev, Nisan, Quantum Circuits with Mixed States, arXiv:quant-ph/9806029v1, §2, unnumbered, p. 6 ("Such a super-operator is denoted by U · U†")

import Mathlib
import Definitions.Def_QAlgorithms_Defs_Basic
import Definitions.Def_QAlgorithms_Defs_Channel
import Definitions.Def_AKNMixed_FQP_QGate

namespace AKNMixed.FQP

open QAlgorithms

/-- **The gate `U · U†` of a `k`-qubit matrix `U`.**
Aharonov, Kitaev, Nisan, *Quantum Circuits with Mixed States*, arXiv:quant-ph/9806029v1, §2,
unnumbered, p. 6: "A super-operator corresponding to a unitary transformation on a space N,
|α⟩ ↦ U|α⟩, sends a quantum state ρ = |α⟩⟨α| to the state UρU†. Such a super-operator is denoted
by U · U†."

`unitaryGate U` is the gate of order `(k, k)` with map `ρ ↦ U ρ U†`
(`QAlgorithms.conjSuperop U`).

**Formalization Note.** Defined for every square matrix; it is a quantum gate when `U` is
unitary. -/
noncomputable def unitaryGate {k : ℕ} (U : Matrix (Qubits k) (Qubits k) ℂ) : QGate :=
  ⟨k, k, conjSuperop U⟩

end AKNMixed.FQP


