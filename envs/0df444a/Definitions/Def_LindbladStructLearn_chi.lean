-- Prove2me | Definitions.Def_LindbladStructLearn_chi
-- name    : LindbladStructLearn_chi
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T21:46:13.124685+00:00
-- url     : https://prove2.me/theorems/1da72908-f3a9-4b4f-96ed-e77211fa27a1
-- title:
--   Fourier basis superoperators $\chi_{P_1,P_2}(\rho) = P_1\rho P_2$
-- statement:
--   For $n$-qubit Paulis $P_1, P_2$, the superoperator $\chi_{P_1,P_2}$ maps an operator $\rho$ to $P_1 \rho P_2$. The $16^n$ maps $\chi_{P_1,P_2}$ form a basis of the superoperators on $n$ qubits.
-- source:
--   Lewis–Tang–Wright, Learning the structure of open quantum systems, arXiv:2606.30358 (held version, sha256 0af12079…2eb52e), §2.2, Eq. (2.10), p.14

import Mathlib
import Definitions.Def_LindbladTolerant_Testing_lindblad_model

set_option autoImplicit false
open scoped ComplexOrder BigOperators Matrix ENNReal NNReal
noncomputable section

namespace LindbladStructLearn

open LindbladTolerant.Testing

/-- The Fourier basis superoperators (Lewis–Tang–Wright, *Learning the structure of open quantum systems*, arXiv:2606.30358 (held version, sha256 0af12079…2eb52e), §2.2, Eq. (2.10), p.14): `χ_(P₁,P₂)(ρ) = P₁ ρ P₂`. -/
def chi {n : ℕ} (P1 P2 : Pauli n) (ρ : Op (Qubits n)) : Op (Qubits n) :=
  pauliMatrix P1 * ρ * pauliMatrix P2

end LindbladStructLearn


