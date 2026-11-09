-- Prove2me | Definitions.Def_LindbladStructLearn_restrict
-- name    : LindbladStructLearn_restrict
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T21:47:18.393169+00:00
-- url     : https://prove2.me/theorems/6ac655e2-86a2-4194-8ad4-f157b27a99d3
-- title:
--   Restriction $Q^S$ of a Pauli to a set of qubits
-- statement:
--   For a set $S \subseteq [n]$ of qubits and a Pauli $Q \in \mathcal P_n$, $Q^S$ is the $n$-qubit Pauli that agrees with $Q$ on $S$ and is the identity off $S$. With $\overline S$ the complement, $Q^{\overline S}$ is $Q$ restricted to the complement.
-- source:
--   Lewis–Tang–Wright, Learning the structure of open quantum systems, arXiv:2606.30358 (held version, sha256 0af12079…2eb52e), §2.2, Eqs. (2.17), (2.21), (2.27), pp.15–17

import Mathlib
import Definitions.Def_LindbladTolerant_Testing_lindblad_model

set_option autoImplicit false
open scoped ComplexOrder BigOperators Matrix ENNReal NNReal
noncomputable section

namespace LindbladStructLearn

open LindbladTolerant.Testing

/-- Restriction of a Pauli to a set of qubits (Lewis–Tang–Wright, *Learning the structure of open quantum systems*, arXiv:2606.30358 (held version, sha256 0af12079…2eb52e), §2.2, Eqs. (2.17), (2.21), (2.27),
pp.15–17): `Q^S` is `Q` on `S` and the identity off `S` (an `n`-qubit Pauli). -/
def restrict {n : ℕ} (S : Finset (Fin n)) (Q : Pauli n) : Pauli n :=
  fun i => if i ∈ S then Q i else 0

end LindbladStructLearn


