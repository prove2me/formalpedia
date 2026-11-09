-- Prove2me | Definitions.Def_LindbladStructLearn_pauliProd
-- name    : LindbladStructLearn_pauliProd
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T21:52:35.883999+00:00
-- url     : https://prove2.me/theorems/b8b3b60b-c30d-438b-b7f9-49305ba680c8
-- title:
--   Pauli part $\mathcal P(PQ)$ of a product of $n$-qubit Paulis
-- statement:
--   For $n$-qubit Paulis $P, Q \in \mathcal P_n = \{I,X,Y,Z\}^{\otimes n}$, $\mathcal P(PQ)$ is the Pauli with $PQ = c(PQ)\,\mathcal P(PQ)$, computed site by site from the single-qubit table.
-- source:
--   Lewis–Tang–Wright, Learning the structure of open quantum systems, arXiv:2606.30358 (held version, sha256 0af12079…2eb52e), §2, Eq. (2.2), p.13

import Mathlib
import Definitions.Def_LindbladStructLearn_letterMul

set_option autoImplicit false
open scoped ComplexOrder BigOperators Matrix ENNReal NNReal
noncomputable section

namespace LindbladStructLearn

open LindbladTolerant.Testing

/-- The Pauli part `𝒫(PQ)` of a product of two `n`-qubit Paulis (Lewis–Tang–Wright, *Learning the structure of open quantum systems*, arXiv:2606.30358 (held version, sha256 0af12079…2eb52e), §2, Eq. (2.2), p.13),
computed letter by letter. -/
def pauliProd {n : ℕ} (P Q : Pauli n) : Pauli n := fun i => letterMul (P i) (Q i)

end LindbladStructLearn


