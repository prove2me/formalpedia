-- Prove2me | Definitions.Def_LindbladStructLearn_pauliPhase
-- name    : LindbladStructLearn_pauliPhase
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T21:51:52.583909+00:00
-- url     : https://prove2.me/theorems/0ce05e59-f508-4a51-bc93-5f3bae77e8d8
-- title:
--   Phase $c(PQ)$ of a product of $n$-qubit Paulis
-- statement:
--   For $n$-qubit Paulis $P, Q$, $c(PQ) \in \{\pm1,\pm i\}$ is the scalar with $PQ = c(PQ)\,\mathcal P(PQ)$; it is the product over the $n$ sites of the single-qubit phases.
-- source:
--   Lewis–Tang–Wright, Learning the structure of open quantum systems, arXiv:2606.30358 (held version, sha256 0af12079…2eb52e), §2, Eq. (2.2), p.13

import Mathlib
import Definitions.Def_LindbladStructLearn_letterPhase

set_option autoImplicit false
open scoped ComplexOrder BigOperators Matrix ENNReal NNReal
noncomputable section

namespace LindbladStructLearn

open LindbladTolerant.Testing

/-- The phase `c(PQ) ∈ {±1, ±i}` of a product of two `n`-qubit Paulis (Lewis–Tang–Wright, *Learning the structure of open quantum systems*, arXiv:2606.30358 (held version, sha256 0af12079…2eb52e), §2, Eq. (2.2),
p.13): `PQ = c(PQ) · 𝒫(PQ)`; it is the product of the single-qubit phases. -/
def pauliPhase {n : ℕ} (P Q : Pauli n) : ℂ := ∏ i, letterPhase (P i) (Q i)

end LindbladStructLearn


