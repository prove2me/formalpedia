-- Prove2me | Definitions.Def_LindbladStructLearn_adjTermPauli
-- name    : LindbladStructLearn_adjTermPauli
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T21:57:31.225308+00:00
-- url     : https://prove2.me/theorems/5539ea28-4b3a-4331-be95-c91b21f3889e
-- title:
--   Pauli part of $\mathcal L_b^\dagger(Q)$
-- statement:
--   For a term $b = (P_1,P_2)$ and a Pauli $Q$, $\mathcal L_b^\dagger(Q) = P_2QP_1 - \tfrac12\{P_2P_1, Q\}$ is a scalar multiple $c'Q'$ of a single Pauli; this is $Q' = \mathcal P(P_2QP_1)$.
-- source:
--   Lewis–Tang–Wright, Learning the structure of open quantum systems, arXiv:2606.30358 (held version, sha256 0af12079…2eb52e), Algorithm 2, line 11, p.30

import Mathlib
import Definitions.Def_LindbladStructLearn_pauliProd

set_option autoImplicit false
open scoped ComplexOrder BigOperators Matrix ENNReal NNReal
noncomputable section

namespace LindbladStructLearn

open LindbladTolerant.Testing

/-- Algorithm 2, line 11 (Lewis–Tang–Wright, *Learning the structure of open quantum systems*, arXiv:2606.30358 (held version, sha256 0af12079…2eb52e), p.30): for a term `b = (P₁,P₂)` and a Pauli `Q`,
`L_b†(Q) = P₂ Q P₁ − ½{P₂P₁, Q} = c'·Q'`; this is the Pauli `Q' = 𝒫(P₂ Q P₁)`. -/
def adjTermPauli {n : ℕ} (b : Pauli n × Pauli n) (Q : Pauli n) : Pauli n :=
  pauliProd (pauliProd b.2 Q) b.1

end LindbladStructLearn


