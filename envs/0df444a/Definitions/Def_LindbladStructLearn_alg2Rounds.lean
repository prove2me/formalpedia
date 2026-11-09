-- Prove2me | Definitions.Def_LindbladStructLearn_alg2Rounds
-- name    : LindbladStructLearn_alg2Rounds
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T22:03:58.140173+00:00
-- url     : https://prove2.me/theorems/1f706a9c-68d2-4bce-bd14-b7ff79fe44a0
-- title:
--   $r$ rounds of Algorithm 2
-- statement:
--   The law of the state of Algorithm 2 after $r$ rounds, started from a given state $(c, Q, A)$.
-- source:
--   Lewis–Tang–Wright, Learning the structure of open quantum systems, arXiv:2606.30358 (held version, sha256 0af12079…2eb52e), Algorithm 2, lines 3–13, p.30

import Mathlib
import Definitions.Def_LindbladStructLearn_alg2Step
import Definitions.Def_LindbladStructLearn_FinDist_bind

set_option autoImplicit false
open scoped ComplexOrder BigOperators Matrix ENNReal NNReal
noncomputable section

namespace LindbladStructLearn

open LindbladTolerant.Testing

/-- `r` rounds of Algorithm 2 (Lewis–Tang–Wright, *Learning the structure of open quantum systems*, arXiv:2606.30358 (held version, sha256 0af12079…2eb52e), lines 3–13, p.30) from a state `(c, Q, A)`. -/
def alg2Rounds {n k : ℕ} (x : Idx n k → ℂ) :
    ℕ → ℂ × Pauli n × Finset (Fin n) → FinDist (ℂ × Pauli n × Finset (Fin n))
  | 0, s => [(1, s)]
  | r + 1, s => FinDist.bind (alg2Rounds x r s) (alg2Step x)

end LindbladStructLearn


