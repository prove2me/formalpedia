-- Prove2me | Definitions.Def_LindbladStructLearn_decodeLindblad
-- name    : LindbladStructLearn_decodeLindblad
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T21:57:30.837776+00:00
-- url     : https://prove2.me/theorems/dc461789-9082-427a-ab7d-3953c545e1ea
-- title:
--   Lindbladian estimate $\widehat\lambda = (\widehat\alpha, \widehat D)$
-- statement:
--   The decoded output vector with the entries of pairs with $P_1 = I$ set to $0$ (they are not parameters): $\widehat\alpha_P = \widehat\lambda_{P,I}$ and $\widehat D_{P_1,P_2} = \widehat\lambda_{P_1,P_2}$.
-- source:
--   Lewis–Tang–Wright, Learning the structure of open quantum systems, arXiv:2606.30358 (held version, sha256 0af12079…2eb52e), Theorem 1.1, p.4

import Mathlib
import Definitions.Def_LindbladStructLearn_decode

set_option autoImplicit false
open scoped ComplexOrder BigOperators Matrix ENNReal NNReal
noncomputable section

namespace LindbladStructLearn

open LindbladTolerant.Testing

/-- The Lindbladian estimate `λ̂ = (α̂, D̂)` output by the learner of Theorem 1.1 (Lewis–Tang–Wright, *Learning the structure of open quantum systems*, arXiv:2606.30358 (held version, sha256 0af12079…2eb52e), p.4):
the decoded vector, with records naming a pair with `P₁ = I` ignored (those are not parameters). -/
def decodeLindblad (n k : ℕ) (s : MState) : Pauli n × Pauli n → ℂ := fun P =>
  if P.1 = 0 then 0 else decode n k s P

end LindbladStructLearn


