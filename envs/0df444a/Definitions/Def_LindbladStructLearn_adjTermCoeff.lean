-- Prove2me | Definitions.Def_LindbladStructLearn_adjTermCoeff
-- name    : LindbladStructLearn_adjTermCoeff
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T21:56:48.753639+00:00
-- url     : https://prove2.me/theorems/29b2e81e-969c-4dfb-a525-d3beddc8004a
-- title:
--   Scalar $c'$ with $\mathcal L_b^\dagger(Q) = c'Q'$
-- statement:
--   For a term $b = (P_1,P_2)$ and a Pauli $Q$, the scalar
--
--   $$c' = c(P_2QP_1) - \tfrac12\big(c(P_2P_1Q) + c(QP_2P_1)\big),$$
--
--   so that $\mathcal L_b^\dagger(Q) = c'\,\mathcal P(P_2QP_1)$ (the three products have the same Pauli part).
-- source:
--   Lewis–Tang–Wright, Learning the structure of open quantum systems, arXiv:2606.30358 (held version, sha256 0af12079…2eb52e), Algorithm 2, line 11, p.30

import Mathlib
import Definitions.Def_LindbladStructLearn_pauliProd
import Definitions.Def_LindbladStructLearn_pauliPhase

set_option autoImplicit false
open scoped ComplexOrder BigOperators Matrix ENNReal NNReal
noncomputable section

namespace LindbladStructLearn

open LindbladTolerant.Testing

/-- Algorithm 2, line 11 (Lewis–Tang–Wright, *Learning the structure of open quantum systems*, arXiv:2606.30358 (held version, sha256 0af12079…2eb52e), p.30): the scalar `c'` with `L_b†(Q) = c' · Q'` for
`b = (P₁,P₂)`: `c' = c(P₂QP₁) − ½(c(P₂P₁Q) + c(QP₂P₁))` (all three products have Pauli part `Q'`). -/
def adjTermCoeff {n : ℕ} (b : Pauli n × Pauli n) (Q : Pauli n) : ℂ :=
  pauliPhase b.2 Q * pauliPhase (pauliProd b.2 Q) b.1 -
    (1 / 2 : ℂ) * (pauliPhase b.2 b.1 * pauliPhase (pauliProd b.2 b.1) Q +
      pauliPhase Q b.2 * pauliPhase (pauliProd Q b.2) b.1)

end LindbladStructLearn


