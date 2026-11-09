-- Prove2me | Definitions.Def_LindbladStructLearn_alg2Law
-- name    : LindbladStructLearn_alg2Law
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T22:07:58.239493+00:00
-- url     : https://prove2.me/theorems/e76e5c6c-762f-4556-a16e-b822121c42d0
-- title:
--   Output law of Algorithm 2: $Z^{(\ell)}_{\overline P}(x)$
-- statement:
--   The law of the output of Algorithm 2 on input $x$, a pair $\overline P = (P_1,P_2)$ and $\ell \ge 0$: sample $R \sim \mathcal P_{S_{\overline P}}$, start from $c^{(0)} = c(P_2RP_1)$, $Q^{(0)} = \mathcal P(P_2RP_1)$, $A^{(0)} = S_{\overline P}$, run $\ell$ rounds, and return $Z^{(\ell)}_{\overline P}(x) = c^{(\ell)}\,\overline{\mathrm{tr}}(Q^{(\ell)}R)$.
-- source:
--   Lewis–Tang–Wright, Learning the structure of open quantum systems, arXiv:2606.30358 (held version, sha256 0af12079…2eb52e), Algorithm 2, p.30

import Mathlib
import Definitions.Def_LindbladStructLearn_alg2Rounds
import Definitions.Def_LindbladStructLearn_FinDist_uniform
import Definitions.Def_LindbladStructLearn_paulisOn
import Definitions.Def_LindbladStructLearn_ntr

set_option autoImplicit false
open scoped ComplexOrder BigOperators Matrix ENNReal NNReal
noncomputable section

namespace LindbladStructLearn

open LindbladTolerant.Testing

/-- The law of the output `Z^(ℓ)_P̄(x)` of Algorithm 2 (Lewis–Tang–Wright, *Learning the structure of open quantum systems*, arXiv:2606.30358 (held version, sha256 0af12079…2eb52e), p.30): sample `R ∼ 𝒫_(S_P̄)`,
start from `c^(0) = c(P₂RP₁)`, `Q^(0) = 𝒫(P₂RP₁)`, `A^(0) = S_P̄`, run `ℓ` rounds, and return
`c^(ℓ) tr̄(Q^(ℓ) R)`. -/
def alg2Law {n k : ℕ} (x : Idx n k → ℂ) (P : Pauli n × Pauli n) (ℓ : ℕ) : FinDist ℂ :=
  FinDist.bind (FinDist.uniform (paulisOn (pairSupport P))) fun R =>
    List.map (fun o => (o.1, o.2.1 * ntr (pauliMatrix o.2.2.1 * pauliMatrix R)))
      (alg2Rounds x ℓ (pauliPhase P.2 R * pauliPhase (pauliProd P.2 R) P.1,
        pauliProd (pauliProd P.2 R) P.1, pairSupport P))

end LindbladStructLearn


