-- Prove2me | Definitions.Def_LindbladStructLearn_deg
-- name    : LindbladStructLearn_deg
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T21:47:19.456142+00:00
-- url     : https://prove2.me/theorems/da27a8e4-cb58-420f-8982-dd7b3cd54ae1
-- title:
--   Degree $\deg(\mathcal L_\lambda)$
-- statement:
--   The degree of a coefficient vector is the largest number of nonzero terms acting on one site:
--
--   $$\deg(\mathcal L_\lambda) = \max_{i\in[n]} \big|\{\overline P : i \in S_{\overline P},\ \lambda_{\overline P}\ne 0\}\big|,$$
--
--   over the terms $\overline P$ with $P_1 \ne I$.
-- source:
--   Lewis–Tang–Wright, Learning the structure of open quantum systems, arXiv:2606.30358 (held version, sha256 0af12079…2eb52e), Definition 2.5, Eq. (2.8), p.14

import Mathlib
import Definitions.Def_LindbladStructLearn_pairSupport

set_option autoImplicit false
open scoped ComplexOrder BigOperators Matrix ENNReal NNReal
noncomputable section

namespace LindbladStructLearn

open LindbladTolerant.Testing

/-- The degree (Lewis–Tang–Wright, *Learning the structure of open quantum systems*, arXiv:2606.30358 (held version, sha256 0af12079…2eb52e), Definition 2.5, Eq. (2.8), p.14):
`deg(L_λ) = max_(i ∈ [n]) |{P̄ : i ∈ S_P̄, λ_P̄ ≠ 0}|`, over terms `P̄` with `P₁ ≠ I`. -/
def deg {n : ℕ} (x : Pauli n × Pauli n → ℂ) : ℕ :=
  Finset.univ.sup fun i : Fin n =>
    (Finset.univ.filter fun P : Pauli n × Pauli n =>
      P.1 ≠ 0 ∧ i ∈ pairSupport P ∧ x P ≠ 0).card

end LindbladStructLearn


