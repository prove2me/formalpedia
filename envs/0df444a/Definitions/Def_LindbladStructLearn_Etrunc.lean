-- Prove2me | Definitions.Def_LindbladStructLearn_Etrunc
-- name    : LindbladStructLearn_Etrunc
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T22:01:18.668788+00:00
-- url     : https://prove2.me/theorems/1b532cb9-b4f4-4e1d-a3b2-1b79c605c797
-- title:
--   Truncated series $\widetilde E_{\overline P}(x)$
-- statement:
--   For a threshold $\Gamma \in \mathbb N$ and a time $t$,
--
--   $$\widetilde E_{\overline P}(x) = \sum_{\ell=1}^{\Gamma} \frac{t^\ell}{\ell!} E^{(\ell)}_{\overline P}(x),$$
--
--   the Taylor series of $E(x)_{\overline P}$ truncated at degree $\Gamma$ (the $\ell = 0$ term vanishes for the pairs used).
-- source:
--   Lewis–Tang–Wright, Learning the structure of open quantum systems, arXiv:2606.30358 (held version, sha256 0af12079…2eb52e), Eq. (4.58), p.29; Eq. (5.80), p.40

import Mathlib
import Definitions.Def_LindbladStructLearn_Eell

set_option autoImplicit false
open scoped ComplexOrder BigOperators Matrix ENNReal NNReal
noncomputable section

namespace LindbladStructLearn

open LindbladTolerant.Testing

/-- The truncated series (Lewis–Tang–Wright, *Learning the structure of open quantum systems*, arXiv:2606.30358 (held version, sha256 0af12079…2eb52e), Eq. (4.58), p.29, and Eq. (5.80), p.40):
`Ẽ_P̄(x) = Σ_(ℓ=1)^Γ (t^ℓ/ℓ!) E^(ℓ)_P̄(x)`. -/
def Etrunc {n : ℕ} (Γ : ℕ) (t : ℝ) (x : Pauli n × Pauli n → ℂ) (P : Pauli n × Pauli n) : ℂ :=
  ∑ ℓ ∈ Finset.Icc 1 Γ, ((t : ℂ) ^ ℓ / (ℓ.factorial : ℂ)) * Eell ℓ x P

end LindbladStructLearn


