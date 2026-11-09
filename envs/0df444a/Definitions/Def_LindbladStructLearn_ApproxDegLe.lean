-- Prove2me | Definitions.Def_LindbladStructLearn_ApproxDegLe
-- name    : LindbladStructLearn_ApproxDegLe
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T21:49:52.387943+00:00
-- url     : https://prove2.me/theorems/83ebb789-f460-403a-9619-0e75fc5e1d23
-- title:
--   Approximate degree bound $\deg_\eta(\mathcal L_\lambda) \le d$
-- statement:
--   The approximate degree is $\deg_\eta(\mathcal L_\lambda) = \min\{\deg(\mathcal L_{\mathrm{big}}) : \|\mathcal L_\lambda - \mathcal L_{\mathrm{big}}\|_{B_1} < \eta\}$, the smallest degree of a vector within local one-norm distance $\eta$. The predicate holds when $\deg_\eta(\mathcal L_\lambda) \le d$, i.e. when there is a $\mu$ with
--
--   $$\|\lambda - \mu\|_{B_1} < \eta \quad\text{and}\quad \deg(\mu) \le d.$$
--
--   **Formalization Note** The minimum is over a nonempty set of naturals whenever $\eta > 0$ ($\mu = \lambda$ is a candidate), so the bound is stated in this equivalent existential form instead of through an infimum.
-- source:
--   Lewis–Tang–Wright, Learning the structure of open quantum systems, arXiv:2606.30358 (held version, sha256 0af12079…2eb52e), Definition 2.5, Eq. (2.9), p.14

import Mathlib
import Definitions.Def_LindbladStructLearn_b1Norm
import Definitions.Def_LindbladStructLearn_deg

set_option autoImplicit false
open scoped ComplexOrder BigOperators Matrix ENNReal NNReal
noncomputable section

namespace LindbladStructLearn

open LindbladTolerant.Testing

/-- `deg_η(L_λ) ≤ d` (Lewis–Tang–Wright, *Learning the structure of open quantum systems*, arXiv:2606.30358 (held version, sha256 0af12079…2eb52e), Definition 2.5, Eq. (2.9), p.14): the approximate degree
`deg_η(L_λ) = min_(L_big : ‖L_λ − L_big‖_B1 < η) deg(L_big)` is at most `d`.

**Formalization Note** The minimum ranges over a set of naturals, nonempty whenever `η > 0`
(`L_big = L_λ`), so `deg_η(L_λ) ≤ d` holds iff some `μ` has `‖λ − μ‖_B1 < η` and `deg(μ) ≤ d`;
this `∃` form is the definition used here (no `sInf`). -/
def ApproxDegLe {n : ℕ} (η : ℝ) (x : Pauli n × Pauli n → ℂ) (d : ℕ) : Prop :=
  ∃ μ : Pauli n × Pauli n → ℂ, b1Norm (x - μ) < η ∧ deg μ ≤ d

end LindbladStructLearn


