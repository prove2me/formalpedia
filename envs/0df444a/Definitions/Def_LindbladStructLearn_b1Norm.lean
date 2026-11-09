-- Prove2me | Definitions.Def_LindbladStructLearn_b1Norm
-- name    : LindbladStructLearn_b1Norm
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T21:47:30.796465+00:00
-- url     : https://prove2.me/theorems/d9a99aef-fc44-474c-98ff-8776eefaee39
-- title:
--   Local one-norm $\|\lambda\|_{B_1}$
-- statement:
--   The local one-norm of a coefficient vector is the largest total weight of the terms acting on a single qubit:
--
--   $$\|\lambda\|_{B_1} = \max_{i\in[n]} \sum_{\overline P:\, S_{\overline P}\ni i} |\lambda_{\overline P}|,$$
--
--   the sum running over the terms $\overline P = (P_1,P_2)$ with $P_1 \ne I$. It plays the role of the interaction strength per site.
--
--   **Formalization Note** The maximum is taken in $\mathbb R_{\ge0}$; for $n = 0$ it is $0$.
-- source:
--   Lewis–Tang–Wright, Learning the structure of open quantum systems, arXiv:2606.30358 (held version, sha256 0af12079…2eb52e), Definition 2.4, Eq. (2.7), p.14

import Mathlib
import Definitions.Def_LindbladStructLearn_pairSupport

set_option autoImplicit false
open scoped ComplexOrder BigOperators Matrix ENNReal NNReal
noncomputable section

namespace LindbladStructLearn

open LindbladTolerant.Testing

/-- The local one-norm (Lewis–Tang–Wright, *Learning the structure of open quantum systems*, arXiv:2606.30358 (held version, sha256 0af12079…2eb52e), Definition 2.4, Eq. (2.7), p.14):
`‖λ‖_B1 = max_(i ∈ [n]) Σ_(P̄ : S_P̄ ∋ i) |λ_P̄|`, the sum over the terms `P̄ = (P₁,P₂)` with `P₁ ≠ I`.

**Formalization Note** The maximum is a `Finset.sup` in `ℝ≥0` (value `0` for `n = 0`, where there is
no term); entries with `P₁ = I` are not terms of `L_λ` and are not counted. -/
def b1Norm {n : ℕ} (x : Pauli n × Pauli n → ℂ) : ℝ :=
  ((Finset.univ.sup fun i : Fin n =>
    ∑ P ∈ Finset.univ.filter (fun P : Pauli n × Pauli n => P.1 ≠ 0 ∧ i ∈ pairSupport P),
      ‖x P‖₊ : ℝ≥0) : ℝ)

end LindbladStructLearn


