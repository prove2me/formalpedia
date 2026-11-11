-- Prove2me | Definitions.Def_ArbLindbladLearn_muMix
-- name    : ArbLindbladLearn_muMix
-- status  : Definition
-- author  : @iris
-- created : 2026-11-10T21:28:03.412114+00:00
-- url     : https://prove2.me/theorems/ce209258-217c-4f92-a3e7-3452f29c986b
-- title:
--   Chebyshev mixture $\mu(a)=\sum_j p_j\lambda_a(t_j)$
-- statement:
--   The **Chebyshev mixture** of Pauli error rates is
--   $$\mu(a)=\sum_{j=1}^q p_j\,\lambda_a(t_j),\qquad a\in\mathbb F_2^{2n},$$
--   with $\lambda_a(t)=g_{aa}(t)$ and the support-learning nodes and weights. It is a probability distribution over Pauli labels, and heavy coefficients make their labels heavy under it (Lemma 3.5).
--
--   **Formalization Note** $\lambda_a(t)$ is real; its real part is taken.
-- source:
--   Chen, Yu, Learning Arbitrary Lindbladians from Time Evolution, arXiv:2607.28610 (sha256 46c27db5…), eq. (18), p.21

import Mathlib
import Definitions.Def_ArbLindbladLearn_suppQ
import Definitions.Def_ArbLindbladLearn_signal

set_option autoImplicit false
open scoped ComplexOrder BigOperators Matrix ENNReal NNReal Kronecker
noncomputable section

namespace ArbLindbladLearn

open LindbladTolerant.Testing

/-- The Chebyshev mixture `μ(a) = Σ_{j=1}^q p_j λ_a(t_j)` of Pauli error rates (eq. (18),
Chen–Yu, *Learning Arbitrary Lindbladians from Time Evolution*, arXiv:2607.28610 (sha256 46c27db5…), p.21), with `λ_a(t) = g_aa(t)`, the nodes on `[0, 1/Λ]` and
`q, p_j` of the support-learning setup.

**Formalization Note** `λ_a(t) = ⟨Φ_a|J_t|Φ_a⟩` is real (`J_t` is Hermitian); its real part is
taken. -/
def muMix {n : ℕ} (c : Coeffs n) (Λ η : ℝ) (a : Pauli n) : ℝ :=
  ∑ j ∈ Finset.Icc 1 (suppQ Λ η),
    suppP Λ η j * (bellCoh c a a (chebNode (suppQ Λ η) (suppT Λ) j)).re

end ArbLindbladLearn


