-- Prove2me | Definitions.Def_GibbsCongestion_IsSLC
-- name    : GibbsCongestion_IsSLC
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T12:01:21.164467+00:00
-- url     : https://prove2.me/theorems/e6177a23-2b48-4c0f-b5ed-dad8282122ac
-- title:
--   Strongly log-concave (SLC) polynomial
-- statement:
--   A polynomial $p$ with non-negative coefficients is **strongly log-concave (SLC)** if for every $\beta\in\mathbb Z^n_{\ge0}$ the partial derivative
--   $$\partial^\beta p=\prod_i\partial_{x_i}^{\beta_i}p$$
--   is log-concave. The zero polynomial is SLC. A distribution $\pi(\alpha)\propto w(\alpha)$ is called SLC when its generating polynomial $\sum_\alpha w(\alpha)x^\alpha$ is SLC.
--
--   **Formalization Note** $\partial^\beta$ is realized by applying $\partial/\partial x_i$ along any finite list of variables; since partial derivatives commute these are exactly the operators $\partial^\beta$. Non-negativity of the coefficients is part of the definition, as in the paper.
-- source:
--   Kleer, Sampling from the Gibbs Distribution in Congestion Games, arXiv:2105.12982v1, Definition 2.2, p.9

import Mathlib
import Definitions.Def_GibbsCongestion_IsLogConcavePoly

namespace GibbsCongestion

/-- **Strong log-concavity** (Kleer, Sampling from the Gibbs Distribution in Congestion Games, arXiv:2105.12982v1, Definition 2.2, p.9): a polynomial `p` with
non-negative coefficients is strongly log-concave (SLC) if `∂^β p` is log-concave for every
`β ∈ ℤ^n_{≥0}`. (The zero polynomial is SLC.)

**Formalization Note** `∂^β p` is realized by applying the partial derivatives `∂/∂x_i` along any
finite list of variables: since partial derivatives commute, the lists give exactly the operators
`∂^β`. Log-concavity is `IsLogConcavePoly` (open positive orthant). Non-negativity of the
coefficients is part of the definition, as in the paper. -/
noncomputable def IsSLC {σ : Type*} [Fintype σ] (p : MvPolynomial σ ℝ) : Prop :=
  (∀ m, 0 ≤ p.coeff m) ∧
    ∀ l : List σ, IsLogConcavePoly (l.foldr (fun i q => MvPolynomial.pderiv i q) p)

end GibbsCongestion


