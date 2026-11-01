-- Prove2me | Definitions.Def_GibbsCongestion_IsLogConcavePoly
-- name    : GibbsCongestion_IsLogConcavePoly
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T12:00:24.827833+00:00
-- url     : https://prove2.me/theorems/7adaf204-1242-45e0-926a-49424447b9f9
-- title:
--   Log-concave polynomial on the positive orthant
-- statement:
--   A polynomial $p\in\mathbb R[x_i: i\in\sigma]$ (with non-negative coefficients) is **log-concave** if the Hessian $\nabla^2\log p$ is negative semidefinite. Here this is required on the open positive orthant: for every $x$ with $x_i>0$ for all $i$ and every direction $v$,
--   $$p(x)\;v^{\top}\nabla^2p(x)\,v\ \le\ \big(\nabla p(x)\cdot v\big)^2 .$$
--   Strong log-concavity (log-concavity of every partial derivative) is built on this notion.
--
--   **Formalization Note** Since $\nabla^2\log p=(p\nabla^2p-\nabla p\nabla p^{\top})/p^2$, the displayed inequality is equivalent to $v^\top\nabla^2\log p(x)\,v\le0$ wherever $p(x)>0$, which holds on the whole open orthant for a nonzero polynomial with non-negative coefficients; for $p=0$ it holds trivially, matching the convention that the zero polynomial is strongly log-concave. The paper leaves the set $S\subseteq\mathbb R^n_{\ge0}$ unspecified; the open positive orthant is the convention of the cited works of Anari et al. and Brändén–Huh.
-- source:
--   Kleer, Sampling from the Gibbs Distribution in Congestion Games, arXiv:2105.12982v1, Definition 2.2, p.9

import Mathlib

namespace GibbsCongestion

/-- **Log-concavity of a polynomial on the open positive orthant**
(Kleer, Sampling from the Gibbs Distribution in Congestion Games, arXiv:2105.12982v1, Definition 2.2, p.9): the Hessian `∇² log p` is negative semidefinite at every point
`x ∈ ℝ^σ_{>0}`.

**Formalization Note** The condition is stated without logarithms: for all `x` with positive
coordinates and every direction `v`,
`p(x) · vᵀ ∇²p(x) v ≤ (∇p(x) · v)²`.
Where `p(x) > 0` this is equivalent to `vᵀ ∇² log p(x) v ≤ 0`, because
`∇² log p = (p ∇²p − ∇p ∇pᵀ)/p²`. For a nonzero polynomial with non-negative coefficients
`p(x) > 0` on the open orthant, and for `p = 0` the condition holds trivially. The paper leaves the
set `S ⊆ ℝⁿ_{≥0}` open; the open positive orthant is the convention of the cited works
(Anari et al.; Brändén–Huh). -/
noncomputable def IsLogConcavePoly {σ : Type*} [Fintype σ] (p : MvPolynomial σ ℝ) : Prop :=
  ∀ x : σ → ℝ, (∀ i, 0 < x i) → ∀ v : σ → ℝ,
    MvPolynomial.eval x p *
        ∑ i, ∑ j, v i * v j * MvPolynomial.eval x (MvPolynomial.pderiv i (MvPolynomial.pderiv j p))
      ≤ (∑ i, v i * MvPolynomial.eval x (MvPolynomial.pderiv i p)) ^ 2

end GibbsCongestion


