-- Prove2me | Definitions.Def_RWPI_SqrtLasso_phi
-- name    : RWPI_SqrtLasso_phi
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-05T09:28:15.654979+00:00
-- url     : https://prove2.me/theorems/cea24957-5188-4e79-ac7f-8138af1126a1
-- title:
--   The function $\varphi_\gamma(z) = \sup_u\{l(u) - \gamma c(u,z)\}$ of Proposition 1 (Eq. (11))
-- statement:
--   Let $c : Z\times Z\to[0,\infty]$ be a cost function, $l : Z\to\mathbb R$ a loss and $\gamma \ge 0$. For a point $z \in Z$ (in the paper, a data point $(X_i,Y_i)$), define
--
--   $$
--   \varphi_\gamma(z) = \sup_{u \in Z} \big\{ l(u) - \gamma\, c(u, z) \big\}.
--   $$
--
--   In the paper $Z = \mathbb R^d\times\mathbb R$, $u = (u,v)$ ranges over all of $\mathbb R^d\times\mathbb R$, and the loss $l(\cdot;\beta)$ depends on a regression parameter $\beta$, which is written $\varphi_\gamma(X_i,Y_i;\beta)$. It is the function that appears in the dual of the worst-case expected loss (Proposition 1): $\gamma$ is the Lagrange multiplier of the transport budget $D_c(P,P_n)\le\delta$.
--
--   **Convention.** A point $u$ with $c(u,z) = +\infty$ contributes $-\infty$ for every $\gamma\ge0$, including $\gamma = 0$; it never contributes to the supremum. This is how the paper evaluates $\varphi_\gamma$ for the cost $N_q$ (p. 29: "the supremum in the above expression is effectively over only $(x',y')$ such that $y' = Y_i$"). The other convention, $0\cdot\infty = 0$, would make $\varphi_0(z) = \sup_u l(u)$ and Proposition 1's minimum over $\gamma\ge0$ fail to be attained for the cost $N_q^2$ with $\beta = 0$.
--
--   **Formalization Note** The value is taken in $[0,\infty]$ with truncated subtraction $a \mathbin{\dot-} b = \max(a-b,0)$. For a nonnegative loss and a cost with $c(z,z) = 0$, the term at $u = z$ equals $l(z) \ge 0$, so the truncation does not change the supremum. The supremum is over the points `u` with `c u z ≠ ⊤`.
-- source:
--   Blanchet, Kang & Murthy, Robust Wasserstein Profile Inference and Applications to Machine Learning, arXiv:1610.05627v4, p. 10, Proposition 1, Eq. (11); convention for infinite cost from App. A.1, outline of the proof of Theorem 1, p. 29

import Mathlib

namespace RWPI.SqrtLasso

/-- The function `φ_γ` of Proposition 1, Eq. (11), p. 10:
`φ_γ(z; l) = sup_{u} { l(u) − γ c(u, z) }`, the supremum over all points `u` of the sample space.
Convention: a term with `c(u, z) = +∞` equals `−∞` for every `γ ≥ 0` (including `γ = 0`), so it
never contributes to the supremum; this is how the paper evaluates `φ_γ` for the cost `N_q`
(p. 29: "the supremum ... is effectively over only `(x', y')` such that `y' = Y_i`").
The value is taken in `[0, ∞]` with truncated subtraction; for a nonnegative loss and a cost
vanishing on the diagonal, the term at `u = z` is `l(z) ≥ 0`, so the truncation does not change the
supremum. -/
noncomputable def phi {Z : Type*} (c : Z → Z → ENNReal) (l : Z → ℝ) (γ : ℝ) (z : Z) : ENNReal :=
  ⨆ (u : Z) (_ : c u z ≠ ⊤), (ENNReal.ofReal (l u) - ENNReal.ofReal γ * c u z)

end RWPI.SqrtLasso


