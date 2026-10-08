-- Prove2me | Definitions.Def_RWPI_SqrtLasso_lqSqCost
-- name    : RWPI_SqrtLasso_lqSqCost
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-05T09:28:24.637549+00:00
-- url     : https://prove2.me/theorems/e6be13dc-364d-4e49-97f8-dd01ddec17a7
-- title:
--   Squared $\ell_q$ cost $\|(x,y)-(u,v)\|_q^2$ on $\mathbb R^{d+1}$ and $\bar\beta = (-\beta, 1)$ (Proposition 2)
-- statement:
--   Identify a predictor–response pair $(x,y)\in\mathbb R^d\times\mathbb R$ with the vector $\bar x = (x,y)\in\mathbb R^{d+1}$ whose last coordinate is the response. For $q\in[1,\infty]$, the **second-order $\ell_q$ cost** of Proposition 2 is
--
--   $$
--   c\big((x,y),(u,v)\big) = \big\|(x,y) - (u,v)\big\|_q^2 ,
--   $$
--
--   the squared $\ell_q$ norm on $\mathbb R^{d+1}$ of the difference. It moves predictors and responses alike, and it is finite everywhere. For $\beta\in\mathbb R^d$ write
--
--   $$
--   \bar\beta = (-\beta, 1) \in \mathbb R^{d+1},
--   $$
--
--   so that $y - \beta^T x = \bar\beta^T \bar x$ and the square loss is $(\bar\beta^T\bar x)^2$.
--
--   **Formalization Note** `stack z` is the vector $(x,y)$ built with `Fin.snoc` (the response is the last coordinate, index $d$), `betaBar β = stack (-β, 1)`, and $\|\cdot\|_q$ is the norm of `PiLp q` (`WithLp.toLp q`), with $q = \infty$ the max norm. The cost is valued in $[0,\infty]$ through `ENNReal.ofReal`.
-- source:
--   Blanchet, Kang & Murthy, Robust Wasserstein Profile Inference and Applications to Machine Learning, arXiv:1610.05627v4, p. 10, Proposition 2 (the cost and $\bar\beta = (-\beta,1)$)

import Mathlib

namespace RWPI.SqrtLasso

/-- The stacked vector `x̄ = (x, y) ∈ ℝ^{d+1}` of a predictor–response pair
`(x, y) ∈ ℝ^d × ℝ` (the last coordinate is the response). -/
def stack {d : ℕ} (z : (Fin d → ℝ) × ℝ) : Fin (d + 1) → ℝ :=
  Fin.snoc (α := fun _ => ℝ) z.1 z.2

/-- `β̄ = (−β, 1) ∈ ℝ^{d+1}` (p. 10), so that `y − βᵀx = β̄ᵀ(x, y)`. -/
def betaBar {d : ℕ} (β : Fin d → ℝ) : Fin (d + 1) → ℝ :=
  stack (-β, 1)

/-- The second-order `ℓ_q` cost of Proposition 2, p. 10:
`c((x, y), (u, v)) = ‖(x, y) − (u, v)‖_q²`, the squared `ℓ_q` norm on `ℝ^{d+1}` of the difference
of the stacked vectors. It is finite everywhere. -/
noncomputable def lqSqCost {d : ℕ} (q : ENNReal) (z w : (Fin d → ℝ) × ℝ) : ENNReal :=
  ENNReal.ofReal (‖WithLp.toLp q (stack z - stack w)‖ ^ 2)

end RWPI.SqrtLasso


