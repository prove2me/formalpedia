-- Prove2me | Definitions.Def_RWPI_SqrtLasso_squareLoss
-- name    : RWPI_SqrtLasso_squareLoss
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-05T09:28:22.645014+00:00
-- url     : https://prove2.me/theorems/2219e73a-6726-4344-8de6-4e823832e2f8
-- title:
--   Square loss $l(x,y;\beta) = (y - \beta^T x)^2$
-- statement:
--   For a predictor $x \in \mathbb R^d$, a response $y\in\mathbb R$ and a regression coefficient $\beta\in\mathbb R^d$, the **square loss** of linear regression is
--
--   $$
--   l(x, y; \beta) = \big(y - \beta^T x\big)^2, \qquad \beta^T x = \sum_{j=1}^d \beta_j x_j .
--   $$
--
--   It is the loss of Example 1, Proposition 2 and Theorem 1.
-- source:
--   Blanchet, Kang & Murthy, Robust Wasserstein Profile Inference and Applications to Machine Learning, arXiv:1610.05627v4, p. 2, Example 1; p. 10, Proposition 2; p. 11, Theorem 1

import Mathlib

namespace RWPI.SqrtLasso

/-- The square loss of linear regression, Example 1 / Theorem 1 (pp. 2, 11):
`l(x, y; β) = (y − βᵀx)²` for a predictor `x ∈ ℝ^d`, response `y ∈ ℝ` and coefficient
`β ∈ ℝ^d`; `βᵀx = ∑_j β_j x_j`. -/
def squareLoss {d : ℕ} (β : Fin d → ℝ) (z : (Fin d → ℝ) × ℝ) : ℝ :=
  (z.2 - ∑ j, β j * z.1 j) ^ 2

end RWPI.SqrtLasso


