-- Prove2me | Definitions.Def_RWPI_SqrtLasso_MSE
-- name    : RWPI_SqrtLasso_MSE
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-05T09:45:58.013584+00:00
-- url     : https://prove2.me/theorems/cf2be89a-8319-4b83-bcf2-4d9aea54c51b
-- title:
--   Empirical mean square error $\mathrm{MSE}_n(\beta)$
-- statement:
--   Let $(X_1,Y_1),\dots,(X_n,Y_n)$ be training data with $X_i\in\mathbb R^d$ and $Y_i\in\mathbb R$. For $\beta\in\mathbb R^d$ the **mean square error** is
--
--   $$
--   \mathrm{MSE}_n(\beta) = \mathbb E_{P_n}\big[(Y-\beta^T X)^2\big] = \frac1n \sum_{i=1}^n \big(Y_i - \beta^T X_i\big)^2,
--   $$
--
--   the average square loss over the sample; $P_n$ is the empirical distribution of the data.
--
--   **Formalization Note** The samples are indexed by `Fin n`; the normalisation is $1/n$ (not $1/(n-1)$). For $n = 0$ the value is $0$; the theorems that use it assume $n > 0$.
-- source:
--   Blanchet, Kang & Murthy, Robust Wasserstein Profile Inference and Applications to Machine Learning, arXiv:1610.05627v4, p. 10, Proposition 2; p. 11, Theorem 1

import Mathlib
import Definitions.Def_RWPI_SqrtLasso_squareLoss

namespace RWPI.SqrtLasso

/-- The empirical mean square error of Proposition 2 and Theorem 1 (pp. 10–11):
`MSE_n(β) = n⁻¹ ∑_{i=1}^n (Y_i − βᵀX_i)²` for training data `(X_i, Y_i)`, `i = 1, …, n`
(indexed by `Fin n`). -/
noncomputable def MSE {d n : ℕ} (X : Fin n → Fin d → ℝ) (Y : Fin n → ℝ) (β : Fin d → ℝ) : ℝ :=
  (n : ℝ)⁻¹ * ∑ i, squareLoss β (X i, Y i)

end RWPI.SqrtLasso


