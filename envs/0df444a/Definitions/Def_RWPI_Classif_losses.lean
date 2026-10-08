-- Prove2me | Definitions.Def_RWPI_Classif_losses
-- name    : RWPI_Classif_losses
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-05T17:33:03.545+00:00
-- url     : https://prove2.me/theorems/47ea84c7-f2a7-4fcd-b6b2-d291b174f984
-- title:
--   The log-exponential (logistic) loss (Example 2) and the hinge loss (Theorem 2)
-- statement:
--   For a coefficient vector $\beta \in \mathbb R^d$ and a predictor–response pair $(x,y) \in \mathbb R^d \times \mathbb R$, with $\beta^T x = \sum_j \beta_j x_j$:
--
--   1. the **log-exponential loss** (negative log-likelihood of the logistic model) is
--   $$l(x,y;\beta) = \log\big(1 + \exp(-y\,\beta^T x)\big);$$
--   2. the **hinge loss** of the support vector machine is
--   $$l(x,y;\beta) = \big(1 - y\,\beta^T x\big)^+ = \max\{0,\ 1 - y\,\beta^T x\}.$$
--
--   Both losses are nonnegative and continuous in $(x,y)$. In binary classification the response takes values $y \in \{-1,+1\}$; the definitions themselves accept any real response.
--
--   **Formalization Note** `logLoss β z` and `hingeLoss β z` take `z : (Fin d → ℝ) × ℝ`, and $\beta^T x$ is `β ⬝ᵥ x` (`dotProduct`).
-- source:
--   Blanchet, Kang & Murthy, Robust Wasserstein Profile Inference and Applications to Machine Learning, arXiv:1610.05627v4, p. 9, Example 2; p. 11, Theorem 2

import Mathlib

namespace RWPI.Classif

/-- Example 2, p. 9: the log-exponential (logistic) loss
`l(x, y; β) = log(1 + exp(−y · βᵀx))`. -/
noncomputable def logLoss {d : ℕ} (β : Fin d → ℝ) (z : (Fin d → ℝ) × ℝ) : ℝ :=
  Real.log (1 + Real.exp (-(z.2 * (β ⬝ᵥ z.1))))

/-- Theorem 2, p. 11: the hinge loss of the support vector machine, `(1 − y · βᵀx)⁺`. -/
def hingeLoss {d : ℕ} (β : Fin d → ℝ) (z : (Fin d → ℝ) × ℝ) : ℝ :=
  max 0 (1 - z.2 * (β ⬝ᵥ z.1))

end RWPI.Classif


