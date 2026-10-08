-- Prove2me | Definitions.Def_L0BnB_Strength_Penalties
-- name    : L0BnB_Strength_Penalties
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-08T00:20:44.175169+00:00
-- url     : https://prove2.me/theorems/2d5ed9a2-2725-4e85-a0ad-4f370a897cb8
-- title:
--   The gap function $h(\lambda_0,\lambda_2,M)$ of Proposition 1
-- statement:
--   Let $\lambda_0, \lambda_2 > 0$ be the $\ell_0$ and ridge regularization parameters of $\ell_0\ell_2$-regularized least squares and $M > 0$ the Big-M bound. The function of Proposition 1 is
--
--   $$h(\lambda_0,\lambda_2,M) = \frac{\lambda_0}{M} + \lambda_2 M - 2\sqrt{\lambda_0\lambda_2}.$$
--
--   It is the difference between the slope $\lambda_0/M+\lambda_2M$ of the $\ell_1$ penalty $\psi_2$ (used by the reduced perspective relaxation (5) when $\sqrt{\lambda_0/\lambda_2} > M$) and the slope $2\sqrt{\lambda_0\lambda_2}$ of the reverse Huber penalty $\psi_1$ near the origin, the penalty of the relaxation (6) of $\mathrm{PR}(\infty)$. Proposition 1 bounds the gap $V_{\mathrm{PR}(M)} - V_{\mathrm{PR}(\infty)}$ from below by $h(\lambda_0,\lambda_2,M)\,\|\beta^*\|_1$.
--
--   **Formalization Note** The function is named `hGap`. It is total in its arguments; its values for non-positive parameters are never used, since every theorem that uses it assumes $\lambda_0,\lambda_2,M > 0$. The module also imports the reverse Huber penalty and the penalties $\psi_1,\psi_2,\psi$ of Theorem 1 (`L0BnB.Reduced`), which the statements of Proposition 1 use alongside $h$.
-- source:
--   Hazimeh, Mazumder, Saab, Sparse Regression at Scale: Branch-and-Bound rooted in First-Order Optimization, arXiv:2004.06152v2, p. 7, Proposition 1 (h)

import Mathlib
import Definitions.Def_L0BnB_Reduced_ReverseHuber
import Definitions.Def_L0BnB_Reduced_Setup

namespace L0BnB.Strength

/-- `h(λ₀, λ₂, M) = λ₀/M + λ₂ M − 2 √(λ₀ λ₂)` (Proposition 1, p. 7). -/
noncomputable def hGap (lam0 lam2 M : ℝ) : ℝ :=
  lam0 / M + lam2 * M - 2 * Real.sqrt (lam0 * lam2)

end L0BnB.Strength


