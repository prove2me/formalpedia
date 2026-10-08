-- Prove2me | Definitions.Def_L0BnB_BigMvsPR_Penalties
-- name    : L0BnB_BigMvsPR_Penalties
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-08T01:27:09.139572+00:00
-- url     : https://prove2.me/theorems/ffe332dc-5ecb-4eb3-ab16-71025f9467b7
-- title:
--   The reverse Huber penalty $\mathcal B$ (4), the penalty $\psi_1$ of Theorem 1 and the gap function $t$ of the proof of Proposition 2
-- statement:
--   Let $\lambda_0, \lambda_2 > 0$ be the $\ell_0$ and ridge regularization parameters of the sparse regression problem and $M > 0$ the Big-M bound. The **reverse Huber penalty** $\mathcal B : \mathbb R \to \mathbb R$ is
--
--   $$\mathcal B(t) = \begin{cases} |t| & |t| \le 1,\\ (t^2+1)/2 & |t| \ge 1.\end{cases}$$
--
--   For a scalar $b$ define the coordinate penalty of the relaxation (6) of $\mathrm{PR}(\infty)$,
--
--   $$\psi_1(b;\lambda_0,\lambda_2) = 2\lambda_0\,\mathcal B\big(b\sqrt{\lambda_2/\lambda_0}\big),$$
--
--   and the function used in the proof of Proposition 2,
--
--   $$t(b) = 2\lambda_0\,\mathcal B\big(b\sqrt{\lambda_2/\lambda_0}\big) - \frac{\lambda_0}{M}|b| - \lambda_2 b^2 .$$
--
--   Thus $t(b)$ is the difference between the coordinate penalty $\psi_1$ of the perspective relaxation $\mathrm{PR}(\infty)$ and the coordinate penalty $\frac{\lambda_0}{M}|b| + \lambda_2 b^2$ of the interval relaxation of the Big-M formulation; its sign on $[-M, M]$ decides which relaxation is stronger.
--
--   **Formalization Note** $\mathcal B$ is `reverseHuber`, written with an `if` on $|t| \le 1$; the two branches agree at $|t| = 1$. The function $t$ is `tGap lam0 lam2 M b`. The functions are total; their values for non-positive parameters are never used, since every theorem assumes $\lambda_0, \lambda_2, M > 0$.
-- source:
--   Hazimeh, Mazumder, Saab, Sparse Regression at Scale: Branch-and-Bound rooted in First-Order Optimization, arXiv:2004.06152v2, p. 6, (4) and Theorem 1 (ψ1); p. 29, Proof of Proposition 2 (t)

import Mathlib
import Definitions.Def_L0BnB_Reduced_ReverseHuber
import Definitions.Def_L0BnB_Strength_Penalties

namespace L0BnB.BigMvsPR

/-- The function `t : ℝ → ℝ` of the proof of Proposition 2 (p. 29):
`t(b) := 2 λ₀ B(b √(λ₂/λ₀)) − (λ₀/M) |b| − λ₂ b²`, i.e. `ψ₁(b; λ₀, λ₂)` minus the
coordinate penalty `(λ₀/M)|b| + λ₂ b²` of the Big-M relaxation (37). -/
noncomputable def tGap (lam0 lam2 M b : ℝ) : ℝ :=
  2 * lam0 * L0BnB.Reduced.reverseHuber (b * Real.sqrt (lam2 / lam0)) - lam0 / M * |b| - lam2 * b ^ 2

end L0BnB.BigMvsPR


