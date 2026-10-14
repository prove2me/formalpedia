-- Prove2me | Definitions.Def_SmoothAmbEq_Gaussian_Model
-- name    : SmoothAmbEq_Gaussian_Model
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-14T04:09:32.855369+00:00
-- url     : https://prove2.me/theorems/19271128-3bc8-4e11-86f8-47355fd0b79e
-- title:
--   §2.1, §5.1, pp. 4, 14–15 — market data, Gaussian prior, ζ(t), CARA utility U, power/log ambiguity function φ
-- statement:
--   This file fixes the data of the Gaussian-prior model of Guan, Liang and Xia (§2.1, p. 4, and §5.1, pp. 14–15).
--
--   An investor trades a bond with constant interest rate $r$ and a stock whose price follows $dS_t/S_t = Z\,dt+\sigma\,dW_t$, where $\sigma>0$ is the volatility and the drift $Z$ is unknown, with Gaussian prior $Z\sim N(\beta_0,\sigma_0^2)$. The horizon is $T>0$. The model data are
--
--   1. the volatility $\sigma>0$, the prior standard deviation $\sigma_0>0$ and the prior mean $\beta_0\in\mathbb R$;
--   2. the interest rate $r\in\mathbb R$ and the horizon $T>0$;
--   3. the CARA coefficient $k>0$ and the ambiguity exponent $\alpha\in\mathbb R$.
--
--   The posterior variance of $Z$ after observing prices up to time $t$ is
--   $$\zeta(t)=\frac{\sigma^2\sigma_0^2}{\sigma^2+t\sigma_0^2}.$$
--   The utility is CARA, $U(x)=-\frac1k e^{-kx}$, and the ambiguity attitude is
--   $$\phi(u)=\begin{cases}-\frac1\alpha(-u)^\alpha,&\alpha\neq0,\\ -\log(-u),&\alpha=0,\end{cases}\qquad u<0,$$
--   with derivative $\phi'(u)=(-u)^{\alpha-1}$ as printed on p. 15. $\phi$ is strictly concave for $\alpha>1$, linear for $\alpha=1$ and strictly convex for $\alpha<1$.
--
--   These are the primitive objects of every statement of the mission.
--
--   **Formalization Note** The paper writes "$\sigma_0\in\mathbb R$"; $\sigma_0>0$ is a standing hypothesis (the prior is nondegenerate, p. 11, and $\zeta$ and (5.17) divide by $\sigma_0$). $\phi$ and $\phi'$ are total functions on $\mathbb R$ but are only applied to negative arguments; $\phi'$ is the printed formula, not the Lean derivative of $\phi$. Powers are real powers (`Real.rpow`).
-- source:
--   Guan, Liang, Xia, Equilibrium Portfolio Selection for Smooth Ambiguity Preferences, arXiv:2302.08181v1, pp. 4, 14–15, §2.1, §5.1

import Mathlib

namespace SmoothAmbEq.Gaussian

/-- The data of the Gaussian-prior model of §2.1 and §5.1 (pp. 4, 14–15): volatility `σ > 0`,
prior standard deviation `σ₀ > 0` and prior mean `β₀` of the unknown drift `Z ∼ N(β₀, σ₀²)`,
interest rate `r`, horizon `T > 0`, CARA coefficient `k > 0`, ambiguity exponent `α ∈ ℝ`. -/
structure Model where
  σ : ℝ
  σ₀ : ℝ
  β₀ : ℝ
  r : ℝ
  T : ℝ
  k : ℝ
  α : ℝ
  hσ : 0 < σ
  hσ₀ : 0 < σ₀
  hT : 0 < T
  hk : 0 < k

namespace Model

variable (M : Model)

/-- The posterior variance `ζ(t) = σ²σ₀² / (σ² + tσ₀²)` (p. 14). -/
noncomputable def ζ (t : ℝ) : ℝ := M.σ ^ 2 * M.σ₀ ^ 2 / (M.σ ^ 2 + t * M.σ₀ ^ 2)

/-- The CARA utility `U(x) = -(1/k) e^{-kx}` (p. 15). -/
noncomputable def U (x : ℝ) : ℝ := -(1 / M.k) * Real.exp (-M.k * x)

/-- The ambiguity function `φ(u) = -(1/α)(-u)^α` for `α ≠ 0` and `-log(-u)` for `α = 0`
(p. 15); it is only ever applied to `u < 0`. -/
noncomputable def φ (u : ℝ) : ℝ :=
  if M.α = 0 then -Real.log (-u) else -(1 / M.α) * (-u) ^ M.α

/-- The derivative `φ'(u) = (-u)^{α-1}` as printed on p. 15 (meaningful for `u < 0`). -/
noncomputable def φ' (u : ℝ) : ℝ := (-u) ^ (M.α - 1)

end Model

end SmoothAmbEq.Gaussian


