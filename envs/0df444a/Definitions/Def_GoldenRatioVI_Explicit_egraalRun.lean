-- Prove2me | Definitions.Def_GoldenRatioVI_Explicit_egraalRun
-- name    : GoldenRatioVI_Explicit_egraalRun
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-27T21:28:29.257985+00:00
-- url     : https://prove2.me/theorems/2fdd5fdc-d605-40a6-9d09-93040c8ffbf6
-- title:
--   Algorithm 1 (EGRAAL): a run of the Explicit Golden Ratio Algorithm
-- statement:
--   Let $\varphi = \frac{\sqrt5+1}{2}$ be the golden ratio. Fix $g:\mathcal E\to(-\infty,+\infty]$, $F:\mathcal E\to\mathcal E$, a parameter $\phi\in(1,\varphi]$ and a cap $\bar\lambda>0$, and put $\rho = \frac1\phi+\frac1{\phi^2}$. A **run of Algorithm 1** consists of sequences $(z^k)$, $(\bar z^k)$ in $\mathcal E$ and $(\lambda_k)$, $(\theta_k)$ in $\mathbb R$ such that $z^0, z^1\in\mathcal E$ are arbitrary, $\lambda_0>0$, $\bar z^0 = z^1$, $\theta_0 = 1$, and for every $k\ge 1$:
--
--   1. the stepsize is
--   $$\lambda_k = \min\Big\{\rho\lambda_{k-1},\ \frac{\phi\theta_{k-1}}{4\lambda_{k-1}}\,\frac{\|z^k-z^{k-1}\|^2}{\|F(z^k)-F(z^{k-1})\|^2},\ \bar\lambda\Big\}, \tag{15}$$
--   with the convention that the middle term is $+\infty$ (so it is dropped from the minimum) when $F(z^k)=F(z^{k-1})$;
--   2. $\bar z^k = \dfrac{(\phi-1)z^k+\bar z^{k-1}}{\phi}$; $\quad$ (16)
--   3. $z^{k+1} = \operatorname{prox}_{\lambda_k g}\big(\bar z^k - \lambda_k F(z^k)\big)$; $\quad$ (17)
--   4. $\theta_k = \dfrac{\lambda_k}{\lambda_{k-1}}\,\phi$.
--
--   The method needs one evaluation of $F$ and one proximal step per iteration and no knowledge of a Lipschitz constant of $F$.
--
--   **Formalization Note** The recursion is written for index $k+1$ with $k\ge0$, so no natural-number subtraction occurs. The paper's convention $0/0=+\infty$ is modelled by the two fields `step_of_eq` / `step_of_ne`: when $F(z^k)=F(z^{k-1})$ the step is $\min\{\rho\lambda_{k-1},\bar\lambda\}$. No condition such as $F(z^1)\ne F(z^0)$ or $\lambda_0\le\bar\lambda$ is imposed. The prox step is the argmin predicate `IsProxPoint` applied to $\lambda_k g$.
-- source:
--   Malitsky, Golden Ratio Algorithms for Variational Inequalities, preprint (Optimization Online 6598, 2018), p. 5, Algorithm 1, Eqs. (15)–(17)

import Mathlib
import Definitions.Def_GoldenRatioVI_Shared_IsProxPoint

namespace GoldenRatioVI.Explicit

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- The contraction factor `ρ = 1/ϕ + 1/ϕ²` of Algorithm 1 (Malitsky, p. 5). -/
noncomputable def rho (ϕ : ℝ) : ℝ := 1 / ϕ + 1 / ϕ ^ 2

/-- A run of Algorithm 1, the Explicit Golden Ratio Algorithm (EGRAAL), of Malitsky (p. 5),
with parameters `ϕ ∈ (1, φ]` (`φ` the golden ratio) and `λ̄ > 0`, producing the sequences
`z, zbar : ℕ → E` and `lam, theta : ℕ → ℝ`.

Input: `z 0, z 1` arbitrary, `lam 0 = λ₀ > 0`, `zbar 0 = z 1`, `theta 0 = 1`. For every
`k ≥ 1` (written `k + 1` below, `k ≥ 0`):
1. step (15): `λ_k = min {ρ λ_{k−1}, (ϕ θ_{k−1} / (4 λ_{k−1})) ‖z^k − z^{k−1}‖² / ‖F(z^k) − F(z^{k−1})‖², λ̄}`,
   where the middle term is `+∞` (and hence dropped) when `F(z^k) = F(z^{k−1})`
   (the paper's convention `0/0 = +∞`): fields `step_of_eq` and `step_of_ne`;
2. (16): `z̄^k = ((ϕ − 1) z^k + z̄^{k−1}) / ϕ`;
3. (17): `z^{k+1} = prox_{λ_k g}(z̄^k − λ_k F(z^k))`;
4. `θ_k = (λ_k / λ_{k−1}) ϕ`. -/
structure IsEGRAALRun (g : E → EReal) (F : E → E) (ϕ lamBar : ℝ)
    (z zbar : ℕ → E) (lam theta : ℕ → ℝ) : Prop where
  one_lt_phi : 1 < ϕ
  phi_le_goldenRatio : ϕ ≤ Real.goldenRatio
  lamBar_pos : 0 < lamBar
  lam_zero_pos : 0 < lam 0
  zbar_zero : zbar 0 = z 1
  theta_zero : theta 0 = 1
  step_of_eq : ∀ k : ℕ, F (z (k + 1)) = F (z k) →
    lam (k + 1) = min (rho ϕ * lam k) lamBar
  step_of_ne : ∀ k : ℕ, F (z (k + 1)) ≠ F (z k) →
    lam (k + 1) = min (min (rho ϕ * lam k)
      (ϕ * theta k / (4 * lam k) * (‖z (k + 1) - z k‖ ^ 2 / ‖F (z (k + 1)) - F (z k)‖ ^ 2)))
      lamBar
  zbar_succ : ∀ k : ℕ, zbar (k + 1) = (1 / ϕ) • ((ϕ - 1) • z (k + 1) + zbar k)
  prox_step : ∀ k : ℕ, GoldenRatioVI.Shared.IsProxPoint (fun x => ((lam (k + 1) : ℝ) : EReal) * g x)
    (zbar (k + 1) - lam (k + 1) • F (z (k + 1))) (z (k + 2))
  theta_succ : ∀ k : ℕ, theta (k + 1) = lam (k + 1) / lam k * ϕ

end GoldenRatioVI.Explicit


