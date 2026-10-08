-- Prove2me | Definitions.Def_SlowConvergence_ARC_Method
-- name    : SlowConvergence_ARC_Method
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-08T06:41:32.148282+00:00
-- url     : https://prove2.me/theorems/f44e2764-8d04-45c9-bdc4-379a97935fd2
-- title:
--   The cubic model (1.3), the ratio $\rho_k$ and a run of the ARC algorithm in one dimension
-- statement:
--   Let $f:\mathbb R\to\mathbb R$ and write $g(x) = f'(x)$, $H(x) = f''(x)$. Given a point $x_k$ and a regularization weight $\sigma_k \ge 0$, the **cubic model** (1.3) of $f$ at $x_k$ is
--   $$m_k(x_k+s) = f(x_k) + g(x_k)\,s + \tfrac12 H(x_k)\,s^2 + \tfrac13\sigma_k |s|^3, \qquad s\in\mathbb R,$$
--   the quadratic Taylor model with exact second-order information plus a cubic regularization term. For a step $s_k$ the ratio of achieved to predicted decrease is
--   $$\rho_k = \frac{f(x_k) - f(x_k+s_k)}{f(x_k) - m_k(x_k+s_k)} .$$
--
--   A **run of the Adaptive Regularization with Cubics (ARC) algorithm** on $f$, with parameters $\gamma_2 \ge \gamma_1 > 1$ and $1 > \eta_2 \ge \eta_1 > 0$ and initial weight $\sigma_0 > 0$, consists of iterates $x_k$, steps $s_k$ and weights $\sigma_k$ such that for every $k \ge 0$:
--
--   1. $s_k$ is a global minimizer of the cubic model: $m_k(x_k+s_k) \le m_k(x_k+s)$ for all $s\in\mathbb R$;
--   2. $x_{k+1} = x_k + s_k$ if $\rho_k \ge \eta_1$, and $x_{k+1} = x_k$ otherwise;
--   3. $\sigma_{k+1}\in(0,\sigma_k]$ if $\rho_k > \eta_2$ (very successful iteration), $\sigma_{k+1}\in[\sigma_k,\gamma_1\sigma_k]$ if $\eta_1\le\rho_k\le\eta_2$ (successful iteration), and $\sigma_{k+1}\in[\gamma_1\sigma_k,\gamma_2\sigma_k]$ otherwise.
--
--   This is the method whose worst-case behaviour the mission's goal theorem pins down from below.
--
--   **Formalization Note** The paper does not restate the algorithm; it says (p. 2) that the new iterate is found "by globally minimizing the cubic model (1.3)" and refers to Cartis, Gould and Toint (2009a). The acceptance test and the weight update are taken from Algorithm 2.1 of that paper; only the step rule (an exact global minimizer of the model) is this paper's. The printed (1.3) has $s_k$ inside the cubic model, a typo for the trial step $s$. The run is a predicate (the step and the new weight are choices); the parameter restrictions are part of it. Lean's convention $a/0 = 0$ gives $\rho_k = 0$ when the model predicts no decrease.
-- source:
--   Cartis, Gould & Toint, On the complexity of steepest descent, Newton's and regularized Newton's methods, preprint 15 Oct 2009, p. 2, (1.3); acceptance and update rules from Algorithm 2.1 of Cartis, Gould and Toint (2009a), cited on p. 2

import Mathlib

namespace SlowConvergence.ARC

/-- The cubic model (1.3), p. 2, of Cartis, Gould & Toint, *On the complexity of steepest descent,
Newton's and regularized Newton's methods for nonconvex unconstrained optimization*, preprint
15 Oct 2009, in one dimension and with exact second-order information:
`m_k(x_k + s) = f(x_k) + g_k s + ½ H_k s² + ⅓ σ_k |s|³`, where `g_k = f'(x_k)` and `H_k = f''(x_k)`.
Here `model f σ x s` is the value at the trial step `s` from the point `x` with weight `σ`. -/
noncomputable def model (f : ℝ → ℝ) (σ x s : ℝ) : ℝ :=
  f x + deriv f x * s + 1 / 2 * deriv (deriv f) x * s ^ 2 + σ / 3 * |s| ^ 3

/-- The ratio of actual to predicted decrease of ARC (Algorithm 2.1 of Cartis, Gould and Toint
(2009a), cited on p. 2): `ρ_k = (f(x_k) − f(x_k + s_k)) / (f(x_k) − m_k(x_k + s_k))`.
(Lean's `a / 0 = 0` makes `ρ_k = 0` when the model predicts no decrease.) -/
noncomputable def rho (f : ℝ → ℝ) (σ x s : ℝ) : ℝ :=
  (f x - f (x + s)) / (f x - model f σ x s)

/-- A run of the Adaptive Regularization with Cubics (ARC) algorithm on `f : ℝ → ℝ`, in the variant
used by the paper (p. 2: "the new iterate is found at iteration k by globally minimizing the cubic
model (1.3)"), with the acceptance and weight-update rules of Algorithm 2.1 of Cartis, Gould and Toint
(2009a), cited on p. 2. Parameters `γ₂ ≥ γ₁ > 1`, `1 > η₂ ≥ η₁ > 0`, initial weight `σ₀ = σ 0 > 0`;
iterates `x k`, steps `s k`, weights `σ k`. For every `k`:
1. `s_k` is a global minimizer of the cubic model `s ↦ m_k(x_k + s)` (exact Hessian);
2. `ρ_k` is the ratio `rho`;
3. `x_{k+1} = x_k + s_k` if `ρ_k ≥ η₁`, and `x_{k+1} = x_k` otherwise;
4. `σ_{k+1} ∈ (0, σ_k]` if `ρ_k > η₂` (very successful), `σ_{k+1} ∈ [σ_k, γ₁σ_k]` if
   `η₁ ≤ ρ_k ≤ η₂` (successful), and `σ_{k+1} ∈ [γ₁σ_k, γ₂σ_k]` otherwise (unsuccessful). -/
def IsARCRun (f : ℝ → ℝ) (γ₁ γ₂ η₁ η₂ : ℝ) (x s σ : ℕ → ℝ) : Prop :=
  1 < γ₁ ∧ γ₁ ≤ γ₂ ∧ 0 < η₁ ∧ η₁ ≤ η₂ ∧ η₂ < 1 ∧ 0 < σ 0 ∧
  (∀ k, ∀ s' : ℝ, model f (σ k) (x k) (s k) ≤ model f (σ k) (x k) s') ∧
  (∀ k, x (k + 1) = if η₁ ≤ rho f (σ k) (x k) (s k) then x k + s k else x k) ∧
  (∀ k,
    (η₂ < rho f (σ k) (x k) (s k) → 0 < σ (k + 1) ∧ σ (k + 1) ≤ σ k) ∧
    (η₁ ≤ rho f (σ k) (x k) (s k) ∧ rho f (σ k) (x k) (s k) ≤ η₂ →
      σ k ≤ σ (k + 1) ∧ σ (k + 1) ≤ γ₁ * σ k) ∧
    (rho f (σ k) (x k) (s k) < η₁ → γ₁ * σ k ≤ σ (k + 1) ∧ σ (k + 1) ≤ γ₂ * σ k))

end SlowConvergence.ARC


