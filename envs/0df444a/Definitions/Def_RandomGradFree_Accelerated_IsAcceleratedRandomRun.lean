-- Prove2me | Definitions.Def_RandomGradFree_Accelerated_IsAcceleratedRandomRun
-- name    : RandomGradFree_Accelerated_IsAcceleratedRandomRun
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-28T10:06:21.064012+00:00
-- url     : https://prove2.me/theorems/0884cc21-35c3-4e03-aaa5-21d566b0275f
-- title:
--   A run of the accelerated random method $\mathcal{FG}_\mu$ (Eq. (60))
-- statement:
--   Fix $f : E \to \mathbb R$, a smoothing parameter $\mu$, a convexity parameter $\tau$, step parameters $\theta$ and $h$, and a starting point $x_0 \in E$. On a probability space $(\Omega, \mathbb P)$, a **run of method $\mathcal{FG}_\mu$** consists of deterministic scalar sequences $(\gamma_k)$, $(\alpha_k)$, random directions $(u_k)$ and random points $(x_k)$, $(v_k)$ such that:
--
--   1. the directions $u_0, u_1, \dots$ are independent, measurable, and each has the standard Gaussian law on $E$;
--   2. $\gamma_0 > 0$ and $\gamma_0 \ge \tau$;
--   3. for every $k \ge 0$ (step a)), $\alpha_k > 0$ and
--   $$
--   \theta^{-1}\alpha_k^2 = (1-\alpha_k)\gamma_k + \alpha_k\tau \equiv \gamma_{k+1};
--   $$
--   4. $x_0 = v_0$ is the given starting point;
--   5. for every $k \ge 0$ (steps b) and d)), with
--   $$
--   \lambda_k = \frac{\alpha_k}{\gamma_{k+1}}\tau, \qquad \beta_k = \frac{\alpha_k\gamma_k}{\gamma_k + \alpha_k\tau}, \qquad y_k = (1-\beta_k)x_k + \beta_k v_k,
--   $$
--   and the oracle $B^{-1}g_\mu(y_k)$ evaluated in the direction $u_k$,
--   $$
--   x_{k+1} = y_k - h\,B^{-1}g_\mu(y_k), \qquad v_{k+1} = (1-\lambda_k)v_k + \lambda_k y_k - \frac{\theta}{\alpha_k}B^{-1}g_\mu(y_k).
--   $$
--
--   This is the accelerated (fast-gradient) scheme of Nesterov with the gradient replaced by the random finite-difference oracle; Theorem 9 bounds its expected objective values.
--
--   **Formalization Note** The file also defines $\lambda_k$ (`lam`), $\beta_k$ (`beta`) and the map $(x_k, v_k) \mapsto y_k$ (`extrap`). The parameters $\theta$ and $h$ are left free here and are pinned to $\theta_n$ and $h_n$ in Theorem 9. The equations of step a) are hypotheses; since $\theta^{-1}\alpha^2 + (\gamma_k - \tau)\alpha - \gamma_k$ has exactly one positive root when $\gamma_k > 0$, such sequences always exist. "Independent" is `iIndepFun` of the whole sequence.
-- source:
--   Nesterov, Spokoiny, Random Gradient-Free Minimization of Convex Functions, Found. Comput. Math. 17 (2017), p. 548, Section 6, Method FG_μ, Eq. (60)

import Mathlib
import Definitions.Def_RandomGradFree_Shared_oracle

namespace RandomGradFree.Accelerated

open MeasureTheory ProbabilityTheory

/-- The coefficient `λ_k = (α_k / γ_{k+1}) τ` of step b) of method `FG_μ`
(Nesterov–Spokoiny, Eq. (60), p. 548). -/
noncomputable def lam (τ : ℝ) (γ α : ℕ → ℝ) (k : ℕ) : ℝ :=
  α k / γ (k + 1) * τ

/-- The coefficient `β_k = α_k γ_k / (γ_k + α_k τ)` of step b) of method `FG_μ`
(Nesterov–Spokoiny, Eq. (60), p. 548). -/
noncomputable def beta (τ : ℝ) (γ α : ℕ → ℝ) (k : ℕ) : ℝ :=
  α k * γ k / (γ k + α k * τ)

/-- The extrapolated point `y_k = (1 - β_k) x_k + β_k v_k` of step b) of method `FG_μ`
(Nesterov–Spokoiny, Eq. (60), p. 548), as a function of the current points `x_k`, `v_k`. -/
noncomputable def extrap {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (τ : ℝ) (γ α : ℕ → ℝ) (k : ℕ) (xk vk : E) : E :=
  (1 - beta τ γ α k) • xk + beta τ γ α k • vk

/-- A run of the accelerated random method `FG_μ` (Nesterov–Spokoiny, Eq. (60), p. 548) with
parameters `θ`, `h`, strong convexity parameter `τ` and starting point `x₀`, on the probability
space `(Ω, P)`.

* The directions `u k` are independent, each a measurable random vector with the standard
  Gaussian law on `E` (step c)).
* The deterministic scalar sequences `γ` and `α` satisfy `γ_0 > 0`, `γ_0 ≥ τ`, and for every
  `k`: `α_k > 0` and `θ⁻¹ α_k² = (1 - α_k) γ_k + α_k τ = γ_{k+1}` (step a)).
* `x_0 = v_0 = x₀`, and for every `k` and outcome `ω`, with
  `y_k = extrap τ γ α k (x_k) (v_k) = (1 - β_k) x_k + β_k v_k` (step b)) and the oracle evaluated at `y_k` in the direction
  `u_k`: `x_{k+1} = y_k - h B⁻¹ g_μ(y_k)` and
  `v_{k+1} = (1 - λ_k) v_k + λ_k y_k - (θ / α_k) B⁻¹ g_μ(y_k)` (step d)). -/
structure IsAcceleratedRandomRun {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E]
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (f : E → ℝ) (μ τ θ h : ℝ) (x₀ : E) (γ α : ℕ → ℝ)
    (u x v : ℕ → Ω → E) : Prop where
  measurable_dir : ∀ k, Measurable (u k)
  indep_dir : iIndepFun u P
  law_dir : ∀ k, P.map (u k) = stdGaussian E
  gamma_zero_pos : 0 < γ 0
  tau_le_gamma_zero : τ ≤ γ 0
  alpha_pos : ∀ k, 0 < α k
  alpha_eq : ∀ k, α k ^ 2 / θ = (1 - α k) * γ k + α k * τ
  gamma_succ : ∀ k, γ (k + 1) = (1 - α k) * γ k + α k * τ
  init_x : x 0 = fun _ => x₀
  init_v : v 0 = fun _ => x₀
  step_x : ∀ k ω,
    x (k + 1) ω =
      extrap τ γ α k (x k ω) (v k ω)
        - h • RandomGradFree.Shared.oracle f μ (extrap τ γ α k (x k ω) (v k ω)) (u k ω)
  step_v : ∀ k ω,
    v (k + 1) ω =
      (1 - lam τ γ α k) • v k ω + lam τ γ α k • (extrap τ γ α k (x k ω) (v k ω))
        - (θ / α k) • RandomGradFree.Shared.oracle f μ (extrap τ γ α k (x k ω) (v k ω)) (u k ω)

end RandomGradFree.Accelerated


