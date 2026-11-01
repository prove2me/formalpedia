-- Prove2me | Definitions.Def_DelayedGLCB_Assumption1
-- name    : DelayedGLCB_Assumption1
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T08:25:15.580637+00:00
-- url     : https://prove2.me/theorems/91f9ec93-e1ce-42ea-94e2-8310785c9e30
-- title:
--   Assumption 1 (GLCB), the round model and the reward model (2)–(3)
-- statement:
--   Fix an environment with contexts $x_{t,a}$, rewards $y_{t,a}$, delays $D_t$ and exploration draws $\alpha_t$, a horizon $T$, a parameter $\theta^*\in\mathbb R^d$ and an inverse link $g:\mathbb R\to\mathbb R$.
--
--   **Assumption 1 (GLCB)** with constants $\sigma_0,\kappa,L_g,M_g$:
--
--   1. $\lambda_{\min}\big(\mathbb E[\tfrac1K\sum_{a\in[K]}x_{t,a}x_{t,a}']\big)\ge\sigma_0^2$ for every $t\in[T]$;
--   2. $\dot g(x'\theta)\ge\kappa$ whenever $\|x\|\le1$ and $\|\theta-\theta^*\|\le1$;
--   3. $g$ is twice differentiable, $\dot g\le L_g$ and $\ddot g\le M_g$.
--
--   **Round model.** For every $t\in[T]$: every $\|x_{t,a}\|\le1$, $y_{t,a}\in[0,1]$, $D_t\ge0$; the round-$t$ data $(x_t,y_t,\alpha_t)$ is independent of $(x_s,y_s,\alpha_s,D_s)_{s<t}$; $(x_t,y_t)$ has the same law as $(x_1,y_1)$; and $\alpha_t$ is uniform on $[K]$ and independent of $(x_t,y_t)$.
--
--   **Reward model.** For every $t\in[T]$, arm $a$ and $\lambda\in\mathbb R$, almost surely
--   $$
--   \mathbb E\big[\exp\big(\lambda\,(y_{t,a}-g(x_{t,a}'\theta^*))\big)\,\big|\,x_t\big]\le\exp\Big(\frac{\lambda^2\hat\sigma^2}{2}\Big).
--   $$
--
--   These are the standing assumptions of the paper's analysis of DUCB-GLCB: a well-conditioned context distribution, local strong monotonicity of the link around $\theta^*$, and sub-Gaussian rewards with mean $g(x'\theta^*)$.
--
--   **Formalization Note** $\lambda_{\min}$ is the Rayleigh infimum, the expectation of the matrix is taken entry by entry, and $\kappa$ is any lower bound of $\dot g$ on the stated set (the paper's infimum is one); positivity of $\kappa$ is a separate hypothesis. "Drawn iid" is read as freshness of each round with respect to everything before it, including earlier delays. The reward condition is the paper's (3), stated per arm and conditional on the context; the zero-mean condition of (2) follows from it. Measurability of all data is assumed.
-- source:
--   Blanchet, Xu, Zhou, Delay-Adaptive Learning in Generalized Linear Contextual Bandits, arXiv:2003.05174v1, Assumption 1, p.6; §2.1, pp.4–5, (2)–(3); Algorithm 1, p.7

import Mathlib
import Definitions.Def_MostlyExplorationFree_GreedyBandit_Matrix
import Definitions.Def_DelayedGLCB_Env

namespace DelayedGLCB

open MeasureTheory ProbabilityTheory MostlyExplorationFree.GreedyBandit
open scoped ENNReal

/-- The matrix `E[(1/K) Σ_{a∈[K]} x_{t,a} x_{t,a}']` of Assumption 1, entry by entry. -/
noncomputable def contextSecondMoment {Ω : Type*} [MeasurableSpace Ω] {d K : ℕ} (P : Measure Ω)
    (E : Env Ω d K) (t : ℕ) : Matrix (Fin d) (Fin d) ℝ :=
  Matrix.of fun i j => ∫ ω, (1 / (K : ℝ)) * ∑ a, E.x t ω a i * E.x t ω a j ∂P

/-- **Assumption 1 (GLCB).**
Blanchet, Xu, Zhou, arXiv:2003.05174v1, Assumption 1, p.6:
"• `λ_min(E[(1/K) Σ_{a∈[K]} x_{t,a} x_{t,a}']) ≥ σ₀²` for all `t ∈ [T]`.
 • `κ := inf_{‖x‖≤1, ‖θ−θ*‖≤1} ġ(x'θ) > 0`.
 • `g` is twice differentiable. `ġ` and `g̈` are upper bounded by `L_g` and `M_g`, respectively."

**Formalization Note.** `λ_min` is the Rayleigh infimum `lambdaMin` (the smallest eigenvalue of a
symmetric matrix). `κ` is any lower bound of `ġ(x'θ)` on `{‖x‖ ≤ 1, ‖θ − θ*‖ ≤ 1}`; the paper's
infimum is one such bound. Positivity `κ > 0` is a separate hypothesis wherever this is used. "Twice
differentiable" is differentiability of `g` and of `ġ`; the bounds on `ġ` and `g̈` are one-sided upper
bounds, as printed. -/
structure Assumption1 {Ω : Type*} [MeasurableSpace Ω] {d K : ℕ} (P : Measure Ω) (E : Env Ω d K)
    (T : ℕ) (θstar : Fin d → ℝ) (g : ℝ → ℝ) (σ₀ κ Lg Mg : ℝ) : Prop where
  lambdaMin_ge : ∀ t ∈ Finset.Icc 1 T, σ₀ ^ 2 ≤ lambdaMin (contextSecondMoment P E t)
  kappa_le : ∀ x θ : Fin d → ℝ, l2norm x ≤ 1 → l2norm (θ - θstar) ≤ 1 →
    κ ≤ deriv g (x ⬝ᵥ θ)
  differentiable : Differentiable ℝ g
  differentiable_deriv : Differentiable ℝ (deriv g)
  deriv_le : ∀ z, deriv g z ≤ Lg
  deriv2_le : ∀ z, deriv (deriv g) z ≤ Mg

/-- **The round model: bounded data and fresh i.i.d. rounds.**
Blanchet, Xu, Zhou, arXiv:2003.05174v1, §2.1, p.4: "the agent observes a context consisting of a set
of `K` feature vectors `x_t := {x_{t,a} ∈ ℝ^d | a ∈ [K]}`, which is drawn iid from an unknown
distribution `γ` with `‖x_{t,a}‖ ≤ 1`. Each feature vector `x_{t,a}` is associated with an unknown
stochastic reward `y_{t,a} ∈ [0,1]`"; §2.2, p.5: "`D_t` is a non-negative random number"; Algorithm 1,
p.7: "randomly choose `α_t ∈ [K]`".

For `t ∈ [1, T]`:
1. every `x_t, y_t, D_t, α_t` is measurable, `‖x_{t,a}‖ ≤ 1`, `y_{t,a} ∈ [0,1]`, `D_t ≥ 0`;
2. the round-`t` data `(x_t, y_t, α_t)` is independent of `(x_s, y_s, α_s, D_s)_{1 ≤ s < t}`;
3. `(x_t, y_t)` has the same law as `(x_1, y_1)`;
4. `α_t` is uniform on `[K]` and independent of `(x_t, y_t)`.

**Formalization Note.** Items 2–3 read "drawn iid" as freshness of each round's data with respect to
everything before it, including earlier delays; without it the literal independence sentence of p.5
allows `D_s` to depend on a later context. The bounds hold at every `ω`; measurability is the standing
convention. -/
structure RoundModel {Ω : Type*} [MeasurableSpace Ω] {d K : ℕ} (P : Measure Ω) (E : Env Ω d K)
    (T : ℕ) : Prop where
  measurable_x : ∀ t, Measurable (E.x t)
  measurable_y : ∀ t, Measurable (E.y t)
  measurable_D : ∀ t, Measurable (E.D t)
  measurable_α : ∀ t, Measurable (E.α t)
  norm_x_le : ∀ t ω a, l2norm (E.x t ω a) ≤ 1
  y_mem : ∀ t ω a, E.y t ω a ∈ Set.Icc (0 : ℝ) 1
  D_nonneg : ∀ t ω, 0 ≤ E.D t ω
  fresh : ∀ t ∈ Finset.Icc 1 T,
    IndepFun (fun ω => (E.x t ω, E.y t ω, E.α t ω))
      (fun ω => fun s : Finset.Ico 1 t => (E.x s ω, E.y s ω, E.α s ω, E.D s ω)) P
  identDistrib : ∀ t ∈ Finset.Icc 1 T,
    IdentDistrib (fun ω => (E.x t ω, E.y t ω)) (fun ω => (E.x 1 ω, E.y 1 ω)) P P
  α_uniform : ∀ t ∈ Finset.Icc 1 T, ∀ a : Fin K, P (E.α t ⁻¹' {a}) = (K : ℝ≥0∞)⁻¹
  α_indep : ∀ t ∈ Finset.Icc 1 T, IndepFun (E.α t) (fun ω => (E.x t ω, E.y t ω)) P

/-- **The reward model (2)–(3): conditionally `σ̂`-sub-Gaussian noise around `g(x'θ*)`.**
Blanchet, Xu, Zhou, arXiv:2003.05174v1, p.5, (2): "`Y_t = g(X_t'θ*) + ε_t`, where `{ε_t}` are
independent zero-mean noise", and (3): "`E[exp(λε_t) | H_t^0] ≤ exp(λ²σ̂²/2)`. Throughout the paper, we
denote `σ̂ > 0` as the sub-Gaussian parameter of the noise `ε_t`."

For every `t ∈ [1, T]`, arm `a` and `λ ∈ ℝ`,
`E[exp(λ (y_{t,a} − g(x_{t,a}'θ*))) | x_t] ≤ exp(λ²σ̂²/2)` almost surely.

**Formalization Note.** The noise is stated per arm, conditionally on the context `x_t`; with the
freshness of `RoundModel` this gives (3) for the chosen arm given the history `H_t^0`. The zero-mean
condition of (2) is implied by the bound for all `λ` and is not repeated. This is the paper's
Remark 1 setting (2)–(3), which covers the exponential family (1). The conditional expectation is
`MeasureTheory.condExp`; under `RoundModel` and a continuous `g` the integrand is bounded and
measurable, so no junk value occurs. -/
def RewardModel {Ω : Type*} [MeasurableSpace Ω] {d K : ℕ} (P : Measure Ω) (E : Env Ω d K)
    (T : ℕ) (θstar : Fin d → ℝ) (g : ℝ → ℝ) (σhat : ℝ) : Prop :=
  ∀ t ∈ Finset.Icc 1 T, ∀ a : Fin K, ∀ l : ℝ,
    condExp (MeasurableSpace.comap (E.x t) inferInstance) P
        (fun ω => Real.exp (l * (E.y t ω a - g (E.x t ω a ⬝ᵥ θstar))))
      ≤ᵐ[P] fun _ => Real.exp (l ^ 2 * σhat ^ 2 / 2)

end DelayedGLCB


