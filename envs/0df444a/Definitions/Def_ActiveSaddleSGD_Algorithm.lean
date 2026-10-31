-- Prove2me | Definitions.Def_ActiveSaddleSGD_Algorithm
-- name    : ActiveSaddleSGD_Algorithm
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T04:09:21.261598+00:00
-- url     : https://prove2.me/theorems/45ce574a-90f7-493b-bfad-1e3548f83fe0
-- title:
--   The stochastic subgradient iteration (10) and Assumption 1
-- statement:
--   On a probability space with a filtration $(\mathcal F_n)$, the **stochastic subgradient iteration** is
--   $$
--   x_{n+1}=x_n-\gamma_nv_n+\gamma_n\eta_{n+1},\qquad v_n\in\partial f(x_n),
--   $$
--   with deterministic $\gamma_n>0$, where $(v_n)$, $(\eta_n)$ are adapted and $x_0$ is $\mathcal F_0$-measurable.
--
--   **Assumption 1** adds that $f$ is path differentiable and that there are $c_1,c_2>0$ and $\alpha\in(1/2,1]$ with
--   $$
--   \frac{c_1}{n^\alpha}\le\gamma_n\le\frac{c_2}{n^\alpha}\qquad(n\ge1).
--   $$
--
--   **Formalization Note** The selection $v_n$ is required for every $n$ and every $\omega$. `IsPathDifferentiable` is the published definition, over Lipschitz curves on $\mathbb R$, and it contains local Lipschitz continuity. $\gamma_0>0$ is otherwise free, and $\alpha=1$ is included. The noise index is $n+1$ and $\eta_0$ is not used.
-- source:
--   Bianchi, Hachem & Schechtman, Stochastic Subgradient Descent Escapes Active Strict Saddles on Weakly Convex Functions, arXiv:2108.02072v4, §4, p.11, equation (10) and Assumption 1

import Mathlib
import Definitions.Def_PathoSubgrad_Circle_Setting

open PathoSubgrad.Circle MeasureTheory

namespace ActiveSaddleSGD

variable {d : ℕ} {Ω : Type*} {mΩ : MeasurableSpace Ω}

/-- Bianchi, Hachem & Schechtman, arXiv:2108.02072v4, §4, p.11, equation (10) with Assumption 1 ii)
and iii): `x_{n+1} = x_n − γ_n v_n + γ_n η_{n+1}` with deterministic `γ_n > 0`, `v_n ∈ ∂f(x_n)`,
`(v_n)`, `(η_n)` adapted to `(𝓕_n)` and `x₀` `𝓕₀`-measurable.

**Formalization Note** `StronglyAdapted` is the adaptedness of Mathlib in which each variable is
strongly measurable. The noise index is `n + 1` and `η 0` is unused. -/
structure IsSGDRun (f : EuclideanSpace ℝ (Fin d) → ℝ) (ℱ : Filtration ℕ mΩ)
    (x v η : ℕ → Ω → EuclideanSpace ℝ (Fin d)) (γ : ℕ → ℝ) : Prop where
  recursion : ∀ n ω, x (n + 1) ω = x n ω - γ n • v n ω + γ n • η (n + 1) ω
  step_pos : ∀ n, 0 < γ n
  subgrad : ∀ n ω, v n ω ∈ clarkeSubdiff f (x n ω)
  adapted_v : StronglyAdapted ℱ v
  adapted_η : StronglyAdapted ℱ η
  measurable_x₀ : StronglyMeasurable[ℱ 0] (x 0)

/-- Bianchi, Hachem & Schechtman, arXiv:2108.02072v4, Assumption 1, p.11: `f` is path differentiable,
the iterates are a run of (10), and `c₁ / n^α ≤ γ_n ≤ c₂ / n^α` for `n ≥ 1`, with `c₁, c₂ > 0` and
`α ∈ (1/2, 1]`.

**Formalization Note** The published `IsPathDifferentiable` carries local Lipschitz continuity. It
quantifies over Lipschitz curves on `ℝ`, which Definition 1 (absolutely continuous curves on
`(0,1)`) implies. `γ₀ > 0` is otherwise free, as on the page; `α = 1` is included. -/
structure Assumption1 (f : EuclideanSpace ℝ (Fin d) → ℝ) (ℱ : Filtration ℕ mΩ)
    (x v η : ℕ → Ω → EuclideanSpace ℝ (Fin d)) (γ : ℕ → ℝ) (c₁ c₂ α : ℝ) : Prop where
  pathDifferentiable : IsPathDifferentiable f
  run : IsSGDRun f ℱ x v η γ
  c₁_pos : 0 < c₁
  c₂_pos : 0 < c₂
  half_lt : 1 / 2 < α
  le_one : α ≤ 1
  step_lower : ∀ n : ℕ, 1 ≤ n → c₁ / (n : ℝ) ^ α ≤ γ n
  step_upper : ∀ n : ℕ, 1 ≤ n → γ n ≤ c₂ / (n : ℝ) ^ α

end ActiveSaddleSGD


