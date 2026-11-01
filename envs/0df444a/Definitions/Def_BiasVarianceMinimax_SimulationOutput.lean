-- Prove2me | Definitions.Def_BiasVarianceMinimax_SimulationOutput
-- name    : BiasVarianceMinimax_SimulationOutput
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T11:30:01.567803+00:00
-- url     : https://prove2.me/theorems/da2e8d89-2ff8-4854-80a1-e27500b58763
-- title:
--   The class $\Theta$ of simulation outputs
-- statement:
--   Fix $q_1,q_2>0$. An element of the class $\Theta$ describes a simulation that estimates a real number $\theta$ with a tuning parameter $\delta>0$. One run at $\delta$ outputs
--
--   $$\hat\theta(\delta)=\theta+b(\delta)+v(\delta),\qquad b(\delta)=B\delta^{q_1}+o(\delta^{q_1}),\qquad v(\delta)=\frac{\varepsilon(\delta)}{\delta^{q_2}}\qquad(\delta\to 0),$$
--
--   where $B\neq 0$ is a constant, $\varepsilon(\delta)$ is a centered random variable, and $\sigma^2(\delta)=\mathrm{Var}(\varepsilon(\delta))\to\sigma^2>0$. The constants $B$, $\sigma^2$ and the higher-order terms are arbitrary, which is what makes $\Theta$ the adversary's set in the minimax problem.
--
--   Concretely, an element consists of:
--
--   1. the numbers $\theta$, $B\neq 0$ and $\sigma^2>0$;
--   2. for every $\delta>0$, a probability law on $\mathbb R$ with finite second moment, the law of $\hat\theta(\delta)$;
--   3. the requirement $b(\delta)-B\delta^{q_1}=o(\delta^{q_1})$ as $\delta\downarrow 0$, with $b(\delta)=\mathbb E\hat\theta(\delta)-\theta$;
--   4. the requirement $\delta^{2q_2}\mathrm{Var}\,\hat\theta(\delta)\to\sigma^2$ as $\delta\downarrow 0$.
--
--   The auxiliary `SimulationOutput.bias` is $b(\delta)$. Every mean squared error of the mission is computed from these laws.
--
--   **Formalization Note** A model is $\theta$ with a family of laws, read only at $\delta>0$. Then $\varepsilon(\delta)=\delta^{q_2}(\hat\theta(\delta)-\theta-b(\delta))$, so $\mathbb E\varepsilon(\delta)=0$ holds by construction and $\mathrm{Var}\,\varepsilon(\delta)=\delta^{2q_2}\mathrm{Var}\,\hat\theta(\delta)$. The variance is finite at every $\delta>0$, not only near $0$, because a run at any positive $\delta$ can occur.
-- source:
--   Lam, Zhang & Zhang, arXiv:1902.04673v1, (7) and Assumption 1, p.7; (11), p.10

import Mathlib

open MeasureTheory ProbabilityTheory Filter Topology Asymptotics

namespace BiasVarianceMinimax

/-- The class `Θ` of simulation outputs for fixed `q₁, q₂`.
Lam, Zhang & Zhang, arXiv:1902.04673v1, §3, (7) and Assumption 1, p.7, and §4.1, (11), p.10.

An element consists of the estimand `θ`, the constants `B ≠ 0` and `σ² > 0`, and for every tuning
parameter `δ > 0` the law of one simulation run `θ̂(δ) = θ + b(δ) + ε(δ)/δ^q₂`.

**Formalization Note.** The model is `θ` together with a family of laws, read only at `δ > 0`; the
values of `law` at `δ ≤ 0` are never used. The bias is `b(δ) = E θ̂(δ) - θ` (p.2) and the noise is
`ε(δ) = δ^q₂ (θ̂(δ) - θ - b(δ))`, so `E ε(δ) = 0` holds by construction and
`Var ε(δ) = δ^(2 q₂) Var θ̂(δ)`. The field `memLp` says that `σ²(δ) = Var ε(δ)` is a finite real
number at every `δ > 0`, not only near `0`, since a run at any positive `δ` can occur. All mean
squared errors are computed from these laws. -/
structure SimulationOutput (q₁ q₂ : ℝ) where
  /-- The estimand `θ`. -/
  θ : ℝ
  /-- The leading bias constant `B`. -/
  B : ℝ
  /-- The limiting noise variance `σ²`. -/
  σsq : ℝ
  /-- The law of one run `θ̂(δ)`, read only at `δ > 0`. -/
  law : ℝ → Measure ℝ
  B_ne_zero : B ≠ 0
  σsq_pos : 0 < σsq
  isProbabilityMeasure : ∀ δ : ℝ, 0 < δ → IsProbabilityMeasure (law δ)
  memLp : ∀ δ : ℝ, 0 < δ → MemLp id 2 (law δ)
  /-- `b(δ) = B δ^q₁ + o(δ^q₁)` as `δ → 0`. -/
  bias_isLittleO :
    (fun δ : ℝ => ((∫ x, x ∂law δ) - θ) - B * δ ^ q₁) =o[𝓝[>] (0 : ℝ)] fun δ : ℝ => δ ^ q₁
  /-- `Var ε(δ) = δ^(2 q₂) Var θ̂(δ) → σ²` as `δ → 0`. -/
  variance_tendsto :
    Tendsto (fun δ : ℝ => δ ^ (2 * q₂) * variance id (law δ)) (𝓝[>] (0 : ℝ)) (𝓝 σsq)

/-- The bias `b(δ) = E θ̂(δ) - θ` of one run. Lam, Zhang & Zhang, arXiv:1902.04673v1, p.2 and (7), p.7. -/
noncomputable def SimulationOutput.bias {q₁ q₂ : ℝ} (M : SimulationOutput q₁ q₂) (δ : ℝ) : ℝ :=
  (∫ x, x ∂M.law δ) - M.θ

end BiasVarianceMinimax


