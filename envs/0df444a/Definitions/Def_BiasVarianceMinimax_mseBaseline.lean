-- Prove2me | Definitions.Def_BiasVarianceMinimax_mseBaseline
-- name    : BiasVarianceMinimax_mseBaseline
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T11:30:38.891168+00:00
-- url     : https://prove2.me/theorems/302029e5-c83f-4d1f-b252-d42e0374daeb
-- title:
--   $\mathrm{MSE}_0$: the mean squared error of the sample average
-- statement:
--   For a model in $\Theta$, the sample average of $n$ independent runs at the one parameter $\delta$ is $\bar\theta_n=\frac1n\sum_{j=1}^n\hat\theta_j(\delta)$, and `mseAverage` is its mean squared error $\mathbb E(\bar\theta_n-\theta)^2$. The baseline of the paper takes $\delta=d(n+n_0)^{-\alpha}$:
--
--   $$\mathrm{MSE}_0(\hat\theta(\cdot),d)=\mathbb E\Big(\frac1n\sum_{j=1}^n\hat\theta_j\big(d(n+n_0)^{-\alpha}\big)-\theta\Big)^2 .$$
--
--   This is the denominator of the risk ratio.
--
--   **Formalization Note** The expectation is the integral of the squared error under the product over `Fin n` of the law of one run, an honest expectation and not a bias-variance formula.
-- source:
--   Lam, Zhang & Zhang, arXiv:1902.04673v1, §3, p.8; §4.1, p.10; §4.2, p.11

import Mathlib
import Definitions.Def_BiasVarianceMinimax_SimulationOutput
import Definitions.Def_BiasVarianceMinimax_deltaGrid

open MeasureTheory

namespace BiasVarianceMinimax

/-- The mean squared error `E(θ̄ₙ - θ)²` of the sample average of `n` independent runs, all at the one
tuning parameter `δ`. Lam, Zhang & Zhang, arXiv:1902.04673v1, §3, p.8.

**Formalization Note.** The independent runs are the coordinates under the product measure over
`Fin n`. The integrand is integrable (`Integrable` is proved from `SimulationOutput.memLp` in the
verification file), so this is the true expectation and not the junk value `0`. -/
noncomputable def mseAverage {q₁ q₂ : ℝ} (M : SimulationOutput q₁ q₂) (δ : ℝ) (n : ℕ) : ℝ :=
  ∫ x : Fin n → ℝ, ((n : ℝ)⁻¹ * ∑ i, x i - M.θ) ^ 2 ∂Measure.pi (fun _ : Fin n => M.law δ)

/-- `MSE₀(θ̂(·), d)`: the mean squared error of the baseline `θ̄ₙ` with `δ = d (n + n₀)^(-α)`.
Lam, Zhang & Zhang, arXiv:1902.04673v1, §4.1, p.10; §4.2, p.11. -/
noncomputable def mseBaseline {q₁ q₂ : ℝ} (M : SimulationOutput q₁ q₂) (n₀ : ℕ) (d : ℝ) (n : ℕ) : ℝ :=
  mseAverage M (baselineDelta q₁ q₂ n₀ d n) n

end BiasVarianceMinimax


