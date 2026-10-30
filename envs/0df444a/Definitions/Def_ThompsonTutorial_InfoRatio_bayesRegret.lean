-- Prove2me | Definitions.Def_ThompsonTutorial_InfoRatio_bayesRegret
-- name    : ThompsonTutorial_InfoRatio_bayesRegret
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-29T18:10:21.831639+00:00
-- url     : https://prove2.me/theorems/5d8c98c5-522d-4474-a49f-0f7fe72affd2
-- title:
--   Expected cumulative (Bayesian) regret $\mathbb E[\mathrm{Regret}(T)]$
-- statement:
--   Let $\mu:X\times\Theta\to\mathbb R$ be the mean reward, $\theta$ the random parameter, $x^*$ the optimal action and $(x_t)_{t\ge1}$ the actions of an algorithm. The **expected cumulative regret** over $T$ periods is
--   $$
--   \mathbb E[\mathrm{Regret}(T)]\;=\;\mathbb E\Big[\sum_{t=1}^T\big(\mu(x^*,\theta)-\mu(x_t,\theta)\big)\Big],
--   $$
--   the expectation being over the prior on $\theta$, the noise, and the algorithm's internal randomization. It is the quantity bounded by (8.8).
--
--   **Formalization Note** The sum ranges over `Finset.Icc 1 T`; at $T=0$ the regret is $0$. The theorems assume the integrand integrable, since a non-integrable integrand has Bochner integral $0$.
-- source:
--   Russo, Van Roy, Kazerouni, Osband, Wen, A Tutorial on Thompson Sampling, Found. Trends Mach. Learn. 11(1) (2018), §8.1.2, p. 71 (PDF p. 74), unnumbered display defining E[Regret(T)]

import Mathlib
open MeasureTheory

namespace ThompsonTutorial.InfoRatio

/-- **Expected cumulative (Bayesian) regret `E[Regret(T)]`.**
Russo, Van Roy, Kazerouni, Osband, Wen, *A Tutorial on Thompson Sampling*, Found. Trends Mach.
Learn. 11(1) (2018), §8.1.2, p. 71 (PDF p. 74): "The expected cumulative regret of an algorithm
over T periods is E[Regret(T)] = E[∑_{t=1}^T (μ(x∗, θ) − μ(xt, θ))]. This expectation is taken
over draws of θ, the idiosyncratic noise terms (wt, . . . , wT), and the algorithm's internal
randomization over actions."

`bayesRegret P μ θ xstar x T = ∫ ∑_{t=1}^T (μ(x*(ω), θ(ω)) − μ(x_t(ω), θ(ω))) dP(ω)`.

**Formalization Note.** Periods `t ∈ {1, …, T}` (`Finset.Icc 1 T`); at `T = 0` the regret is `0`.
`μ`, `θ`, `x*` and the actions are parameters; the theorems instantiate `μ` with `meanReward` and
assume the integrand integrable (otherwise the Bochner integral is `0`). -/
noncomputable def bayesRegret {Ω X Θ : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (μ : X → Θ → ℝ) (θ : Ω → Θ) (xstar : Ω → X) (x : ℕ → Ω → X) (T : ℕ) : ℝ :=
  ∫ ω, ∑ t ∈ Finset.Icc 1 T, (μ (xstar ω) (θ ω) - μ (x t ω) (θ ω)) ∂P

end ThompsonTutorial.InfoRatio


