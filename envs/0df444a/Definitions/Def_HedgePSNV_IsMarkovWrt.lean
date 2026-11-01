-- Prove2me | Definitions.Def_HedgePSNV_IsMarkovWrt
-- name    : HedgePSNV_IsMarkovWrt
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T12:00:26.246251+00:00
-- url     : https://prove2.me/theorems/73afb2aa-5600-4e1a-b5a3-1c8556d3bcfd
-- title:
--   Markov property on $[0,T]$ with respect to a filtration
-- statement:
--   Let $Y$ be a process with values in a measurable space $E$, $Q$ a measure and $(\mathcal F_t)$ a filtration. $Y$ is **Markov on $[0,T]$ under $Q$ with respect to $(\mathcal F_t)$** when, for all $0\le s\le t\le T$ and every bounded measurable $g:E\to\mathbb R$,
--   $$
--   \mathbb E_Q\big[g(Y_t)\mid\mathcal F_s\big]=\mathbb E_Q\big[g(Y_t)\mid\sigma(Y_s)\big]\qquad Q\text{-a.s.}
--   $$
--   The paper assumes that $(X_t,\mu_t,\sigma_t)$ is Markovian under $\mathbb P$ (p.11) and that $(X_t,\sigma_t)$ is Markovian under $\mathbb P^M$ (p.12); both hypotheses are this predicate.
--
--   **Formalization Note** The paper does not define the term; this is the simple Markov property relative to the filtration $\mathcal F_t$ of footnote 4, p.11.
-- source:
--   Wang–Yao–Zhang, How Does Risk Hedging Impact Operations? Insights from a Price-Setting Newsvendor Model, arXiv:2201.01026v4, §3.1, pp.11–12

import Mathlib

open MeasureTheory
open scoped NNReal

namespace HedgePSNV

/-- The (simple) Markov property on `[0, T]` of a process `Y` with values in a measurable
space `E`, under the measure `Q` and with respect to the filtration `F`: for `s ≤ t ≤ T` and
every bounded measurable `g : E → ℝ`,
`E_Q[g(Y_t) | F_s] = E_Q[g(Y_t) | σ(Y_s)]` `Q`-a.s. This is the reading of "(X_t, µ_t, σ_t)
is Markovian under P" (arXiv:2201.01026v4, p.11) and "(X_t, σ_t) is Markovian under P^M"
(p.12), with respect to the filtration `F_t` of footnote 4, p.11. -/
def IsMarkovWrt {Ω E : Type*} [m : MeasurableSpace Ω] [mE : MeasurableSpace E]
    (Q : Measure Ω) (F : Filtration ℝ≥0 m) (T : ℝ≥0) (Y : ℝ≥0 → Ω → E) : Prop :=
  ∀ s t : ℝ≥0, s ≤ t → t ≤ T → ∀ g : E → ℝ, Measurable g → (∃ K : ℝ, ∀ y, |g y| ≤ K) →
    condExp (F s) Q (fun ω => g (Y t ω)) =ᵐ[Q]
      condExp (MeasurableSpace.comap (Y s) mE) Q (fun ω => g (Y t ω))

end HedgePSNV


