-- Prove2me | Definitions.Def_WassersteinLinOpt_Ball_wassersteinDist
-- name    : WassersteinLinOpt_Ball_wassersteinDist
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-02T14:46:46.507954+00:00
-- url     : https://prove2.me/theorems/41cee01b-e33b-4342-8332-7489e08cfe25
-- title:
--   Wasserstein distance $W_p$ (Eq. (1))
-- statement:
--   Let $(X,d)$ be a metric space with its Borel $\sigma$-algebra and let $\mu_1,\mu_2$ be Borel probability measures on $X$. A **coupling** of $\mu_1$ and $\mu_2$ is a measure $\gamma$ on $X\times X$ whose first marginal is $\mu_1$ and whose second marginal is $\mu_2$; the set of couplings is $\Pi(\mu_1,\mu_2)$. For $p \ge 1$ the **$p$-th Wasserstein distance** is
--
--   $$W_p(\mu_1,\mu_2)=\Big(\inf_{\gamma\in\Pi(\mu_1,\mu_2)}\int_{X\times X} d^p(x_1,x_2)\,d\gamma(x_1,x_2)\Big)^{1/p}\in[0,+\infty].$$
--
--   It is defined for all probability measures, including those without a finite $p$-th moment, for which it may be $+\infty$ (p. 1109).
--
--   **Formalization Note.** `couplings μ₁ μ₂` is the set of `γ : Measure (X × X)` with `γ.map Prod.fst = μ₁` and `γ.map Prod.snd = μ₂` (the projections are measurable, so `map` is the true marginal; a measure with probability marginals is itself a probability measure). The value lives in `ℝ≥0∞`, the integral is the lower Lebesgue integral of $d^p$, and the infimum and the power $1/p$ are taken in `ℝ≥0∞`, so an infinite transport cost is `⊤`, never a junk real.
-- source:
--   Yue, Kuhn & Wiesemann, On linear optimization over Wasserstein balls, Math. Program. 195 (2022) 1107–1122, https://doi.org/10.1007/s10107-021-01673-8, p. 1108, Eq. (1)

import Mathlib

open MeasureTheory
open scoped ENNReal NNReal

namespace WassersteinLinOpt.Ball

/-- Couplings `Π(μ₁, μ₂)` (Yue–Kuhn–Wiesemann, p. 1108, below Eq. (1)): the measures `γ` on
`X × X` whose first marginal is `μ₁` and whose second marginal is `μ₂`. Both projections are
measurable, so `Measure.map` is never the junk zero measure here; a measure with probability
marginals is automatically a probability measure. -/
def couplings {X : Type*} [MeasurableSpace X] (μ₁ μ₂ : Measure X) : Set (Measure (X × X)) :=
  {γ | γ.map Prod.fst = μ₁ ∧ γ.map Prod.snd = μ₂}

/-- The `p`-th Wasserstein distance, Eq. (1), p. 1108:
`W_p(μ₁, μ₂) = (inf_{γ ∈ Π(μ₁, μ₂)} ∫_{X×X} d^p(x₁, x₂) dγ(x₁, x₂))^{1/p}`.
It is valued in `ℝ≥0∞`, so it is `⊤` (not a junk real) for measures without a finite `p`-th
moment, which the paper explicitly allows (p. 1109). -/
noncomputable def wassersteinDist {X : Type*} [MetricSpace X] [MeasurableSpace X] (p : ℝ)
    (μ₁ μ₂ : ProbabilityMeasure X) : ℝ≥0∞ :=
  (⨅ γ ∈ couplings (μ₁ : Measure X) (μ₂ : Measure X),
      ∫⁻ z, ENNReal.ofReal (dist z.1 z.2 ^ p) ∂γ) ^ (1 / p)

end WassersteinLinOpt.Ball


