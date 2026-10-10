-- Prove2me | Definitions.Def_RiskSensMFG_Nash_Equilibrium
-- name    : RiskSensMFG_Nash_Equilibrium
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-09T14:45:59.146008+00:00
-- url     : https://prove2.me/theorems/83c310b1-9ea8-4705-9ed0-7553c3d7e381
-- title:
--   Definition 3 and Assumption 2-(a), pp. 9, 22–23 — mean-field equilibrium, the bounded-Lipschitz metric, total variation and the moduli ω_p, ω_c
-- statement:
--   1. **Mean-field equilibrium.** A Markov policy $\pi$ and a state-measure flow $\boldsymbol\mu$ form a mean-field equilibrium if $\boldsymbol\mu=\Lambda(\pi)$ and $\pi$ is optimal for $\boldsymbol\mu$ among Markov policies:
--   $$J_{\boldsymbol\mu}(\pi)\le J_{\boldsymbol\mu}(\sigma)\quad\text{for every Markov policy }\sigma .$$
--   2. **Bounded-Lipschitz metric.** For a metric space $\mathsf X$ and $\mu,\nu\in\mathcal P(\mathsf X)$,
--   $$d_{BL}(\mu,\nu)=\sup\Big\{\Big|\int f\,d\mu-\int f\,d\nu\Big| : \|f\|_\infty+\mathrm{Lip}(f)\le1\Big\}.$$
--   3. **Total variation.** $\|\mu-\nu\|_{TV}=\sup\{|\int g\,d\mu-\int g\,d\nu| : g \text{ measurable},\ |g|\le1\}$.
--   4. **Assumption 2-(a).** The moduli of continuity
--   $$\omega_p(r)=\sup_{(x,a)}\sup_{d_{BL}(\mu,\nu)\le r}\|p(\cdot\mid x,a,\mu)-p(\cdot\mid x,a,\nu)\|_{TV},\qquad \omega_c(r)=\sup_{(x,a)}\sup_{d_{BL}(\mu,\nu)\le r}|c(x,a,\mu)-c(x,a,\nu)|$$
--   tend to $0$ as $r\to0$.
--
--   These are the hypotheses of the approximation theorem: the pair $(\pi,\boldsymbol\mu)$ is a mean-field equilibrium, and Assumption 2 makes $p$ and $c$ uniformly continuous in the measure argument.
--
--   **Formalization Note** Optimality in the equilibrium is required only against Markov policies, a weaker requirement than the paper's Definition 3 (optimality against all policies); the paper's proof uses only Markov deviations (Corollary 1). Assumption 2-(a) is written as "for every $\varepsilon>0$ there is $\delta>0$ such that $d_{BL}(\mu,\nu)\le\delta$ implies the difference is at most $\varepsilon$, for all $x,a$", which is equivalent to $\omega(r)\to0$ because the moduli are nondecreasing in $r$. $d_{BL}$ is taken for the metric of the `MetricSpace` instance of $\mathsf X$; the supremum is over a nonempty set bounded by $2$. The total-variation convention is the one used in Appendix C (supremum over $|g|\le1$), which is twice $\sup_B|\mu(B)-\nu(B)|$; the condition "$\to0$" does not depend on the factor.
-- source:
--   Saldi, Başar & Raginsky, Discrete-time Risk-sensitive Mean-field Games, arXiv:1808.03929v2, p. 9, Definition 3; p. 22, ω_p and ω_c; p. 23, Assumption 2-(a); p. 36 (TV convention)

import Mathlib
import Definitions.Def_RiskSensMFG_Nash_Model

open MeasureTheory ProbabilityTheory
open scoped NNReal

namespace RiskSensMFG.Nash

section MFE

variable {X A : Type*} [MeasurableSpace X] [TopologicalSpace X] [OpensMeasurableSpace X]
  [MeasurableSpace A]

/-- A mean-field equilibrium `(π, μ)` with a Markov policy `π` (Definition 3, with optimality
required against Markov policies): `μ = Λ(π)` and `J_μ(π) ≤ J_μ(σ)` for every Markov policy `σ`. -/
def IsMFE (M : Model X A) (π : MarkovPolicy X A) (μ : ℕ → RiskSensMFG.Existence.PM X) : Prop :=
  μ = flow M π ∧ ∀ σ : MarkovPolicy X A, J M μ π.toPolicy ≤ J M μ σ.toPolicy

end MFE

section Metrics

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]

/-- The bounded-Lipschitz distance `d_BL(μ, ν) = sup { |∫ f dμ - ∫ f dν| : ‖f‖_∞ + Lip(f) ≤ 1 }`
on `P(X)`, for the metric of `X`. -/
noncomputable def dBL (μ ν : RiskSensMFG.Existence.PM X) : ℝ :=
  ⨆ f : {f : X → ℝ // ∃ a b : ℝ≥0, (∀ x, |f x| ≤ a) ∧ LipschitzWith b f ∧ (a : ℝ) + b ≤ 1},
    |∫ x, f.1 x ∂(ProbabilityMeasure.toMeasure μ) - ∫ x, f.1 x ∂(ProbabilityMeasure.toMeasure ν)|

end Metrics

section TV

variable {X : Type*} [MeasurableSpace X]

/-- The total-variation norm `‖μ - ν‖_TV = sup { |∫ g dμ - ∫ g dν| : g measurable, |g| ≤ 1 }`
(used for probability measures). -/
noncomputable def tv (μ ν : Measure X) : ℝ :=
  ⨆ g : {g : X → ℝ // Measurable g ∧ ∀ x, |g x| ≤ 1}, |∫ x, g.1 x ∂μ - ∫ x, g.1 x ∂ν|

end TV

section Assumption2

variable {X A : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X] [MeasurableSpace A]

/-- Assumption 2-(a): the moduli `ω_p(r)` and `ω_c(r)` of `p` (in total variation) and `c` in the
measure argument (in `d_BL`), uniform in `(x, a)`, tend to `0` as `r → 0`. -/
def Assumption2a (M : Model X A) : Prop :=
  (∀ ε > 0, ∃ δ > 0, ∀ (x : X) (a : A) (μ ν : RiskSensMFG.Existence.PM X), dBL μ ν ≤ δ →
      tv (M.p (x, a, μ)) (M.p (x, a, ν)) ≤ ε) ∧
  (∀ ε > 0, ∃ δ > 0, ∀ (x : X) (a : A) (μ ν : RiskSensMFG.Existence.PM X), dBL μ ν ≤ δ →
      |M.c (x, a, μ) - M.c (x, a, ν)| ≤ ε)

end Assumption2

end RiskSensMFG.Nash


