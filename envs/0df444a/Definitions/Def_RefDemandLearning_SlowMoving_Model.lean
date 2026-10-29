-- Prove2me | Definitions.Def_RefDemandLearning_SlowMoving_Model
-- name    : RefDemandLearning_SlowMoving_Model
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-29T05:22:55.189883+00:00
-- url     : https://prove2.me/theorems/ce0b53c8-66d7-42cc-91b8-d9ce76c9b210
-- title:
--   Loss-averse additive demand and the parameter rectangle
-- statement:
--   Let $I=[\ell,u]$, $0\le\ell<u$, and let known finite lower and upper bounds specify a nonempty rectangle for $\theta=(\alpha,\beta,\eta^+,\eta^-)$. The lower bounds ensure $\alpha\ge0$, $\beta>0$ and $\eta^+,\eta^-\ge0$. The parameter set $\Theta$ is the rectangle intersected with $\eta^+\le\eta^-$. It is nonempty, but may be a singleton. For every $\theta\in\Theta$, require
--   $$\alpha-\beta u-\eta^-(u-\ell)\ge0,\qquad \ell<\frac{\alpha}{2\beta}<u.$$
--   The expected demand, revenue and reference-free optimum are
--   $$d(p,r,\theta)=\alpha-\beta p+\eta^+\max(r-p,0)-\eta^-\max(p-r,0),\quad R(p,r,\theta)=p\,d(p,r,\theta),\quad p^*=\frac{\alpha}{2\beta}.$$
--   The boundary demand inequality ensures nonnegative expected demand throughout the price box. It imposes no sign restriction on realized observations. Zero sensitivities and equality of the two sensitivities are allowed.
--
--   **Formalization Note.** `Bounds` contains only known bounds and the price interval; `Standing` and `InTheta` state the standing assumptions explicitly. All quantities are real, and this module contains no noise, optimality or consistency assumption.
-- source:
--   den Boer and Keskin, Dynamic Pricing with Demand Learning and Reference Effects, DOI https://doi.org/10.1287/mnsc.2021.4234, supplied April 19, 2021 artifact, Section 2, printed/PDF pp. 7–8, (2.2)–(2.3)

import Definitions.Def_RefDemandLearning_SlowMoving_Mechanism

set_option autoImplicit false

noncomputable section

namespace RefDemandLearning.SlowMoving

structure Parameters where
  alpha : ℝ
  beta : ℝ
  etaPlus : ℝ
  etaMinus : ℝ

structure Bounds where
  prices : PriceInterval
  alphaMin : ℝ
  alphaMax : ℝ
  betaMin : ℝ
  betaMax : ℝ
  plusMin : ℝ
  plusMax : ℝ
  minusMin : ℝ
  minusMax : ℝ

def InTheta (B : Bounds) (θ : Parameters) : Prop :=
  θ.alpha ∈ Set.Icc B.alphaMin B.alphaMax ∧
  θ.beta ∈ Set.Icc B.betaMin B.betaMax ∧
  θ.etaPlus ∈ Set.Icc B.plusMin B.plusMax ∧
  θ.etaMinus ∈ Set.Icc B.minusMin B.minusMax ∧ θ.etaPlus ≤ θ.etaMinus

/-- Exactly the standing parameter assumptions of Section 2. -/
def Standing (B : Bounds) : Prop :=
  0 ≤ B.alphaMin ∧ B.alphaMin ≤ B.alphaMax ∧
  0 < B.betaMin ∧ B.betaMin ≤ B.betaMax ∧
  0 ≤ B.plusMin ∧ B.plusMin ≤ B.plusMax ∧
  0 ≤ B.minusMin ∧ B.minusMin ≤ B.minusMax ∧
  (∃ θ, InTheta B θ) ∧
  ∀ θ, InTheta B θ →
    0 ≤ θ.alpha - θ.beta * B.prices.hi - θ.etaMinus * (B.prices.hi - B.prices.lo) ∧
    B.prices.lo < θ.alpha / (2 * θ.beta) ∧ θ.alpha / (2 * θ.beta) < B.prices.hi

def demand (θ : Parameters) (p r : ℝ) : ℝ :=
  θ.alpha - θ.beta * p + θ.etaPlus * max (r - p) 0 - θ.etaMinus * max (p - r) 0

def revenue (θ : Parameters) (p r : ℝ) : ℝ := p * demand θ p r

def optimalBasePrice (θ : Parameters) : ℝ := θ.alpha / (2 * θ.beta)

end RefDemandLearning.SlowMoving


