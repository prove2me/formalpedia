-- Prove2me | Definitions.Def_FragileBandit_CauchyTail_Supplement_ProcessAsymptotics
-- name    : FragileBandit_CauchyTail_Supplement_ProcessAsymptotics
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-24T00:03:29.889646+00:00
-- url     : https://prove2.me/theorems/eb532785-b287-4765-b1b5-02848d348560
-- title:
--   Scaled and limiting CGFs, Assumptions 1–2, rate functions and the exponent of (23)
-- statement:
--   For an arm reward table with law $\nu$, let $S_{i,n}=\sum_{s=1}^n X_i(s)$. Its scaled cumulant generating function and limiting function are
--   $$\overline\Lambda_i^n(\theta)=n^{-1}\log\mathbb E_\nu e^{\theta S_{i,n}},\qquad \overline\Lambda_i(\theta)=\lim_{n\to\infty}\overline\Lambda_i^n(\theta).$$
--   Assumption 1 requires every extended-real limit to exist and zero to lie in the interior $\overline\Theta_i$ of its finite domain. Assumption 2 requires differentiability on that interior and either a full real domain or divergence of the absolute derivative along every sequence approaching a finite boundary point from within the domain. The long-run mean is $m_i=\overline\Lambda_i'(0)$.
--
--   The rate function and its interior domain are
--   $$\overline\Lambda_i^*(z)=\sup_{\theta\in\mathbb R}(\theta z-\overline\Lambda_i(\theta)),\qquad \overline I_i=\operatorname{int}\{z:\overline\Lambda_i^*(z)<\infty\}.$$
--   The process tail exponent for arm $k$ is $\sum_{j:m_j>m_k}\inf_{z\in\overline I_j,\ z<m_k}\overline\Lambda_j^*(z)/d_P(z,m_k)$. The standing compatibility conditions are that $I_P$ is an interval containing all rewards almost surely and $\overline I_i\subseteq I_P$ for every arm.
--
--   These definitions preserve the distinction between the process CGF and the base family's CGF. **Formalization Note** Nonnegative integrals and the extended logarithm retain infinite moments. The limiting CGF is chosen from limits of these computed scaled CGFs, not freely supplied. Rate functions and exponents lie in $[0,\infty]$; empty infima equal $+\infty$. Their supremum is taken in the extended reals before conversion to a nonnegative value; Assumption 1 supplies the zero term, so the rate is nonnegative.
-- source:
--   Fan and Glynn, The Fragility of Optimized Bandit Algorithms, arXiv:2109.13595v8, pp.18, 20–21, Assumptions 1–2 and the definitions before Theorem 3

import Mathlib
import Definitions.Def_FragileBandit_CauchyTail_Supplement_TailEncoding
import Definitions.Def_FragileBandit_CauchyTail_Supplement_RestedProcess

set_option autoImplicit false

namespace FragileBandit.CauchyTail.Supplement

open MeasureTheory ProbabilityTheory Filter BanditAlgorithm
open scoped ENNReal Topology

/-- The scaled CGF uses the nonnegative integral and extended logarithm: divergent exponential
moments are +∞, never the Bochner integral's default zero. Only n ≥ 1 matters in limits. -/
noncomputable def scaledCGF {K : ℕ} (ν : RestedEnvironment K)
    (i : Fin K) (n : ℕ) (θ : ℝ) : EReal :=
  ((1 / (n : ℝ) : ℝ) : EReal) *
    ENNReal.log (∫⁻ x, ENNReal.ofReal (Real.exp (θ * rewardSum x i n)) ∂ν.law)

open Classical in
/-- The limit is computed from the law. It is not an unconstrained CGF parameter. -/
noncomputable def limitingCGF {K : ℕ} (ν : RestedEnvironment K) (i : Fin K) (θ : ℝ) : EReal :=
  if h : ∃ L : EReal, Tendsto (fun n => scaledCGF ν i n θ) atTop (𝓝 L) then h.choose else 0

/-- The barred natural-parameter domain, distinct from the base family's Θ_P. -/
noncomputable def processTheta {K : ℕ} (ν : RestedEnvironment K) (i : Fin K) : Set ℝ :=
  interior {θ | limitingCGF ν i θ < ⊤}

/-- The real CGF on the interior of its finite domain. -/
noncomputable def realCGF {K : ℕ} (ν : RestedEnvironment K) (i : Fin K) (θ : ℝ) : ℝ :=
  (limitingCGF ν i θ).toReal

/-- Assumption 1, p.20. -/
def AssumptionOne {K : ℕ} (ν : RestedEnvironment K) : Prop :=
  (∀ i θ, Tendsto (fun n => scaledCGF ν i n θ) atTop (𝓝 (limitingCGF ν i θ))) ∧
    ∀ i, 0 ∈ processTheta ν i

/-- Assumption 2, p.20: differentiability and steepness at every finite boundary point.
It adds no strict convexity, stationarity, mixing, or finite-n concentration assumption. -/
def AssumptionTwo {K : ℕ} (ν : RestedEnvironment K) : Prop :=
  ∀ i, DifferentiableOn ℝ (realCGF ν i) (processTheta ν i) ∧
    (processTheta ν i = Set.univ ∨
      ∀ (θ : ℕ → ℝ) (b : ℝ), (∀ m, θ m ∈ processTheta ν i) →
        b ∈ frontier (processTheta ν i) → Tendsto θ atTop (𝓝 b) →
        Tendsto (fun m => |deriv (realCGF ν i) (θ m)|) atTop atTop)

/-- The long-run mean is the derivative of the limiting CGF at zero. -/
noncomputable def processMean {K : ℕ} (ν : RestedEnvironment K) (i : Fin K) : ℝ :=
  deriv (realCGF ν i) 0

/-- The convex conjugate in [0,+∞]. Under Assumption 1 the θ=0 term is zero,
so taking the nonnegative part loses no value. -/
noncomputable def processRate {K : ℕ} (ν : RestedEnvironment K) (i : Fin K) (z : ℝ) : ℝ≥0∞ :=
  (⨆ θ : ℝ, ((θ * z : ℝ) : EReal) - limitingCGF ν i θ).toENNReal

/-- The barred interior effective domain of the rate function. -/
noncomputable def processMeanSet {K : ℕ} (ν : RestedEnvironment K) (i : Fin K) : Set ℝ :=
  interior {z | processRate ν i z < ⊤}

/-- The standing reward-range and rate-domain conditions of pp.18 and 21. -/
def FitsFamily {K : ℕ} (P : Measure ℝ) (ν : RestedEnvironment K) : Prop :=
  Set.OrdConnected (meanSet P) ∧
    (∀ᵐ x ∂ν.law, ∀ i s, x i s ∈ meanSet P) ∧
    ∀ i, processMeanSet ν i ⊆ meanSet P

/-- The exact sum of infima in (23), with the infimum of an empty set equal to +∞. -/
noncomputable def processTailExponent {K : ℕ} (P : Measure ℝ) (ν : RestedEnvironment K)
    (k : Fin K) : ℝ≥0∞ :=
  ∑ j ∈ Finset.univ.filter (fun j => processMean ν k < processMean ν j),
    ⨅ z ∈ processMeanSet ν j ∩ Set.Iio (processMean ν k),
      processRate ν j z / dP P z (processMean ν k)

/-- The tail probability under the process-induced history law. -/
noncomputable def processTail {K : ℕ} (ν : RestedEnvironment K) (π : BanditPolicy K)
    (i : Fin K) (T : ℕ) (x : ℝ) : ℝ≥0∞ :=
  processMeasure ν π T {h | x < (armPullCount i h : ℝ)}

end FragileBandit.CauchyTail.Supplement


