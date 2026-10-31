-- Prove2me | Definitions.Def_AlwaysValidInference_Efficiency_MSPRT
-- name    : AlwaysValidInference_Efficiency_MSPRT
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-30T14:39:31.629822+00:00
-- url     : https://prove2.me/theorems/c84f8bb9-ca18-4b34-b061-b48959ec3760
-- title:
--   Mixture likelihood test and its finite-horizon truncation
-- statement:
--   Let $S_n=n^{-1}\sum_{i=1}^nX_i$ for $n\ge1$. For a fixed mixing distribution $H$, define
--   $$\Lambda_n^H=\int_\Theta\exp\{n[(\theta-\theta_0)S_n-(\psi(\theta)-\psi(\theta_0))]\}\,dH(\theta).$$
--   The mSPRT stops at $T^H(\alpha)=\inf\{n\ge1:\Lambda_n^H\ge1/\alpha\}$, with the empty infimum equal to infinity, and rejects exactly when it stops. At a positive integer horizon $M$, it uses $\min(T^H(\alpha),M)$ observations and rejects exactly when $T^H(\alpha)\le M$. In particular, a first crossing at $M$ rejects.
--
--   Formalization Note: The exponential ratio is the intended likelihood-ratio reading of equation (7), cancelling the common carrier density wherever the printed quotient is defined. It avoids evaluating $0/0$ at sample means outside the carrier support; the concrete support issue is recorded as insight I3. Nonnegative extended integrals retain infinite likelihood values. Only positive sample counts are tested.
-- source:
--   Johari, Pekelis and Walsh, Always Valid Inference: Continuous Monitoring of A/B Tests, arXiv:1512.04922v3 (2019), https://arxiv.org/abs/1512.04922v3, §5.1 and §5.2, equations (7)–(9), pp. 17–18 (PDF page = printed page).

import Definitions.Def_AlwaysValidInference_Efficiency_Model
import Definitions.Def_AlwaysValidInference_Efficiency_DecisionRule
import Definitions.Def_AlwaysValidInference_Efficiency_MixingDistribution

open MeasureTheory Set
open scoped ENNReal BigOperators

namespace AlwaysValidInference.Efficiency

noncomputable def sampleMean {Ω : Type*} [MeasurableSpace Ω]
    (E : Model Ω) (n : ℕ) (ω : Ω) : ℝ :=
  (∑ i ∈ Finset.range n, E.X i ω) / n

/-- Equation (7), using the exponential likelihood ratio after cancellation of
the common carrier density. No division by a carrier density at the mean. -/
noncomputable def mixtureRatio {Ω : Type*} [MeasurableSpace Ω]
    (E : Model Ω) (H : MixingDistribution E.family.domain) (n : ℕ) (ω : Ω) : ℝ≥0∞ :=
  ∫⁻ θ, ENNReal.ofReal (Real.exp ((n : ℝ) *
    ((θ - E.null) * sampleMean E n ω -
      (E.family.cumulant θ - E.family.cumulant E.null)))) ∂H.law

/-- Equation (8): the infimum of positive crossing times; an empty set gives top. -/
noncomputable def crossingTime {Ω : Type*} [MeasurableSpace Ω]
    (E : Model Ω) (H : MixingDistribution E.family.domain) (α : ℝ) (ω : Ω) : ℕ∞ :=
  sInf {t | ∃ n : ℕ, 1 ≤ n ∧ t = (n : ℕ∞) ∧
    ENNReal.ofReal (1 / α) ≤ mixtureRatio E H n ω}

noncomputable def msprt {Ω : Type*} [MeasurableSpace Ω]
    (E : Model Ω) (H : MixingDistribution E.family.domain) (α : ℝ) : DecisionRule Ω :=
  { time := crossingTime E H α
    reject := fun ω => if crossingTime E H α ω < ⊤ then true else false }

/-- Section 5.1: a crossing at the horizon still rejects. -/
noncomputable def truncatedMSPRT {Ω : Type*} [MeasurableSpace Ω]
    (E : Model Ω) (H : MixingDistribution E.family.domain) (α : ℝ) (M : ℕ) :
    DecisionRule Ω :=
  { time := fun ω => min (crossingTime E H α ω) (M : ℕ∞)
    reject := fun ω => if crossingTime E H α ω ≤ (M : ℕ∞) then true else false }

end AlwaysValidInference.Efficiency


