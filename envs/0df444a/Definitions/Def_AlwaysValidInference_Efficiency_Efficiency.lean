-- Prove2me | Definitions.Def_AlwaysValidInference_Efficiency_Efficiency
-- name    : AlwaysValidInference_Efficiency_Efficiency
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-30T14:40:29.068859+00:00
-- url     : https://prove2.me/theorems/098b31da-5b29-4da4-a02c-9cc69d4a830e
-- title:
--   Power, run length, and double-infimum relative efficiency
-- statement:
--   A rule is admissible if it observes the natural filtration, has positive sample counts, and does not reject on infinite stopping, almost surely under every parameter law. Its power is $\nu_R(\theta)=P_\theta(\delta_R=1)$ and its relative run length is $\rho_R(\theta)=E_\theta[T_R]/M$. A sequential test is an alpha-indexed family of admissible rules with Type I error at most alpha, stopping times nonincreasing and decisions nondecreasing almost surely as alpha increases.
--
--   For each $0<\alpha<1$ and integer $M\ge1$, the competitor class contains every individual admissible rule $R$ with $T_R\le M$ almost surely at every parameter, Type I error at most alpha at the null, and power at least that of the truncated mSPRT at every non-null parameter. Its members need not be nested test families. The rule itself has no unknown-parameter argument. The relative efficiency is
--   $$\phi(M,\alpha)=\inf_{R\ \mathrm{feasible}}\inf_{\theta\in\Theta\setminus\{\theta_0\}}\frac{\rho_R(\theta)}{\rho_H(\theta;\alpha,M)}.$$
--   Infima and nonnegative expectations are extended-valued, preserving empty-set and infinite values. For valid parameters the test's derived error control makes the class nonempty; positive bounded sample counts make every denominator positive and finite. Those facts are not assumptions inserted into the competitor definition.
-- source:
--   Johari, Pekelis and Walsh, Always Valid Inference: Continuous Monitoring of A/B Tests, arXiv:1512.04922v3 (2019), https://arxiv.org/abs/1512.04922v3, §3, p. 11; §5.3, p. 19; Definition 3, p. 21 (PDF page = printed page).

import Definitions.Def_AlwaysValidInference_Efficiency_MSPRT

open MeasureTheory Set
open scoped ENNReal

namespace AlwaysValidInference.Efficiency

def Admissible {Ω : Type*} [MeasurableSpace Ω] (E : Model Ω)
    (R : DecisionRule Ω) : Prop :=
  R.Observed E.history ∧
    ∀ θ ∈ E.family.domain, ∀ᵐ ω ∂E.law θ, R.time ω = ⊤ → R.reject ω = false

noncomputable def power {Ω : Type*} [MeasurableSpace Ω] (E : Model Ω)
    (R : DecisionRule Ω) (θ : ℝ) : ℝ≥0∞ :=
  E.law θ {ω | R.reject ω = true}

noncomputable def runLength {Ω : Type*} [MeasurableSpace Ω] (E : Model Ω)
    (R : DecisionRule Ω) (θ : ℝ) (M : ℕ) : ℝ≥0∞ :=
  (∫⁻ ω, timeValue (R.time ω) ∂E.law θ) / (M : ℝ≥0∞)

/-- Section 3's nested family; competitors below are individual rules. -/
def SequentialTest {Ω : Type*} [MeasurableSpace Ω] (E : Model Ω)
    (R : ℝ → DecisionRule Ω) : Prop :=
  (∀ α ∈ Ioo (0 : ℝ) 1, Admissible E (R α) ∧
    power E (R α) E.null ≤ ENNReal.ofReal α) ∧
  (∀ α ∈ Ioo (0 : ℝ) 1, ∀ β ∈ Ioo (0 : ℝ) 1, α ≤ β →
    ∀ θ ∈ E.family.domain, ∀ᵐ ω ∂E.law θ,
      (R β).time ω ≤ (R α).time ω ∧
        ((R α).reject ω = true → (R β).reject ω = true))

/-- The complete competitor class of Definition 3, with no unknown parameter
argument to the decision rule and dominance at every alternative. -/
def Feasible {Ω : Type*} [MeasurableSpace Ω] (E : Model Ω)
    (H : MixingDistribution E.family.domain) (α : ℝ) (M : ℕ)
    (R : DecisionRule Ω) : Prop :=
  Admissible E R ∧
  (∀ θ ∈ E.family.domain, ∀ᵐ ω ∂E.law θ, R.time ω ≤ (M : ℕ∞)) ∧
  power E R E.null ≤ ENNReal.ofReal α ∧
  ∀ θ ∈ E.family.domain, θ ≠ E.null →
    power E (truncatedMSPRT E H α M) θ ≤ power E R θ

/-- Definition 3, preserving both infima and their order. Extended nonnegative
infima give infinity, never an arbitrary zero, if the competitor set is empty. -/
noncomputable def efficiency {Ω : Type*} [MeasurableSpace Ω] (E : Model Ω)
    (H : MixingDistribution E.family.domain) (α : ℝ) (M : ℕ) : ℝ≥0∞ :=
  ⨅ R : {R : DecisionRule Ω // Feasible E H α M R},
    ⨅ θ : {θ : ℝ // θ ∈ E.family.domain ∧ θ ≠ E.null},
      runLength E R.val θ.val M / runLength E (truncatedMSPRT E H α M) θ.val M

end AlwaysValidInference.Efficiency


