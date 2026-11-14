-- Prove2me | Definitions.Def_AppliedSDE_SarkkaSolin_StateSpaceModels
-- name    : AppliedSDE_SarkkaSolin_StateSpaceModels
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-13T17:52:50.025691+00:00
-- url     : https://prove2.me/theorems/6be2b20a-89ed-40ab-a2f9-eda864279b70
-- title:
--   Continuous-time and continuous-discrete stochastic state-space models
-- statement:
--   Definitions 10.1 and 10.2, printed pp. 199–200. The continuous-time model is expressed in a scalar specialisation using a genuinely Brownian filtered probability space, independent state and measurement driving noises, a scalar stochastic-integral state equation, and an integrated observation-noise equation. The continuous-discrete model is an interface for discrete observation times and measurable conditional probability distributions indexed by the continuous state. Model-specific assertions that the observed random variables possess these conditional laws remain separate.
--
--   Representative mathematical statement, subject to the precise formal hypotheses:
--
--   $$
--   \mathrm dX_t=AX_t\,\mathrm dt+L\,\mathrm dW_t,\qquad\mathrm dY_t=HX_t\,\mathrm dt+\mathrm dV_t
--   $$
-- source:
--   Original derived from Simo Särkkä and Arno Solin, Applied Stochastic Differential Equations (Cambridge University Press, 2019), Definitions 10.1, 10.2, equations (10.7), (10.12), printed pp. 199–200. https://doi.org/10.1017/9781108186735

import Mathlib
import Definitions.Def_KLSModular_LevyStochCalc_Brownian_Filtered
import Definitions.Def_KLSModular_LevyStochCalc_Brownian_ItoL2CompletionMaster
set_option autoImplicit false
open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

namespace AppliedSDE.SarkkaSolin

/-- Source Definition 10.1, scalar continuous-time state-space model.
The process equations are genuine integral SDE identities relative to a
Brownian filtered probability space. Independence of the two Brownian
driving processes is an additional hypothesis, as in the book. -/
def IsContinuousTimeStateSpaceModelScalar
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (W B : LevyStochCalc.Brownian.BrownianMotion P)
    (ℱ : Filtration ℝ ‹MeasurableSpace Ω›)
    (hW : LevyStochCalc.Brownian.IsBrownianFiltration W ℱ)
    (x₀ z₀ : ℝ) (X Z : ℝ → Ω → ℝ)
    (f h : ℝ → ℝ → ℝ) (L : Ω → ℝ → ℝ)
    (hLm : Measurable (Function.uncurry L))
    (hLp : LevyStochCalc.Probability.ProgressivelyMeasurable ℱ L)
    (hLs : ∀ t : ℝ, 0 < t →
      ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) t,
        (‖L ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤) : Prop :=
  IndepFun (fun ω : Ω => fun t : ℝ => W.W t ω)
    (fun ω : Ω => fun t : ℝ => B.W t ω) P ∧
  (∀ t : ℝ, 0 ≤ t →
    (fun ω : Ω => X t ω) =ᵐ[P] fun ω : Ω =>
      x₀ + (∫ s in (0 : ℝ)..t, f (X s ω) s) +
        LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian
          W ℱ hW L hLm hLp hLs t ω) ∧
  (∀ t : ℝ, 0 ≤ t →
    (fun ω : Ω => Z t ω) =ᵐ[P] fun ω : Ω =>
      z₀ + (∫ s in (0 : ℝ)..t, h (X s ω) s) +
        B.W t ω - B.W 0 ω)

/-- Source Definition 10.2, scalar continuous-discrete observation interface.
The measurement model is a measurable family of conditional probability laws.
Its conditional-law correctness for an actual observed process is a separate
property and must be proved or assumed in each model instance. -/
structure ContinuousDiscreteObservationModel
    (State : Type*) [MeasurableSpace State]
    (Observation : Type*) [MeasurableSpace Observation] where
  observationTimes : ℕ → ℝ≥0
  conditionalLaw : State → Measure Observation
  lawIsProbability : ∀ x, IsProbabilityMeasure (conditionalLaw x)
  lawMeasurable : ∀ A : Set Observation,
    MeasurableSet A → Measurable (fun x => conditionalLaw x A)

end AppliedSDE.SarkkaSolin


