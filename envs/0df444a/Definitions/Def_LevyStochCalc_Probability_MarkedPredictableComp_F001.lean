-- Prove2me | Definitions.Def_LevyStochCalc_Probability_MarkedPredictableComp_F001
-- name    : LevyStochCalc_Probability_MarkedPredictableComp_F001
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-20T20:20:28.856694+00:00
-- url     : https://prove2.me/theorems/d48f6c61-e104-4070-acba-85d34c926029
-- title:
--   Source declarations: LevyStochCalc.Probability.MarkedPredictableComp
-- statement:
--   Source-preserving extracted declarations from LevyStochCalc.Probability.MarkedPredictableComp. Existing definitions, lemmas, instances, proofs and elaboration context are retained; generated import closure remains under review.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Ito_JumpCoefficientPredictableCriteria_F001
import Definitions.Def_LevyStochCalc_Ito_JumpCoefficientPredictableCriteria_F002
import Definitions.Def_LevyStochCalc_Ito_JumpCoefficientPredictableCriteria_F003
import Definitions.Def_LevyStochCalc_Ito_JumpCoefficientPredictableLeftLim_F000
import Definitions.Def_LevyStochCalc_Ito_JumpCoefficientPredictableLeftLim_F001
import Definitions.Def_SourceProof_d6ed8f97bdea5b0368dd302f
import Mathlib.Algebra.Order.Chebyshev
import Mathlib.Analysis.Normed.Group.Continuity
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.MeasureTheory.Constructions.BorelSpace.ContinuousLinearMap
import Mathlib.MeasureTheory.Constructions.BorelSpace.Order
import Mathlib.MeasureTheory.Covering.DensityTheorem
import Mathlib.MeasureTheory.Function.ConditionalExpectation.CondJensen
import Mathlib.MeasureTheory.Function.ConditionalExpectation.PullOut
import Mathlib.MeasureTheory.Function.ConvergenceInMeasure
import Mathlib.MeasureTheory.Integral.Average
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.Layercake
import Mathlib.MeasureTheory.Measure.CharacteristicFunction.Basic
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
import Mathlib.MeasureTheory.Measure.MeasureSpace
import Mathlib.MeasureTheory.Measure.Typeclasses.Probability
import Mathlib.Probability.Distributions.Poisson.Basic
import Mathlib.Probability.Independence.CharacteristicFunction
import Mathlib.Probability.Independence.InfinitePi
import Mathlib.Probability.Martingale.OptionalStopping
import Mathlib.Probability.Martingale.Upcrossing
import Mathlib.Probability.Notation
import Mathlib.Probability.Process.Filtration
import Mathlib.Probability.Process.Stopping
import Mathlib.Topology.Algebra.MulAction
import Mathlib.Topology.Instances.ENNReal.Lemmas
import Mathlib.Topology.MetricSpace.Bounded
import Mathlib.Topology.Order.Compact
import Mathlib.Topology.Order.DenselyOrdered
import Mathlib.Topology.Order.LeftRight
import Mathlib.Topology.Order.LeftRightLim
import Mathlib.Topology.Order.Monotone
import Mathlib.Topology.Separation.Regular

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# Marked predictability under measurable post-composition

On the positive times the time coordinate of the time–mark space is measurable for the marked
predictable σ-algebra, a predictable process of the time and the sample point lifts to a marked
predictable one, and a marked predictable process keeps its measurability. A measurable function
of the time, a predictable process and a marked predictable process is therefore marked
predictable once it is cut to the positive times.

## Main statements

* `LevyStochCalc.Probability.measurableSet_markedPredictableSigma_time_pos` — a measurable set
  of positive times, carrying all sample points and marks, is marked predictable.
* `LevyStochCalc.Probability.measurable_markedPredictableSigma_time_pos` — the time coordinate,
  cut to the positive times, is marked predictable.
* `LevyStochCalc.Probability.MarkedPredictable.comp_measurable` — a measurable function of the
  time, a predictable process and a marked predictable process, cut to the positive times, is
  marked predictable.
* `LevyStochCalc.Probability.MarkedPredictable.comp_continuous` — the same for a continuous
  function.

## References

* Ikeda–Watanabe, *SDEs and Diffusion Processes*, 1989, §II.3.
-/

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace LevyStochCalc.Probability

universe u v

variable {Ω : Type u} {mΩ : MeasurableSpace Ω} {ℱ : Filtration ℝ mΩ}
  {E : Type v} [MeasurableSpace E] {ν : Measure E}

section Time

end Time

section Comp

/-- **A measurable function of the time, a predictable process and a marked predictable process
is marked predictable once it is cut to the positive times**, for a predictable process in the
sense of `Predictable`. -/
theorem MarkedPredictable.comp_measurable_of_predictable [SigmaFinite ν] {F₁ : Type*}
    {F₂ : Type*} {F₃ : Type*} [TopologicalSpace F₁] [TopologicalSpace.PseudoMetrizableSpace F₁]
    [MeasurableSpace F₁] [BorelSpace F₁] [Zero F₁] [MeasurableSpace F₂] [MeasurableSpace F₃]
    [Zero F₃] {F : ℝ × F₁ × F₂ → F₃} (hF : Measurable F) {Y : Ω → ℝ → F₁}
    (hY : Predictable ℱ Y) {Γ : Ω → ℝ → E → F₂} (hΓ : MarkedPredictable ℱ ν Γ) :
    MarkedPredictable ℱ ν fun (ω : Ω) (s : ℝ) (e : E) =>
      if 0 < s then F (s, Y ω s, Γ ω s e) else 0 :=
  (fun p2mMethodArg0 p2mMethodArg1 => _root_.Prove2MeSourceProof.h_d6ed8f97bdea5b0368dd302f p2mMethodArg0 p2mMethodArg1 hΓ) hF hY.measurable
/-- **A continuous function of the time, a predictable process and a marked predictable process
is marked predictable once it is cut to the positive times.** -/
theorem MarkedPredictable.comp_continuous [SigmaFinite ν] {F₁ : Type*} {F₂ : Type*}
    {F₃ : Type*} [TopologicalSpace F₁] [MeasurableSpace F₁] [OpensMeasurableSpace F₁]
    [TopologicalSpace F₂] [MeasurableSpace F₂] [OpensMeasurableSpace F₂]
    [SecondCountableTopologyEither F₁ F₂] [TopologicalSpace F₃] [MeasurableSpace F₃]
    [BorelSpace F₃] [Zero F₃] {F : ℝ × F₁ × F₂ → F₃} (hF : Continuous F) {Y : Ω → ℝ → F₁}
    (hY : Measurable[predictableSigma ℱ] fun q : ℝ × Ω => Y q.2 q.1)
    {Γ : Ω → ℝ → E → F₂} (hΓ : MarkedPredictable ℱ ν Γ) :
    MarkedPredictable ℱ ν fun (ω : Ω) (s : ℝ) (e : E) =>
      if 0 < s then F (s, Y ω s, Γ ω s e) else 0 :=
  (fun p2mMethodArg0 p2mMethodArg1 => _root_.Prove2MeSourceProof.h_d6ed8f97bdea5b0368dd302f p2mMethodArg0 p2mMethodArg1 hΓ) hF.measurable hY
end Comp

end LevyStochCalc.Probability


