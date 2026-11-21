-- Prove2me | Definitions.Def_LevyStochCalc_Probability_MarkedPredictableComp_F000
-- name    : LevyStochCalc_Probability_MarkedPredictableComp_F000
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-20T20:12:07.928935+00:00
-- url     : https://prove2.me/theorems/2a0248ed-c2ac-403d-be2c-6739c27f5081
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
import Definitions.Def_SourceProof_801b26c6530d1a0902cf7deb
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

/-- A measurable set of positive times, carrying all sample points and marks, is marked
predictable. -/
theorem measurableSet_markedPredictableSigma_time_pos [SigmaFinite ν] {S : Set ℝ}
    (hS : MeasurableSet S) :
    MeasurableSet[markedPredictableSigma ℱ ν] {p : Ω × ℝ × E | 0 < p.2.1 ∧ p.2.1 ∈ S} := by
  have hrw : {p : Ω × ℝ × E | 0 < p.2.1 ∧ p.2.1 ∈ S}
      = (Set.univ : Set Ω) ×ˢ ((S ×ˢ (Set.univ : Set E))
          ∩ Set.Ioi (0 : ℝ) ×ˢ (Set.univ : Set E)) := by
    ext p
    simp only [Set.mem_setOf_eq, Set.mem_prod, Set.mem_univ, true_and, and_true,
      Set.mem_inter_iff, Set.mem_Ioi]
    exact and_comm
  rw [hrw]
  exact _root_.Prove2MeSourceProof.h_801b26c6530d1a0902cf7deb (hS.prod MeasurableSet.univ)
/-- A function on the time–mark space whose level sets, cut to the positive times, are marked
predictable is marked predictable once it is cut to the positive times. -/
theorem measurable_markedPredictableSigma_ite_pos [SigmaFinite ν] {G : Type*}
    [MeasurableSpace G] [Zero G] {g : Ω × ℝ × E → G}
    (hg : ∀ U : Set G, MeasurableSet U →
      MeasurableSet[markedPredictableSigma ℱ ν] (g ⁻¹' U ∩ {p : Ω × ℝ × E | 0 < p.2.1})) :
    Measurable[markedPredictableSigma ℱ ν]
      fun p : Ω × ℝ × E => if 0 < p.2.1 then g p else 0 := by
  classical
  have hpos := measurableSet_markedPredictableSigma_pos (Ω := Ω) (E := E) ℱ ν
  intro U hU
  have hkey := hg U hU
  by_cases h0 : (0 : G) ∈ U
  · have hrw : (fun p : Ω × ℝ × E => if 0 < p.2.1 then g p else 0) ⁻¹' U
        = (g ⁻¹' U ∩ {p : Ω × ℝ × E | 0 < p.2.1}) ∪ {p : Ω × ℝ × E | 0 < p.2.1}ᶜ := by
      ext p
      by_cases hp : 0 < p.2.1 <;> simp [hp, h0]
    rw [hrw]
    exact hkey.union hpos.compl
  · have hrw : (fun p : Ω × ℝ × E => if 0 < p.2.1 then g p else 0) ⁻¹' U
        = g ⁻¹' U ∩ {p : Ω × ℝ × E | 0 < p.2.1} := by
      ext p
      by_cases hp : 0 < p.2.1 <;> simp [hp, h0]
    rw [hrw]
    exact hkey
/-- The time coordinate of the time–mark space, cut to the positive times, is marked
predictable. -/
theorem measurable_markedPredictableSigma_time_pos [SigmaFinite ν] :
    Measurable[markedPredictableSigma ℱ ν]
      fun p : Ω × ℝ × E => if 0 < p.2.1 then p.2.1 else 0 :=
  measurable_markedPredictableSigma_ite_pos fun S hS => by
    have hrw : (fun p : Ω × ℝ × E => p.2.1) ⁻¹' S ∩ {p : Ω × ℝ × E | 0 < p.2.1}
        = {p : Ω × ℝ × E | 0 < p.2.1 ∧ p.2.1 ∈ S} := by
      ext p
      simp only [Set.mem_inter_iff, Set.mem_preimage, Set.mem_setOf_eq]
      exact and_comm
    rw [hrw]
    exact measurableSet_markedPredictableSigma_time_pos hS
end Time

section Comp

end Comp

end LevyStochCalc.Probability


