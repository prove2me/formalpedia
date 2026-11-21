-- Prove2me | Definitions.Def_LevyStochCalc_Ito_ItoFormulaStopped_F000
-- name    : LevyStochCalc_Ito_ItoFormulaStopped_F000
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-20T23:08:41.924669+00:00
-- url     : https://prove2.me/theorems/8a80f2ef-6e24-4800-a215-19f8b1d4742f
-- title:
--   Source declarations: LevyStochCalc.Ito.ItoFormulaStopped
-- statement:
--   Source-preserving extracted declarations from LevyStochCalc.Ito.ItoFormulaStopped. Existing definitions, lemmas, instances, proofs and elaboration context are retained; generated import closure remains under review.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Brownian_VectorItoStopped_F001
import Definitions.Def_LevyStochCalc_Ito_ItoFormulaUnboundedClamp_F000
import Definitions.Def_LevyStochCalc_Ito_ItoFormulaUnboundedClamp_F001
import Definitions.Def_LevyStochCalc_Ito_ItoFormulaUnboundedClamp_F002
import Definitions.Def_LevyStochCalc_Ito_ItoFormulaUnboundedIntegrands_F000
import Definitions.Def_LevyStochCalc_Ito_ItoFormulaUnboundedIntegrands_F001
import Definitions.Def_LevyStochCalc_Ito_ItoFormulaUnboundedLimit_F000
import Definitions.Def_LevyStochCalc_Ito_ItoFormulaUnboundedLimit_F001
import Definitions.Def_SourceProof_8cfa002050fede424ae29a90
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.Calculus.FDeriv.Comp
import Mathlib.Analysis.Calculus.FDeriv.Const
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.MeanInequalities
import Mathlib.Analysis.Normed.Group.Constructions
import Mathlib.Analysis.Normed.Group.Continuity
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Analysis.SpecialFunctions.SmoothTransition
import Mathlib.Data.Rat.Denumerable
import Mathlib.MeasureTheory.Constructions.BorelSpace.ContinuousLinearMap
import Mathlib.MeasureTheory.Covering.DensityTheorem
import Mathlib.MeasureTheory.Function.ConditionalExpectation.CondJensen
import Mathlib.MeasureTheory.Function.ConditionalExpectation.PullOut
import Mathlib.MeasureTheory.Function.ConvergenceInMeasure
import Mathlib.MeasureTheory.Function.Floor
import Mathlib.MeasureTheory.Integral.Average
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.MeasureTheory.Integral.Layercake
import Mathlib.MeasureTheory.Measure.CharacteristicFunction.Basic
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
import Mathlib.MeasureTheory.Measure.MeasureSpace
import Mathlib.MeasureTheory.Measure.NullMeasurable
import Mathlib.Probability.Distributions.Poisson.Basic
import Mathlib.Probability.Independence.CharacteristicFunction
import Mathlib.Probability.Independence.InfinitePi
import Mathlib.Probability.Martingale.OptionalStopping
import Mathlib.Probability.Martingale.Upcrossing
import Mathlib.Probability.Notation
import Mathlib.Probability.Process.Filtration
import Mathlib.Probability.Process.Predictable
import Mathlib.Topology.Algebra.MulAction
import Mathlib.Topology.Instances.ENNReal.Lemmas
import Mathlib.Topology.MetricSpace.Basic
import Mathlib.Topology.MetricSpace.Bounded
import Mathlib.Topology.MetricSpace.Contracting
import Mathlib.Topology.Order.Compact
import Mathlib.Topology.Order.DenselyOrdered
import Mathlib.Topology.Order.LeftRight
import Mathlib.Topology.Order.LeftRightLim
import Mathlib.Topology.Order.Monotone
import Mathlib.Topology.Separation.Regular
import Mathlib.Topology.UniformSpace.Cauchy
import Mathlib.Topology.UniformSpace.HeineCantor
import Mathlib.Topology.UniformSpace.UniformEmbedding

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# Itô's formula along a stopped path

Stopping a vector Itô process at a stopping time of finite range stops each of the three
integrands of Itô's formula at the same time, so the formula for the stopped process reads as the
formula for the original one with every integrand cut off at the stopping time.

## Main statements

* `LevyStochCalc.Brownian.Ito.itoFormula_stopped` — Itô's formula along the stopped path.
-/

namespace LevyStochCalc.Brownian.Ito

open MeasureTheory ProbabilityTheory LevyStochCalc.Brownian.Multidim
open scoped NNReal ENNReal Topology

universe u

section StoppedFormula

variable {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {n d : ℕ} (W : Multidim.MultidimBrownianMotion P d)
  (ℱ' : Filtration ℝ ‹MeasurableSpace Ω›)
  (hcoord : ∀ k : Fin d, IsBrownianFiltration (W.W k) ℱ')

omit [MeasurableSpace Ω] [IsProbabilityMeasure P] in
/-- A function of the stopped path against a stopped integrand is the stopped product. -/
theorem stopped_comp_eq {X : ℝ → Ω → Fin n → ℝ} (τ : Ω → WithTop ℝ)
    (g : (Fin n → ℝ) → ℝ) (K : Ω → ℝ → ℝ) :
    (fun ω s => g (X (clipTime τ s ω) ω) * Probability.stopped τ K ω s)
      = Probability.stopped τ (fun ω s => g (X s ω) * K ω s) := by
  funext ω s
  simp only [Probability.stopped]
  by_cases hle : ((s : ℝ) : WithTop ℝ) ≤ τ ω
  · rw [if_pos hle, if_pos hle, clipTime_of_le hle]
  · rw [if_neg hle, if_neg hle, mul_zero]
omit [MeasurableSpace Ω] [IsProbabilityMeasure P] in
/-- A function of the stopped path against a sum of products of stopped integrands is the
stopped product. -/
theorem stopped_comp₂_eq {X : ℝ → Ω → Fin n → ℝ} (τ : Ω → WithTop ℝ)
    (g : (Fin n → ℝ) → ℝ) (K L : Fin d → Ω → ℝ → ℝ) :
    (fun ω s => g (X (clipTime τ s ω) ω)
        * ∑ k : Fin d, Probability.stopped τ (K k) ω s * Probability.stopped τ (L k) ω s)
      = Probability.stopped τ (fun ω s => g (X s ω) * ∑ k : Fin d, K k ω s * L k ω s) := by
  funext ω s
  simp only [Probability.stopped]
  by_cases hle : ((s : ℝ) : WithTop ℝ) ≤ τ ω
  · simp only [if_pos hle, clipTime_of_le hle]
  · simp [hle]
end StoppedFormula

end LevyStochCalc.Brownian.Ito


