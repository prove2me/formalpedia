-- Prove2me | Definitions.Def_StochLean_Probability_Process_Semimartingale_StochasticArea_Exponent_F000
-- name    : StochLean_Probability_Process_Semimartingale_StochasticArea_Exponent_F000
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-25T20:03:19.429533+00:00
-- url     : https://prove2.me/theorems/8cd7ff05-bafb-5124-9c76-a6648e305897
-- title:
--   StochLean: Probability.Process.Semimartingale.StochasticArea.Exponent F000

import Definitions.Def_StochLean_ForMathlib_Analysis_LevyAreaRiccati_F000
import Definitions.Def_StochLean_Probability_Process_Path_Complex_F000
import Definitions.Def_StochLean_Probability_Process_Semimartingale_StochasticArea_Basic_F000
import Mathlib.Algebra.BigOperators.Pi
import Mathlib.Algebra.QuadraticDiscriminant
import Mathlib.Analysis.Calculus.ContDiff.Comp
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.Calculus.ContDiff.RCLike
import Mathlib.Analysis.Calculus.DSlope
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.FDeriv.CompCLM
import Mathlib.Analysis.Calculus.Taylor
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Analysis.Complex.RealDeriv
import Mathlib.Analysis.Normed.Group.Constructions
import Mathlib.Analysis.Normed.Group.InfiniteSum
import Mathlib.Analysis.Normed.Group.Real
import Mathlib.Analysis.Normed.Group.Uniform
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
import Mathlib.Data.Finset.Sort
import Mathlib.MeasureTheory.Constructions.BorelSpace.Order
import Mathlib.MeasureTheory.Function.LocallyIntegrable
import Mathlib.MeasureTheory.Function.StronglyMeasurable.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Integral.Bochner.SumMeasure
import Mathlib.MeasureTheory.Integral.Lebesgue.Countable
import Mathlib.MeasureTheory.Integral.MeanInequalities
import Mathlib.MeasureTheory.Measure.Decomposition.RadonNikodym
import Mathlib.MeasureTheory.Measure.Dirac
import Mathlib.MeasureTheory.Measure.GiryMonad
import Mathlib.MeasureTheory.Measure.Real
import Mathlib.MeasureTheory.Measure.Stieltjes
import Mathlib.MeasureTheory.Measure.Typeclasses.NullSingletonClass
import Mathlib.MeasureTheory.Measure.Typeclasses.SFinite
import Mathlib.Order.Filter.Finite
import Mathlib.Probability.Kernel.Basic
import Mathlib.Probability.Kernel.MeasurableIntegral
import Mathlib.Probability.Kernel.MeasurableLIntegral
import Mathlib.Tactic
import Mathlib.Topology.Algebra.Group.Basic
import Mathlib.Topology.Algebra.InfiniteSum.Order
import Mathlib.Topology.Algebra.InfiniteSum.Real
import Mathlib.Topology.Algebra.InfiniteSum.Ring
import Mathlib.Topology.EMetricSpace.VariationOnFromTo
import Mathlib.Topology.Instances.ENNReal.Lemmas
import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Topology.MetricSpace.Pseudo.Lemmas
import Mathlib.Topology.MetricSpace.Pseudo.Real
import Mathlib.Topology.Order.Basic
import Mathlib.Topology.UniformSpace.UniformApproximation

/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/

/-! # The actual Riccati-compensated area exponential

The clock is explicit: it may be deterministic time or the existing continuous
bracket. The process is constructed from the actual area integral, and its
semimartingale, continuity, endpoint and norm properties are proved here.
The local-martingale property still requires the stochastic drift calculation.
-/

@[expose] public section

open MeasureTheory Filter StochLean
open scoped NNReal

namespace ProbabilityTheory

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsFiniteMeasure P]
  {F : Filtration ℝ≥0 mΩ} {X Y Q : ℝ≥0 → Ω → ℝ}

noncomputable def IsSemimartingale.stochasticAreaExponent
    (hX : IsSemimartingale X F P) (hY : IsSemimartingale Y F P) (hF : F.IsUsual P)
    (Q : ℝ≥0 → Ω → ℝ) (u T : ℝ) : ℝ≥0 → Ω → ℂ :=
  complexProcess
    (fun t ω ↦ -(1 / 2 : ℝ) * (levyAreaAlpha u T (Q t ω) *
      (X t ω ^ 2 + Y t ω ^ 2)) + levyAreaBeta u T (Q t ω))
    (fun t ω ↦ u * hX.stochasticArea hY hF t ω)
noncomputable def IsSemimartingale.stochasticAreaExponential
    (hX : IsSemimartingale X F P) (hY : IsSemimartingale Y F P) (hF : F.IsUsual P)
    (Q : ℝ≥0 → Ω → ℝ) (u T : ℝ) : ℝ≥0 → Ω → ℂ :=
  fun t ω ↦ Complex.exp (hX.stochasticAreaExponent hY hF Q u T t ω)
end ProbabilityTheory


