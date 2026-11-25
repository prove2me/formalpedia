-- Prove2me | Definitions.Def_StochLean_Probability_Process_Semimartingale_StochasticExponential_Characteristic_F000
-- name    : StochLean_Probability_Process_Semimartingale_StochasticExponential_Characteristic_F000
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-25T21:10:17.417015+00:00
-- url     : https://prove2.me/theorems/525275b7-b1f4-50c3-832d-67230aef625d
-- title:
--   StochLean: Probability.Process.Semimartingale.StochasticExponential.Characteristic F000

import Definitions.Def_StochLean_Probability_Process_Path_Complex_F000
import Definitions.Def_StochLean_Probability_Process_Semimartingale_QuadraticVariation_ContinuousPart_F000
import Mathlib.Algebra.BigOperators.Pi
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
import Mathlib.Analysis.SpecialFunctions.Log.Summable
import Mathlib.MeasureTheory.Function.LocallyIntegrable
import Mathlib.MeasureTheory.Function.StronglyMeasurable.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.Order.Filter.Finite
import Mathlib.Topology.Algebra.InfiniteSum.Order
import Mathlib.Topology.Algebra.InfiniteSum.Real
import Mathlib.Topology.Algebra.IsUniformGroup.Basic
import Mathlib.Topology.Compactness.Compact
import Mathlib.Topology.MetricSpace.Lipschitz
import Mathlib.Topology.MetricSpace.Pseudo.Lemmas
import Mathlib.Topology.MetricSpace.Pseudo.Real
import Mathlib.Topology.Order.Basic

/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/

/-! # The compensated characteristic exponential

The real compensation is positive: its imaginary coefficient has negative
bilinear quadratic variation. This is a function of the existing continuous
real bracket, not a second stochastic integration or bracket construction.
-/

@[expose] public section

open MeasureTheory
open scoped NNReal

namespace ProbabilityTheory

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsFiniteMeasure P]
  {F : Filtration ℝ≥0 mΩ} {X : ℝ≥0 → Ω → ℝ}

noncomputable def IsSemimartingale.characteristicExponent
    (hX : IsSemimartingale X F P) (hF : F.IsUsual P) (u : ℝ) : ℝ≥0 → Ω → ℂ :=
  complexProcess (fun t ω ↦ ((1 / 2 : ℝ) * u ^ 2) * hX.continuousQuadraticVariation hF t ω)
    (fun t ω ↦ u * X t ω)
noncomputable def IsSemimartingale.characteristicExponential
    (hX : IsSemimartingale X F P) (hF : F.IsUsual P) (u : ℝ) : ℝ≥0 → Ω → ℂ :=
  fun t ω ↦ Complex.exp (hX.characteristicExponent hF u t ω)
end ProbabilityTheory


