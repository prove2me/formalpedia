-- Prove2me | Definitions.Def_SourceProof_3371ea3822340c17baa8afad
-- name    : SourceProof_3371ea3822340c17baa8afad
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-25T00:45:18.170808+00:00
-- url     : https://prove2.me/theorems/86e30c88-ad22-45c9-a2d8-fd529d753f9d
-- title:
--   StochLean source theorem: ProbabilityTheory.IsPoissonProcess.hasCadlagPaths_compensated

import Definitions.Def_StochLean_Probability_Process_Poisson_Basic_F000
import Definitions.Def_SourceProof_2c0d4ca99a3f51a9d8eb6cb0
import Definitions.Def_SourceProof_44c235d61a2cdcb446e715a4
import Definitions.Def_SourceProof_5abd8ef5abbb365343c607a9
import Definitions.Def_SourceProof_7c758b3f54acb965f59f9d0b
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Analysis.Normed.Group.Uniform
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Analysis.SpecialFunctions.Exponential
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.MeasureTheory.Function.ConditionalExpectation.Indicator
import Mathlib.MeasureTheory.Function.ConditionalExpectation.Real
import Mathlib.MeasureTheory.Function.ConvergenceInMeasure
import Mathlib.MeasureTheory.Function.Floor
import Mathlib.MeasureTheory.Function.UniformIntegrable
import Mathlib.MeasureTheory.Measure.NullMeasurable
import Mathlib.Probability.ConditionalExpectation
import Mathlib.Probability.Martingale.Basic
import Mathlib.Probability.Martingale.OptionalSampling
import Mathlib.Probability.Process.Adapted
import Mathlib.Probability.Process.Filtration
import Mathlib.Probability.Process.LocalProperty
import Mathlib.Probability.Process.Stopping
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Order
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Topology.Algebra.Order.LiminfLimsup
import Mathlib.Topology.EMetricSpace.BoundedVariation
import Mathlib.Topology.MetricSpace.Pseudo.Basic
import Mathlib.Topology.UniformSpace.HeineCantor

/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/

/-! # The compensated Poisson martingale for an explicit filtration

The process is the actual real count minus its rate times time. Independent
future increments from the chosen past are explicit, so the theorem does not
assert a false martingale property for arbitrary enlarged filtrations.
-/

@[expose] public section

open MeasureTheory Filter
open scoped NNReal

namespace ProbabilityTheory

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsProbabilityMeasure P]
  {F : Filtration ℝ≥0 mΩ} {N : ℝ≥0 → Ω → ℕ} {rate : ℝ≥0}

namespace IsPoissonProcess
theorem _root_.Prove2MeSourceProof.h_3371ea3822340c17baa8afad (hN : IsPoissonProcess N rate P) :
    HasCadlagPaths (fun t ω ↦ (N t ω : ℝ) - (rate : ℝ) * t) P := by
  apply (_root_.Prove2MeSourceProof.h_44c235d61a2cdcb446e715a4 (_root_.Prove2MeSourceProof.h_5abd8ef5abbb365343c607a9 hN))
  exact (_root_.Prove2MeSourceProof.h_2c0d4ca99a3f51a9d8eb6cb0 (show ProbabilityTheory.HasContinuousPaths (fun (t : ℝ≥0) (_ : Ω) ↦ (rate : ℝ) * t) P from
    Filter.Eventually.of_forall fun _ ↦ continuous_const.mul NNReal.continuous_coe))
end IsPoissonProcess

end ProbabilityTheory


