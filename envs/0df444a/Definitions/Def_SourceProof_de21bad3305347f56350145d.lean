-- Prove2me | Definitions.Def_SourceProof_de21bad3305347f56350145d
-- name    : SourceProof_de21bad3305347f56350145d
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-25T14:36:08.012861+00:00
-- url     : https://prove2.me/theorems/ea98fccd-0324-435c-8d8e-7e287f7258d9
-- title:
--   StochLean source theorem: ProbabilityTheory.IsPoissonProcess.hasFiniteVariationPaths_compensated

import Definitions.Def_StochLean_Probability_Process_Path_FiniteVariation_F000
import Definitions.Def_StochLean_Probability_Process_Poisson_Basic_F000
import Definitions.Def_SourceProof_798d59aac4a0874192da8eb2
import Definitions.Def_SourceProof_8ba5e1d4066cc49c9a78b37c
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
import Mathlib.Topology.Algebra.Group.Basic
import Mathlib.Topology.Algebra.Monoid
import Mathlib.Topology.Algebra.Order.LiminfLimsup
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
theorem _root_.Prove2MeSourceProof.h_de21bad3305347f56350145d (hN : IsPoissonProcess N rate P) :
    HasFiniteVariationPaths (fun t ω ↦ (N t ω : ℝ) - (rate : ℝ) * t) P := by
  have hm : Monotone (fun t : ℝ≥0 ↦ (rate : ℝ) * t) := fun _ _ h ↦
    mul_le_mul_of_nonneg_left (NNReal.coe_le_coe.mpr h) rate.2
  filter_upwards [(_root_.Prove2MeSourceProof.h_8ba5e1d4066cc49c9a78b37c hN)] with ω hv
  exact _root_.Prove2MeSourceProof.h_798d59aac4a0874192da8eb2 hv
    (hm.monotoneOn Set.univ).locallyBoundedVariationOn
end IsPoissonProcess

end ProbabilityTheory


