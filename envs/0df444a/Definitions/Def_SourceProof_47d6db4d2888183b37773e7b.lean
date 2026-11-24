-- Prove2me | Definitions.Def_SourceProof_47d6db4d2888183b37773e7b
-- name    : SourceProof_47d6db4d2888183b37773e7b
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-24T21:58:13.216611+00:00
-- url     : https://prove2.me/theorems/00084a8f-a48a-49f9-9d77-50506ebf6903
-- title:
--   StochLean source theorem: ProbabilityTheory.IsPoissonProcess.hasMonotonePaths_real

import Definitions.Def_StochLean_Probability_Process_Poisson_Basic_F000
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.MeasureTheory.Function.ConditionalExpectation.Indicator
import Mathlib.MeasureTheory.Function.ConditionalExpectation.Real
import Mathlib.MeasureTheory.Function.ConvergenceInMeasure
import Mathlib.MeasureTheory.Function.Floor
import Mathlib.MeasureTheory.Function.UniformIntegrable
import Mathlib.MeasureTheory.Measure.NullMeasurable
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

/-! # The real-valued Poisson counting process is a semimartingale

Real left limits follow from monotonicity; right continuity is transported from the
canonical counting-process predicate. No cadlag path realization is assumed in addition
to those existing path properties. Adaptedness to the chosen filtration remains explicit.
-/

@[expose] public section

open MeasureTheory Filter Set
open scoped NNReal ENNReal Topology

namespace ProbabilityTheory.IsPoissonProcess

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsProbabilityMeasure P]
  {N : ℝ≥0 → Ω → ℕ} {rate : ℝ≥0}

theorem _root_.Prove2MeSourceProof.h_47d6db4d2888183b37773e7b (hN : IsPoissonProcess N rate P) :
    HasMonotonePaths (fun t ω ↦ (N t ω : ℝ)) P := by
  filter_upwards [hN.monotonePaths] with ω hω
  intro s t hst
  change (N s ω : ℝ) ≤ (N t ω : ℝ)
  exact_mod_cast hω hst
end ProbabilityTheory.IsPoissonProcess


