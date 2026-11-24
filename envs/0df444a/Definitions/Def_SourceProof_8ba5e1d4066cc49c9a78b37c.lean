-- Prove2me | Definitions.Def_SourceProof_8ba5e1d4066cc49c9a78b37c
-- name    : SourceProof_8ba5e1d4066cc49c9a78b37c
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-24T23:13:58.544729+00:00
-- url     : https://prove2.me/theorems/74218734-2f4a-4621-8767-f17d4dce1880
-- title:
--   StochLean source theorem: ProbabilityTheory.IsPoissonProcess.hasFiniteVariationPaths_real

import Definitions.Def_StochLean_Probability_Process_Poisson_Basic_F000
import Definitions.Def_SourceProof_47d6db4d2888183b37773e7b
import Definitions.Def_SourceProof_6ed3c177b9234dc2ab8ed747
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

theorem _root_.Prove2MeSourceProof.h_8ba5e1d4066cc49c9a78b37c (hN : IsPoissonProcess N rate P) :
    HasFiniteVariationPaths (fun t ω ↦ (N t ω : ℝ)) P :=
  (_root_.Prove2MeSourceProof.h_6ed3c177b9234dc2ab8ed747 (_root_.Prove2MeSourceProof.h_47d6db4d2888183b37773e7b hN))
end ProbabilityTheory.IsPoissonProcess


