-- Prove2me | Definitions.Def_SourceProof_b39c46ea153c4c96354bca13
-- name    : SourceProof_b39c46ea153c4c96354bca13
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-25T18:07:00.995901+00:00
-- url     : https://prove2.me/theorems/9d89c7ec-30ab-4b51-8cda-6119d7e476c4
-- title:
--   StochLean source theorem: ProbabilityTheory.adapted_stieltjesContinuousPart

import Definitions.Def_StochLean_Analysis_PathVariation_StieltjesContinuousPart_F000
import Definitions.Def_SourceProof_8510097a2a6d2946051d412e
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Data.Finset.Max
import Mathlib.Data.Finset.Sort
import Mathlib.MeasureTheory.Constructions.BorelSpace.Real
import Mathlib.MeasureTheory.Function.Floor
import Mathlib.MeasureTheory.Integral.Lebesgue.Countable
import Mathlib.MeasureTheory.Measure.NullMeasurable
import Mathlib.Probability.Kernel.Basic
import Mathlib.Probability.Kernel.MeasurableLIntegral
import Mathlib.Probability.Process.Adapted
import Mathlib.Probability.Process.Filtration
import Mathlib.Probability.Process.FiniteDimensionalLaws
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Topology.Algebra.Order.LiminfLimsup
import Mathlib.Topology.Bases
import Mathlib.Topology.EMetricSpace.BoundedVariation
import Mathlib.Topology.Instances.ENNReal.Lemmas
import Mathlib.Topology.Order.IsLUB
import Mathlib.Topology.UniformSpace.HeineCantor

/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/

/-! # Adaptedness of the continuous component of a random Stieltjes path -/

@[expose] public section

open MeasureTheory StochLean
open scoped NNReal

namespace ProbabilityTheory

theorem _root_.Prove2MeSourceProof.h_b39c46ea153c4c96354bca13
    {Ω : Type*} {mΩ : MeasurableSpace Ω} {F : Filtration ℝ≥0 mΩ}
    {B : Ω → StieltjesFunction ℝ≥0} (hB : Adapted F (fun t ω ↦ B ω t)) :
    Adapted F (fun t ω ↦ stieltjesContinuousPart (B ω) t) := by
  intro T
  let : MeasurableSpace Ω := F T
  exact _root_.Prove2MeSourceProof.h_8510097a2a6d2946051d412e T
    (fun t ht ↦ (hB t).mono (F.mono ht) le_rfl)
end ProbabilityTheory


