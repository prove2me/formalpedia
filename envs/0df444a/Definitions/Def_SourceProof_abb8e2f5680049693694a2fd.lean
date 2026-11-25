-- Prove2me | Definitions.Def_SourceProof_abb8e2f5680049693694a2fd
-- name    : SourceProof_abb8e2f5680049693694a2fd
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-25T19:41:58.152639+00:00
-- url     : https://prove2.me/theorems/01b327f1-2d50-5505-b902-bc27926154b0
-- title:
--   StochLean source theorem: ProbabilityTheory.exists_simplePredictable_tendstoUCP

import Definitions.Def_StochLean_Probability_Process_Filtration_Usual_F001
import Definitions.Def_StochLean_Probability_Process_Path_Caglad_F000
import Definitions.Def_StochLean_Probability_Process_Semimartingale_SimplePredictable_F003
import Definitions.Def_StochLean_Probability_Process_UCP_F001
import Definitions.Def_SourceProof_546401850289f7fba55f35a5
import Mathlib.Analysis.Normed.Group.Continuity
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.Data.Finset.Max
import Mathlib.MeasureTheory.Constructions.Polish.Basic
import Mathlib.MeasureTheory.Function.ConditionalExpectation.Indicator
import Mathlib.MeasureTheory.Function.ConditionalExpectation.Real
import Mathlib.MeasureTheory.Function.Floor
import Mathlib.MeasureTheory.Function.UniformIntegrable
import Mathlib.MeasureTheory.Integral.Indicator
import Mathlib.Probability.Martingale.Basic
import Mathlib.Probability.Martingale.OptionalSampling
import Mathlib.Probability.Process.Adapted
import Mathlib.Probability.Process.HittingTime
import Mathlib.Probability.Process.LocalProperty
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Topology.EMetricSpace.BoundedVariation
import Mathlib.Topology.MetricSpace.Pseudo.Basic
import Mathlib.Topology.Order.Compact
import Mathlib.Topology.Order.DenselyOrdered
import Mathlib.Topology.Order.LeftRightLim
import Mathlib.Topology.Order.MonotoneConvergence
import Mathlib.Topology.Order.WithTop
import Mathlib.Topology.UniformSpace.HeineCantor

/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/

/-! # Source simple predictable density in the caglad UCP class

Protter II.10 with the first interval restored. Actual oscillation times of the
right-limit process and finite capped coefficients give the approximants. Their
number of cells is chosen from the proved vanishing exit probabilities. The source
allows unbounded finite coefficients, so no preliminary global coefficient bound
is imposed. No density assumption or general stochastic-integral selector is used.
-/

@[expose] public section

open MeasureTheory Filter Set
open scoped NNReal ENNReal Topology

namespace ProbabilityTheory

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {F : Filtration ℝ≥0 mΩ}
  {P : Measure Ω} [IsFiniteMeasure P] {H : ℝ≥0 → Ω → ℝ}


theorem _root_.Prove2MeSourceProof.h_abb8e2f5680049693694a2fd (ha : Adapted F H) (hF : F.IsUsual P)
    (hc : HasCagladPaths H P) :
    ∃ S : ℕ → ℝ≥0 → Ω → ℝ, (∀ n, IsSimplePredictable (S n) F) ∧ TendstoUCP P S atTop H := by
  obtain ⟨S, hS, _, hu⟩ := _root_.Prove2MeSourceProof.h_546401850289f7fba55f35a5 ha hF hc
  exact ⟨S, hS, hu⟩
end ProbabilityTheory


