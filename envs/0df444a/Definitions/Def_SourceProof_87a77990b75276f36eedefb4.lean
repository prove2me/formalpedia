-- Prove2me | Definitions.Def_SourceProof_87a77990b75276f36eedefb4
-- name    : SourceProof_87a77990b75276f36eedefb4
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-24T16:08:02.652301+00:00
-- url     : https://prove2.me/theorems/8a39520d-2dcc-44e9-8911-76a77bef7799
-- title:
--   StochLean source theorem: ProbabilityTheory.measure_ucp_deviation_triangle

import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.MeasureTheory.Constructions.BorelSpace.Real
import Mathlib.MeasureTheory.Function.ConvergenceInMeasure
import Mathlib.Probability.Process.FiniteDimensionalLaws
import Mathlib.Topology.Bases
import Mathlib.Topology.MetricSpace.Cauchy
import Mathlib.Topology.MetricSpace.UniformConvergence
import Mathlib.Topology.Order.IsLUB
import Mathlib.Topology.Order.LeftRight

/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/

/-! # UCP-Cauchy sequences and a common-event uniform Cauchy subsequence

The criterion uses the existing UCP strict-deviation events. The subsequence is
constructed by a summable-probability diagonal, without assuming measurable paths
or continuity of an outer measure on arbitrary decreasing sets.
-/

@[expose] public section

open MeasureTheory Filter Set
open scoped NNReal ENNReal Topology

namespace ProbabilityTheory

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω}
  {X : ℕ → ℝ≥0 → Ω → ℝ} {Y : ℝ≥0 → Ω → ℝ}

theorem _root_.Prove2MeSourceProof.h_87a77990b75276f36eedefb4 (X Y Z : ℝ≥0 → Ω → ℝ) (T : ℝ≥0) (ε : ℝ) :
    P {ω | ∃ t ≤ T, ε < ‖X t ω - Z t ω‖} ≤
      P {ω | ∃ t ≤ T, ε / 2 < ‖X t ω - Y t ω‖} +
        P {ω | ∃ t ≤ T, ε / 2 < ‖Y t ω - Z t ω‖} := by
  apply (measure_mono (t := {ω | ∃ t ≤ T, ε / 2 < ‖X t ω - Y t ω‖} ∪
    {ω | ∃ t ≤ T, ε / 2 < ‖Y t ω - Z t ω‖}) ?_).trans (measure_union_le _ _)
  rintro ω ⟨t, ht, hω⟩
  by_cases hXY : ε / 2 < ‖X t ω - Y t ω‖
  · exact Or.inl ⟨t, ht, hXY⟩
  · refine Or.inr ⟨t, ht, ?_⟩
    have h := dist_triangle (X t ω) (Y t ω) (Z t ω)
    simp only [dist_eq_norm_sub] at h
    have hXY := le_of_not_gt hXY
    linarith
end ProbabilityTheory


