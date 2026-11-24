-- Prove2me | Definitions.Def_StochLean_Probability_Process_Path_CadlagWindowOscillation_F000
-- name    : StochLean_Probability_Process_Path_CadlagWindowOscillation_F000
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-24T21:56:59.864841+00:00
-- url     : https://prove2.me/theorems/237d94b9-e53b-472c-b811-443d15842d53
-- title:
--   StochLean: Probability.Process.Path.CadlagWindowOscillation F000

import Definitions.Def_StochLean_Probability_Process_Path_Supremum_F000
import Definitions.Def_StochLean_Probability_Process_Path_Supremum_F001
import Mathlib.Analysis.Normed.Group.Continuity
import Mathlib.Topology.Compactness.Compact
import Mathlib.Topology.MetricSpace.Pseudo.Lemmas
import Mathlib.Topology.Order.LeftRightLim

/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/

/-! # Measurable two-time short-window oscillations

The envelope uses two points of the existing clipped dense grid and an actual
order and strict-width guard. Countability makes it measurable. Two right-side
approximating sequences recover every strict window of a right-continuous
path; doubling a positive width also covers a closed-width window. Cadlag
compact boundedness proves finiteness before the real-valued bridge is used.
-/

@[expose] public section

open Set Filter MeasureTheory
open scoped NNReal ENNReal Topology

namespace ProbabilityTheory

variable {Ω : Type*} {mΩ : MeasurableSpace Ω}

/-- Absolute increments on ordered pairs of clipped dense times less than the
given width apart. This is an extended nonnegative supremum, not a maximum. -/
noncomputable def denseWindowOscillation (X : ℝ≥0 → Ω → ℝ)
    (T δ : ℝ≥0) (ω : Ω) : ℝ≥0∞ :=
  ⨆ i : ℕ, ⨆ j : ℕ,
    if denseTimeUpTo T i ≤ denseTimeUpTo T j ∧
        denseTimeUpTo T j < denseTimeUpTo T i + δ then
      ENNReal.ofReal ‖X (denseTimeUpTo T j) ω - X (denseTimeUpTo T i) ω‖ else 0
end ProbabilityTheory


