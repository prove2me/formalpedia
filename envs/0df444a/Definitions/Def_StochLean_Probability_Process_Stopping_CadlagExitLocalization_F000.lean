-- Prove2me | Definitions.Def_StochLean_Probability_Process_Stopping_CadlagExitLocalization_F000
-- name    : StochLean_Probability_Process_Stopping_CadlagExitLocalization_F000
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-24T16:06:51.114898+00:00
-- url     : https://prove2.me/theorems/8d21ff88-08fd-4330-9193-516bc5561bb8
-- title:
--   StochLean: Probability.Process.Stopping.CadlagExitLocalization F000

import Mathlib.Analysis.Normed.Group.Continuity
import Mathlib.MeasureTheory.Constructions.BorelSpace.Real
import Mathlib.MeasureTheory.Measure.NullMeasurable
import Mathlib.Probability.Process.Filtration
import Mathlib.Probability.Process.FiniteDimensionalLaws
import Mathlib.Probability.Process.HittingTime
import Mathlib.Probability.Process.LocalProperty
import Mathlib.Probability.Process.Stopping
import Mathlib.Topology.Bases
import Mathlib.Topology.Compactness.Compact
import Mathlib.Topology.Order.Compact
import Mathlib.Topology.Order.IsLUB
import Mathlib.Topology.Order.LeftRight
import Mathlib.Topology.Order.LeftRightLim

/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/

/-! # Capped open norm exits for cadlag localization

The stopping sequence is the existing open norm hit, capped by its increasing
integer threshold. Cadlag compact bounds imply divergence. Strictly before
the exit, the path is bounded by the threshold, and the same bound holds for
its left limit at the exit. A bound on positive-time jumps controls overshoot.

Without a jump bound the stopped process is not claimed to be bounded. Only
its jumps away from the stopping endpoint are at most twice the threshold;
the non-strict inequality and the exceptional endpoint are retained.
-/

@[expose] public section

open MeasureTheory Filter Set
open scoped NNReal Topology

namespace ProbabilityTheory

variable {Ω : Type*} {X : ℝ≥0 → Ω → ℝ} {ω : Ω}

/-- The native open norm exit, capped at the same positive integer level. -/
noncomputable def cappedNormExitSequence (X : ℝ≥0 → Ω → ℝ) (n : ℕ)
    (ω : Ω) : WithTop ℝ≥0 :=
  min (hittingAfter X {x : ℝ | ((n + 1 : ℕ) : ℝ) < ‖x‖} 0 ω)
    (((n + 1 : ℕ) : ℝ≥0) : WithTop ℝ≥0)
variable {mΩ : MeasurableSpace Ω} {F : Filtration ℝ≥0 mΩ} {P : Measure Ω}

end ProbabilityTheory

namespace MeasureTheory

open ProbabilityTheory

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {F : Filtration ℝ≥0 mΩ}
  {P : Measure Ω} {X : ℝ≥0 → Ω → ℝ}

end MeasureTheory


