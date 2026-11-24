-- Prove2me | Definitions.Def_StochLean_Probability_Process_Stopping_Oscillation_F000
-- name    : StochLean_Probability_Process_Stopping_Oscillation_F000
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-24T23:01:25.26741+00:00
-- url     : https://prove2.me/theorems/320d4a40-9e5b-4514-be59-2ceb0d26dc3a
-- title:
--   StochLean: Probability.Process.Stopping.Oscillation F000

import Definitions.Def_StochLean_Probability_Process_Path_LeftLimit_F000
import Mathlib.Analysis.Normed.Group.Continuity
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.MeasureTheory.Constructions.BorelSpace.Real
import Mathlib.MeasureTheory.Function.ConditionalExpectation.Indicator
import Mathlib.MeasureTheory.Function.ConditionalExpectation.Real
import Mathlib.MeasureTheory.Function.Floor
import Mathlib.MeasureTheory.Function.UniformIntegrable
import Mathlib.MeasureTheory.Measure.NullMeasurable
import Mathlib.Probability.Martingale.Basic
import Mathlib.Probability.Martingale.OptionalSampling
import Mathlib.Probability.Process.Adapted
import Mathlib.Probability.Process.Filtration
import Mathlib.Probability.Process.HittingTime
import Mathlib.Probability.Process.LocalProperty
import Mathlib.Probability.Process.Stopping
import Mathlib.Topology.Order.Compact
import Mathlib.Topology.Order.MonotoneConvergence
import Mathlib.Topology.Order.WithTop

/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/

/-! # Recursive oscillation stopping times

The next time is the existing first hit of `X - X^tau`, so it never evaluates an
unprovided value `X_infinity`. For a positive threshold, finite successive times
are strictly separated and their sampled values differ by at least the threshold.
Cadlag paths therefore force the actual recursive times to tend to infinity.
-/

@[expose] public section

open MeasureTheory Filter Set
open scoped NNReal Topology

namespace ProbabilityTheory

variable {Ω : Type*} {X : ℝ≥0 → Ω → ℝ}

noncomputable def nextOscillationTime (X : ℝ≥0 → Ω → ℝ) (ε : ℝ)
    (τ : Ω → WithTop ℝ≥0) : Ω → WithTop ℝ≥0 :=
  hittingAfter (X - stoppedProcess X τ) {x | ε < ‖x‖} 0
variable {mΩ : MeasurableSpace Ω} {F : Filtration ℝ≥0 mΩ} {P : Measure Ω}

end ProbabilityTheory


