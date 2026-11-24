-- Prove2me | Definitions.Def_StochLean_Probability_Process_Stopping_Oscillation_F001
-- name    : StochLean_Probability_Process_Stopping_Oscillation_F001
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-24T23:02:08.321927+00:00
-- url     : https://prove2.me/theorems/f6903f74-df2c-4c00-97df-34dc6f4998d2
-- title:
--   StochLean: Probability.Process.Stopping.Oscillation F001

import Definitions.Def_StochLean_Probability_Process_Path_LeftLimit_F000
import Definitions.Def_SourceProof_245119f42083b7c11a8dd571
import Definitions.Def_SourceProof_38b6716030de814054336ad8
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

private theorem rightContinuous_sub_stopped {τ : Ω → WithTop ℝ≥0} {ω : Ω}
    (hX : IsRightContinuousPath (X · ω)) :
    IsRightContinuousPath (fun t ↦ X t ω - stoppedProcess X τ t ω) := by
  cases hτ : τ ω with
  | top =>
    have heq : (fun t ↦ X t ω - stoppedProcess X τ t ω) = fun _ ↦ (0 : ℝ) := by
      funext t
      rw [stoppedProcess_eq_of_le (by rw [hτ]; exact le_top), sub_self]
    rw [heq]
    exact _root_.Prove2MeSourceProof.h_245119f42083b7c11a8dd571 continuous_const
  | coe T =>
    have heq : (fun t ↦ X t ω - stoppedProcess X τ t ω) =
        fun t ↦ X t ω - X (min t T) ω := by
      funext t
      change X t ω - X (min (t : WithTop ℝ≥0) (τ ω)).untopA ω = _
      rw [hτ, ← WithTop.coe_min]
      rfl
    rw [heq]
    exact fun t ↦ (hX t).sub ((_root_.Prove2MeSourceProof.h_38b6716030de814054336ad8 hX) T t)
variable {mΩ : MeasurableSpace Ω} {F : Filtration ℝ≥0 mΩ} {P : Measure Ω}

end ProbabilityTheory


