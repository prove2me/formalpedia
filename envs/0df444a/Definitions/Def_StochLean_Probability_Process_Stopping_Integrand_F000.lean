-- Prove2me | Definitions.Def_StochLean_Probability_Process_Stopping_Integrand_F000
-- name    : StochLean_Probability_Process_Stopping_Integrand_F000
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-24T22:15:36.163178+00:00
-- url     : https://prove2.me/theorems/fe86e5b2-ece2-4fcf-84ad-ea1ea8d06cc0
-- title:
--   StochLean: Probability.Process.Stopping.Integrand F000

import Definitions.Def_StochLean_Probability_Process_Path_Caglad_F000
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.MeasureTheory.Function.Floor
import Mathlib.MeasureTheory.Measure.NullMeasurable
import Mathlib.Probability.Process.Adapted
import Mathlib.Probability.Process.Filtration
import Mathlib.Probability.Process.Predictable
import Mathlib.Probability.Process.Stopping
import Mathlib.Topology.Order.LeftRightLim

/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/

/-! # Cutting an integrand off after a stopping time

Unlike a stopped process, the cutoff is zero strictly after the stopping time.
The closed endpoint preserves the stopping jump and the initial value.
-/

@[expose] public section

open MeasureTheory Filter Set
open scoped NNReal Topology

namespace ProbabilityTheory

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {F : Filtration ℝ≥0 mΩ}

noncomputable def cutoffIntegrand (H : ℝ≥0 → Ω → ℝ) (τ : Ω → WithTop ℝ≥0)
    (t : ℝ≥0) (ω : Ω) : ℝ :=
  if (t : WithTop ℝ≥0) ≤ τ ω then H t ω else 0
end ProbabilityTheory


