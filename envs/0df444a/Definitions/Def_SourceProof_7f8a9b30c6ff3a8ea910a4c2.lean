-- Prove2me | Definitions.Def_SourceProof_7f8a9b30c6ff3a8ea910a4c2
-- name    : SourceProof_7f8a9b30c6ff3a8ea910a4c2
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-25T18:11:18.539134+00:00
-- url     : https://prove2.me/theorems/04be2b7d-4dea-4d02-8e4d-b43090adfdfe
-- title:
--   StochLean source theorem: ProbabilityTheory.IsCadlagPath.norm_jumpProcess_le_of_bound

import Definitions.Def_StochLean_Probability_Process_Path_LeftLimit_F000
import Definitions.Def_SourceProof_fca76a61bfc585d0b64bc810
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.MeasureTheory.Function.Floor
import Mathlib.MeasureTheory.MeasurableSpace.Prod
import Mathlib.MeasureTheory.Measure.NullMeasurable
import Mathlib.Probability.Process.Adapted
import Mathlib.Probability.Process.Filtration
import Mathlib.Probability.Process.Predictable
import Mathlib.Probability.Process.Stopping

/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/

/-! # Actual jump coefficients at stopping times

Jump sampling uses `stoppedValueWithTerminal` with explicitly zero terminal
coefficient. A finite lifetime samples the actual source jump; infinity gives
zero and never invokes an arbitrary finite-time fallback.

The jump process of an adapted cadlag process is optional, as the difference
between an optional process and its predictable left limit. Its stopped jump
is measurable at the native stopped sigma-algebra and is revealed only at
and after that time. Common path bounds control an arbitrary family of these
coefficients on one common event, without intersecting uncountably many
coordinate exceptional events and without any jump-count moment assumption.
-/

@[expose] public section

open MeasureTheory Filter Set
open scoped NNReal Topology

namespace ProbabilityTheory

variable {Ω : Type*} {X : ℝ≥0 → Ω → ℝ} {ω : Ω} {N : ℝ}

namespace IsCadlagPath

theorem _root_.Prove2MeSourceProof.h_7f8a9b30c6ff3a8ea910a4c2 (hX : IsCadlagPath (X · ω))
    (hb : ∀ t, ‖X t ω‖ ≤ N) (t : ℝ≥0) : ‖jumpProcess X t ω‖ ≤ 2 * N := by
  change ‖X t ω - ProbabilityTheory.leftLimitProcess X t ω‖ ≤ 2 * N
  have h := (norm_sub_le (X t ω) (ProbabilityTheory.leftLimitProcess X t ω)).trans
    (add_le_add (hb t) ((_root_.Prove2MeSourceProof.h_fca76a61bfc585d0b64bc810 hX) hb t))
  simpa only [two_mul] using h
end IsCadlagPath

variable {mΩ : MeasurableSpace Ω} {P : Measure Ω}

end ProbabilityTheory

namespace MeasureTheory

open ProbabilityTheory

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {F : Filtration ℝ≥0 mΩ}
  {X : ℝ≥0 → Ω → ℝ} {τ : Ω → WithTop ℝ≥0}

end MeasureTheory


