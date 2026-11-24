-- Prove2me | Definitions.Def_SourceProof_16b415d0c40536c6ca3b78ee
-- name    : SourceProof_16b415d0c40536c6ca3b78ee
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-24T23:19:55.867415+00:00
-- url     : https://prove2.me/theorems/c2de46af-dfb3-42c7-9699-4aee4a79e623
-- title:
--   StochLean source theorem: MeasureTheory.stoppedValueWithTerminal_jump_eq_of_eq_coe

import Definitions.Def_StochLean_Probability_Process_Path_LeftLimit_F000
import Definitions.Def_StochLean_Probability_Process_Stopping_TerminalValue_F000
import Definitions.Def_SourceProof_6da37c641e8d3b5ccb3dfebc
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.MeasureTheory.Function.Floor
import Mathlib.MeasureTheory.MeasurableSpace.Prod
import Mathlib.MeasureTheory.Measure.NullMeasurable
import Mathlib.Probability.Process.Adapted
import Mathlib.Probability.Process.Filtration
import Mathlib.Probability.Process.Predictable

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

variable {mΩ : MeasurableSpace Ω} {P : Measure Ω}

end ProbabilityTheory

namespace MeasureTheory

open ProbabilityTheory

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {F : Filtration ℝ≥0 mΩ}
  {X : ℝ≥0 → Ω → ℝ} {τ : Ω → WithTop ℝ≥0}

theorem _root_.Prove2MeSourceProof.h_16b415d0c40536c6ca3b78ee {ω : Ω} {t : ℝ≥0}
    (ht : τ ω = (t : WithTop ℝ≥0)) :
    stoppedValueWithTerminal (jumpProcess X) (fun _ ↦ (0 : ℝ)) τ ω = jumpProcess X t ω := by
  have hne : τ ω ≠ ⊤ := ht ▸ WithTop.coe_ne_top
  rw [_root_.Prove2MeSourceProof.h_6da37c641e8d3b5ccb3dfebc hne]
  change ProbabilityTheory.jumpProcess X (τ ω).untopA ω = ProbabilityTheory.jumpProcess X t ω
  rw [ht]
  rfl
end MeasureTheory


