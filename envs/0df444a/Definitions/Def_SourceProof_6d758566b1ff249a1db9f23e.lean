-- Prove2me | Definitions.Def_SourceProof_6d758566b1ff249a1db9f23e
-- name    : SourceProof_6d758566b1ff249a1db9f23e
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-25T18:31:19.240665+00:00
-- url     : https://prove2.me/theorems/faceca6a-5656-4eba-b62d-8835a590dab0
-- title:
--   StochLean source theorem: ProbabilityTheory.HasCadlagPaths.ae_forall_norm_stopped_jump_le_of_bound

import Definitions.Def_StochLean_Probability_Process_Path_LeftLimit_F000
import Definitions.Def_SourceProof_407218b22ae1495f01bcf52b
import Definitions.Def_SourceProof_6da37c641e8d3b5ccb3dfebc
import Definitions.Def_SourceProof_cd52bba90d11cc31e1b57a3e
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

namespace HasCadlagPaths

theorem _root_.Prove2MeSourceProof.h_6d758566b1ff249a1db9f23e {ι : Type*}
    (hc : HasCadlagPaths X P) (hb : ∀ᵐ ω ∂P, ∀ t, ‖X t ω‖ ≤ N)
    (τ : ι → Ω → WithTop ℝ≥0) :
    ∀ᵐ ω ∂P, ∀ i,
      ‖stoppedValueWithTerminal (jumpProcess X) (fun _ ↦ (0 : ℝ)) (τ i) ω‖ ≤ 2 * N := by
  filter_upwards [(_root_.Prove2MeSourceProof.h_cd52bba90d11cc31e1b57a3e hc) hb, hb] with ω hj hbω i
  by_cases ht : τ i ω = ⊤
  · rw [_root_.Prove2MeSourceProof.h_407218b22ae1495f01bcf52b ht, norm_zero]
    exact mul_nonneg (by norm_num) ((norm_nonneg (X 0 ω)).trans (hbω 0))
  · rw [_root_.Prove2MeSourceProof.h_6da37c641e8d3b5ccb3dfebc ht]
    exact hj (τ i ω).untopA
end HasCadlagPaths

end ProbabilityTheory

namespace MeasureTheory

open ProbabilityTheory

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {F : Filtration ℝ≥0 mΩ}
  {X : ℝ≥0 → Ω → ℝ} {τ : Ω → WithTop ℝ≥0}

end MeasureTheory


