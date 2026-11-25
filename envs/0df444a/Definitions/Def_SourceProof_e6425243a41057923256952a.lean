-- Prove2me | Definitions.Def_SourceProof_e6425243a41057923256952a
-- name    : SourceProof_e6425243a41057923256952a
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-25T19:12:01.139592+00:00
-- url     : https://prove2.me/theorems/8085f086-ab57-5e85-9af2-45819dc78d51
-- title:
--   StochLean source theorem: MeasureTheory.Adapted.totalVariationProcess_of_rightContinuous

import Definitions.Def_SourceProof_06a61994cd7744e3d7c117fb
import Definitions.Def_SourceProof_c6775852856193851365c661

/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/

/-! # The adapted total-variation process

Variation is first kept in ENNReal, including infinite values. Right continuity,
not continuity, makes actual finite-partition sums converge to it. Real-valued
variation is the canonical Mathlib conversion; its finite-variation interpretation
requires the common-event locally BV hypothesis.
-/

@[expose] public section

open MeasureTheory StochLean Filter Set
open scoped NNReal ENNReal Topology

namespace ProbabilityTheory

variable {Ω : Type*} {mΩ : MeasurableSpace Ω}

end ProbabilityTheory

namespace MeasureTheory

open ProbabilityTheory

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {F : Filtration ℝ≥0 mΩ}
  {X : ℝ≥0 → Ω → ℝ} {P : Measure Ω}

namespace Adapted
theorem _root_.Prove2MeSourceProof.h_e6425243a41057923256952a (ha : Adapted F X)
    (hr : ∀ ω, IsRightContinuousPath (fun t ↦ X t ω)) :
    Adapted F (ProbabilityTheory.totalVariationProcess X) := by
  intro t
  have h := ((_root_.Prove2MeSourceProof.h_06a61994cd7744e3d7c117fb ha) hr t).ennreal_toReal
  have heq : ProbabilityTheory.totalVariationProcess X t =
      fun ω ↦ (ProbabilityTheory.eTotalVariationProcess X t ω).toReal :=
    funext (_root_.Prove2MeSourceProof.h_c6775852856193851365c661 X t)
  rw [heq]
  exact h
end Adapted

end MeasureTheory


