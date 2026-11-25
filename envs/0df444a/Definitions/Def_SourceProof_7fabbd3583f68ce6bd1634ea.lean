-- Prove2me | Definitions.Def_SourceProof_7fabbd3583f68ce6bd1634ea
-- name    : SourceProof_7fabbd3583f68ce6bd1634ea
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-25T18:37:13.972083+00:00
-- url     : https://prove2.me/theorems/5d0320e7-0892-4df0-81d7-7e7a7ba28f1e
-- title:
--   StochLean source theorem: MeasureTheory.Adapted.isStronglyOptional_jumpProcess_of_cadlag

import Definitions.Def_StochLean_Probability_Process_Measurability_Optional_F001
import Definitions.Def_StochLean_Probability_Process_Path_LeftLimit_F000
import Definitions.Def_SourceProof_0a41c493088d6b6495e37e42
import Definitions.Def_SourceProof_5544cb84f6e1d4dffa6eb498
import Definitions.Def_SourceProof_6781543f132c74b0c839e817
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

variable {mΩ : MeasurableSpace Ω} {P : Measure Ω}

end ProbabilityTheory

namespace MeasureTheory

open ProbabilityTheory

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {F : Filtration ℝ≥0 mΩ}
  {X : ℝ≥0 → Ω → ℝ} {τ : Ω → WithTop ℝ≥0}

namespace Adapted
theorem _root_.Prove2MeSourceProof.h_7fabbd3583f68ce6bd1634ea (hX : Adapted F X)
    (hc : ∀ ω, IsCadlagPath (X · ω)) : IsStronglyOptional F (jumpProcess X) := by
  have ho : StronglyMeasurable[F.optional] (Function.uncurry X) :=
    (_root_.Prove2MeSourceProof.h_0a41c493088d6b6495e37e42 hX) hc
  have hl : StronglyMeasurable[F.optional] (Function.uncurry (ProbabilityTheory.leftLimitProcess X)) :=
    (_root_.Prove2MeSourceProof.h_6781543f132c74b0c839e817 ((_root_.Prove2MeSourceProof.h_5544cb84f6e1d4dffa6eb498 hX) hc))
  change StronglyMeasurable[F.optional]
    (fun p : ℝ≥0 × Ω ↦ X p.1 p.2 - ProbabilityTheory.leftLimitProcess X p.1 p.2)
  exact ho.sub hl
end Adapted

end MeasureTheory


