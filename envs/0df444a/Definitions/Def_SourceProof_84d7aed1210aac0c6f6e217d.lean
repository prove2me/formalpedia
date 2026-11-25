-- Prove2me | Definitions.Def_SourceProof_84d7aed1210aac0c6f6e217d
-- name    : SourceProof_84d7aed1210aac0c6f6e217d
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-25T18:51:38.092216+00:00
-- url     : https://prove2.me/theorems/481e9caf-2e32-522f-bdf7-96aa90c3f4e6
-- title:
--   StochLean source theorem: MeasureTheory.Adapted.isStronglyOptional_stopped_jump_step

import Definitions.Def_StochLean_Probability_Process_Measurability_Optional_F001
import Definitions.Def_StochLean_Probability_Process_Path_LeftLimit_F000
import Definitions.Def_StochLean_Probability_Process_Stopping_TerminalValue_F000
import Definitions.Def_SourceProof_20377c625b34905cce0ac877
import Definitions.Def_SourceProof_b81c9b8175076e0b66117dff

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
theorem _root_.Prove2MeSourceProof.h_84d7aed1210aac0c6f6e217d (hX : Adapted F X)
    (hc : ∀ ω, IsCadlagPath (X · ω)) (hτ : IsStoppingTime F τ) :
    IsStronglyOptional F (fun t : ℝ≥0 ↦
      {ω | τ ω ≤ (t : WithTop ℝ≥0)}.indicator
        (stoppedValueWithTerminal (jumpProcess X) (fun _ ↦ (0 : ℝ)) τ)) :=
  (fun p2mMethodArg0 => _root_.Prove2MeSourceProof.h_b81c9b8175076e0b66117dff p2mMethodArg0 ((_root_.Prove2MeSourceProof.h_20377c625b34905cce0ac877 hX) hc hτ)) hτ
end Adapted

end MeasureTheory


