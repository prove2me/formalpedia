-- Prove2me | Definitions.Def_SourceProof_20377c625b34905cce0ac877
-- name    : SourceProof_20377c625b34905cce0ac877
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-25T18:46:24.392056+00:00
-- url     : https://prove2.me/theorems/5b9a6038-abb4-53dd-b8a3-96f7bcf4d40f
-- title:
--   StochLean source theorem: MeasureTheory.Adapted.stronglyMeasurable_stopped_jump

import Definitions.Def_StochLean_Probability_Process_Stopping_TerminalValue_F000
import Definitions.Def_SourceProof_0859bfd91b5c292257b9a768
import Definitions.Def_SourceProof_7fabbd3583f68ce6bd1634ea

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
theorem _root_.Prove2MeSourceProof.h_20377c625b34905cce0ac877 (hX : Adapted F X)
    (hc : ∀ ω, IsCadlagPath (X · ω)) (hτ : IsStoppingTime F τ) :
    StronglyMeasurable[hτ.measurableSpace]
      (stoppedValueWithTerminal (jumpProcess X) (fun _ ↦ (0 : ℝ)) τ) :=
  (_root_.Prove2MeSourceProof.h_0859bfd91b5c292257b9a768 ((_root_.Prove2MeSourceProof.h_7fabbd3583f68ce6bd1634ea hX) hc))
    stronglyMeasurable_const hτ
end Adapted

end MeasureTheory


