-- Prove2me | Definitions.Def_SourceProof_c6bf0251dfd0b9d2b4772331
-- name    : SourceProof_c6bf0251dfd0b9d2b4772331
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-25T19:03:07.334916+00:00
-- url     : https://prove2.me/theorems/e2852644-1ef1-5946-962f-f0e82a72f223
-- title:
--   StochLean source theorem: MeasureTheory.Adapted.stronglyAdapted_sub_finset_stopped_jumps

import Definitions.Def_SourceProof_1a62c55b8d71b214cbc871c3
import Definitions.Def_SourceProof_22e9197c5f3b64379ebba20b

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
theorem _root_.Prove2MeSourceProof.h_c6bf0251dfd0b9d2b4772331 {ι : Type*}
    (hX : Adapted F X) (hc : ∀ ω, IsCadlagPath (X · ω)) (s : Finset ι)
    (τ : ι → Ω → WithTop ℝ≥0) (hτ : ∀ i ∈ s, IsStoppingTime F (τ i)) :
    StronglyAdapted F (fun t ω ↦ X t ω -
      ∑ i ∈ s, {ω | τ i ω ≤ (t : WithTop ℝ≥0)}.indicator
        (stoppedValueWithTerminal (jumpProcess X) (fun _ ↦ (0 : ℝ)) (τ i)) ω) :=
  (_root_.Prove2MeSourceProof.h_1a62c55b8d71b214cbc871c3 ((_root_.Prove2MeSourceProof.h_22e9197c5f3b64379ebba20b hX) hc s τ hτ))
end Adapted

end MeasureTheory


