-- Prove2me | Definitions.Def_SourceProof_22e9197c5f3b64379ebba20b
-- name    : SourceProof_22e9197c5f3b64379ebba20b
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-25T18:56:46.685275+00:00
-- url     : https://prove2.me/theorems/7ad95dd2-a84d-579b-9f38-be09942d8a5c
-- title:
--   StochLean source theorem: MeasureTheory.Adapted.isStronglyOptional_sub_finset_stopped_jumps

import Definitions.Def_SourceProof_0a41c493088d6b6495e37e42
import Definitions.Def_SourceProof_84d7aed1210aac0c6f6e217d

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

theorem _root_.Prove2MeSourceProof.h_22e9197c5f3b64379ebba20b {ι : Type*}
    (hX : Adapted F X) (hc : ∀ ω, IsCadlagPath (X · ω)) (s : Finset ι)
    (τ : ι → Ω → WithTop ℝ≥0) (hτ : ∀ i ∈ s, IsStoppingTime F (τ i)) :
    IsStronglyOptional F (fun t ω ↦ X t ω -
      ∑ i ∈ s, {ω | τ i ω ≤ (t : WithTop ℝ≥0)}.indicator
        (stoppedValueWithTerminal (jumpProcess X) (fun _ ↦ (0 : ℝ)) (τ i)) ω) := by
  have ho : StronglyMeasurable[F.optional] (Function.uncurry X) :=
    (_root_.Prove2MeSourceProof.h_0a41c493088d6b6495e37e42 hX) hc
  change StronglyMeasurable[F.optional] (fun p : ℝ≥0 × Ω ↦ X p.1 p.2 -
    ∑ i ∈ s, {ω | τ i ω ≤ (p.1 : WithTop ℝ≥0)}.indicator
      (MeasureTheory.stoppedValueWithTerminal (ProbabilityTheory.jumpProcess X) (fun _ ↦ (0 : ℝ)) (τ i)) p.2)
  apply ho.sub
  convert Finset.stronglyMeasurable_sum s (fun i hi ↦
    (_root_.Prove2MeSourceProof.h_84d7aed1210aac0c6f6e217d hX) hc (hτ i hi)) using 1
  funext p
  simp only [Finset.sum_apply, Function.uncurry]
end Adapted

end MeasureTheory


