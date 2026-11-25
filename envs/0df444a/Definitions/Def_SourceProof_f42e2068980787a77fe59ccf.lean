-- Prove2me | Definitions.Def_SourceProof_f42e2068980787a77fe59ccf
-- name    : SourceProof_f42e2068980787a77fe59ccf
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-25T17:51:38.284661+00:00
-- url     : https://prove2.me/theorems/82d18d01-c869-5afa-a518-5f80f20f2e46
-- title:
--   StochLean source theorem: ProbabilityTheory.measurable_compactDeviation

import Definitions.Def_SourceProof_4a6ff19237aa56ae481190c2
import Definitions.Def_SourceProof_a71baf5518a31bfb9018c882

/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/

/-!
# Uniform convergence on compact time intervals in probability

The compact deviation has an extended nonnegative value, so it never uses a
default real supremum of an unbounded set. Its equality with a countable dense
supremum is proved on right-continuous paths. Measurability is then a theorem,
not an assumption hidden in the definition of an uncountable supremum.
-/

@[expose] public section

open MeasureTheory Filter Set
open scoped NNReal ENNReal Topology

namespace ProbabilityTheory

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω}
  {X Y : ℝ≥0 → Ω → ℝ}

theorem _root_.Prove2MeSourceProof.h_f42e2068980787a77fe59ccf (hX : ∀ t, Measurable (X t))
    (hY : ∀ t, Measurable (Y t))
    (hrX : ∀ ω, IsRightContinuousPath (X · ω))
    (hrY : ∀ ω, IsRightContinuousPath (Y · ω)) (T : ℝ≥0) :
    Measurable (compactDeviation X Y T) := by
  have heq : ProbabilityTheory.compactDeviation X Y T =
      ProbabilityTheory.denseRunningSupremum (fun t ω ↦ ‖X t ω - Y t ω‖) T :=
    funext fun ω ↦ _root_.Prove2MeSourceProof.h_a71baf5518a31bfb9018c882 (hrX ω) (hrY ω)
  rw [heq]
  exact _root_.Prove2MeSourceProof.h_4a6ff19237aa56ae481190c2 (fun t ↦ ((hX t).sub (hY t)).norm) T
end ProbabilityTheory


