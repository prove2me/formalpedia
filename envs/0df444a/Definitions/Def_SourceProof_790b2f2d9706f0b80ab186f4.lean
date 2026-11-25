-- Prove2me | Definitions.Def_SourceProof_790b2f2d9706f0b80ab186f4
-- name    : SourceProof_790b2f2d9706f0b80ab186f4
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-25T14:33:39.102027+00:00
-- url     : https://prove2.me/theorems/e08dd79f-aceb-4d11-b9b5-3b442d3d220a
-- title:
--   StochLean source theorem: ProbabilityTheory.aemeasurable_compactDeviation

import Definitions.Def_StochLean_Probability_Process_UCP_F000
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

theorem _root_.Prove2MeSourceProof.h_790b2f2d9706f0b80ab186f4 (hX : ∀ t, Measurable (X t))
    (hY : ∀ t, Measurable (Y t))
    (hrX : HasRightContinuousPaths X P) (hrY : HasRightContinuousPaths Y P) (T : ℝ≥0) :
    AEMeasurable (compactDeviation X Y T) P := by
  have hm := (_root_.Prove2MeSourceProof.h_4a6ff19237aa56ae481190c2
    (fun t ↦ ((hX t).sub (hY t)).norm) T).aemeasurable (μ := P)
  apply hm.congr
  filter_upwards [hrX, hrY] with ω hx hy
  exact (_root_.Prove2MeSourceProof.h_a71baf5518a31bfb9018c882 hx hy).symm
end ProbabilityTheory


