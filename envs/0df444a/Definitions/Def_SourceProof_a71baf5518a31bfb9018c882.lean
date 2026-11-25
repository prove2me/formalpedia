-- Prove2me | Definitions.Def_SourceProof_a71baf5518a31bfb9018c882
-- name    : SourceProof_a71baf5518a31bfb9018c882
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-25T12:44:26.821002+00:00
-- url     : https://prove2.me/theorems/565b2c40-15e2-586b-88f1-41b7d84e9967
-- title:
--   StochLean source theorem: ProbabilityTheory.compactDeviation_eq_dense

import Definitions.Def_StochLean_Probability_Process_UCP_F000
import Definitions.Def_SourceProof_0d990b6d42af60e405064fad
import Definitions.Def_SourceProof_845eb3d5bff7aa74f6afa784

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

theorem _root_.Prove2MeSourceProof.h_a71baf5518a31bfb9018c882 {T : ℝ≥0} {ω : Ω}
    (hX : IsRightContinuousPath (X · ω)) (hY : IsRightContinuousPath (Y · ω)) :
    compactDeviation X Y T ω =
      denseRunningSupremum (fun t ω ↦ ‖X t ω - Y t ω‖) T ω := by
  apply le_antisymm
  · apply iSup_le
    intro t
    apply iSup_le
    intro ht
    exact _root_.Prove2MeSourceProof.h_0d990b6d42af60e405064fad ht
      (fun s ↦ ((hX s).sub (hY s)).norm)
  · apply iSup_le
    intro n
    exact _root_.Prove2MeSourceProof.h_845eb3d5bff7aa74f6afa784 (min_le_left _ _) ω
end ProbabilityTheory


