-- Prove2me | Definitions.Def_SourceProof_9b3b467d9208979297cd6213
-- name    : SourceProof_9b3b467d9208979297cd6213
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-25T12:44:53.515132+00:00
-- url     : https://prove2.me/theorems/32cd7397-91d1-421c-86f5-a22204e5bce8
-- title:
--   StochLean source theorem: MeasureTheory.abs_stoppedProcess_hittingAfter_le

import Definitions.Def_SourceProof_b74f6a65e2b4b7aa5b730057

/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/

/-! # Continuous-path hitting times

These results use Mathlib's `hittingAfter`, not a second hitting-time definition.
Closed targets are attained when the hitting time is finite. For real processes,
compact maxima and a countable dense grid give measurable closed-level hitting times.
-/

@[expose] public section

open MeasureTheory Set Filter
open scoped NNReal ENNReal Topology

namespace MeasureTheory

variable {Ω E : Type*} [TopologicalSpace E]

end MeasureTheory

namespace ProbabilityTheory

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {X : ℝ≥0 → Ω → ℝ}

end ProbabilityTheory

namespace MeasureTheory

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {F : Filtration ℝ≥0 mΩ}
  {X : ℝ≥0 → Ω → ℝ}

theorem _root_.Prove2MeSourceProof.h_9b3b467d9208979297cd6213 {a : ℝ} {ω : Ω}
    (hc : Continuous (X · ω)) (hzero : |X 0 ω| ≤ a) (t : ℝ≥0) :
    |stoppedProcess X (hittingAfter X {x | a ≤ |x|} 0) t ω| ≤ a := by
  apply _root_.Prove2MeSourceProof.h_b74f6a65e2b4b7aa5b730057 hc hzero
  have hne : min (t : WithTop ℝ≥0) (hittingAfter X {x | a ≤ |x|} 0 ω) ≠ ⊤ :=
    ne_top_of_le_ne_top WithTop.coe_ne_top (min_le_left _ _)
  rw [WithTop.untopA_eq_untop hne, WithTop.coe_untop]
  exact min_le_right _ _
end MeasureTheory


