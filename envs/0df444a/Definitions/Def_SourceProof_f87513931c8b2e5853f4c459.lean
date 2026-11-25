-- Prove2me | Definitions.Def_SourceProof_f87513931c8b2e5853f4c459
-- name    : SourceProof_f87513931c8b2e5853f4c459
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-25T17:56:52.236484+00:00
-- url     : https://prove2.me/theorems/b0a72c6c-0b67-5218-8bc0-728b7eed1cbd
-- title:
--   StochLean source theorem: MeasureTheory.tendsto_hittingAfter_abs_nat

import Definitions.Def_SourceProof_8060b70dbd7753b7696a7230

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


theorem _root_.Prove2MeSourceProof.h_f87513931c8b2e5853f4c459 {ω : Ω} (hc : Continuous (X · ω)) :
    Tendsto (fun n : ℕ ↦ hittingAfter X {x | (n : ℝ) ≤ |x|} 0 ω) atTop (𝓝 ⊤) := by
  rw [WithTop.tendsto_nhds_top_iff]
  intro T
  obtain ⟨t, _, hmax⟩ := isCompact_Icc.exists_isMaxOn
    (nonempty_Icc.mpr (bot_le : (0 : ℝ≥0) ≤ T)) hc.abs.continuousOn
  obtain ⟨N, hN⟩ := exists_nat_gt |X t ω|
  filter_upwards [eventually_ge_atTop N] with n hn
  apply lt_of_not_ge
  intro hle
  obtain ⟨u, hu, hm⟩ := (_root_.Prove2MeSourceProof.h_8060b70dbd7753b7696a7230 hc
    (isClosed_le continuous_const continuous_abs)).mp hle
  exact (not_le.mpr hN) ((Nat.cast_le.mpr hn).trans (hm.trans (hmax hu)))
end MeasureTheory


