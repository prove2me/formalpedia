-- Prove2me | Definitions.Def_SourceProof_3db4205103ad8412e26caea6
-- name    : SourceProof_3db4205103ad8412e26caea6
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-25T12:44:47.443953+00:00
-- url     : https://prove2.me/theorems/f1fc1efc-ec2a-484e-a741-a803e9c06b7d
-- title:
--   StochLean source theorem: ProbabilityTheory.le_denseRunningSupremum_iff_exists_of_continuous

import Definitions.Def_StochLean_Probability_Process_Path_Supremum_F000
import Definitions.Def_StochLean_Probability_Process_Path_Supremum_F001
import Definitions.Def_SourceProof_0d990b6d42af60e405064fad
import Mathlib.Probability.Process.HittingTime
import Mathlib.Topology.Order.Compact

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


theorem _root_.Prove2MeSourceProof.h_3db4205103ad8412e26caea6
    {T : ℝ≥0} {a : ℝ} {ω : Ω} (hX : Continuous (X · ω))
    (hpos : ∀ t, 0 ≤ X t ω) :
    ENNReal.ofReal a ≤ denseRunningSupremum X T ω ↔ ∃ t ≤ T, a ≤ X t ω := by
  obtain ⟨t, ht, hmax⟩ := isCompact_Icc.exists_isMaxOn
    (nonempty_Icc.mpr (bot_le : (0 : ℝ≥0) ≤ T)) hX.continuousOn
  have heq : ProbabilityTheory.denseRunningSupremum X T ω = ENNReal.ofReal (X t ω) := by
    apply le_antisymm
    · apply iSup_le
      intro n
      exact ENNReal.ofReal_le_ofReal (hmax ⟨bot_le, min_le_left _ _⟩)
    · exact _root_.Prove2MeSourceProof.h_0d990b6d42af60e405064fad ht.2
        (fun _ ↦ hX.continuousWithinAt)
  rw [heq]
  constructor
  · intro h
    exact ⟨t, ht.2, (ENNReal.ofReal_le_ofReal_iff (hpos t)).mp h⟩
  · rintro ⟨u, hu, ha⟩
    exact ENNReal.ofReal_le_ofReal (ha.trans (hmax ⟨bot_le, hu⟩))
end ProbabilityTheory

namespace MeasureTheory

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {F : Filtration ℝ≥0 mΩ}
  {X : ℝ≥0 → Ω → ℝ}

end MeasureTheory


