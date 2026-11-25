-- Prove2me | Definitions.Def_SourceProof_541913de150c81e147df976a
-- name    : SourceProof_541913de150c81e147df976a
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-25T14:34:10.190731+00:00
-- url     : https://prove2.me/theorems/7a67f89d-d445-46da-9ba1-e23e7d677623
-- title:
--   StochLean source theorem: MeasureTheory.Adapted.isStoppingTime_hittingAfter_abs

import Definitions.Def_StochLean_Probability_Process_Path_Supremum_F000
import Definitions.Def_StochLean_Probability_Process_Path_Supremum_F001
import Definitions.Def_SourceProof_3db4205103ad8412e26caea6
import Definitions.Def_SourceProof_8060b70dbd7753b7696a7230
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

end ProbabilityTheory

namespace MeasureTheory

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {F : Filtration ℝ≥0 mΩ}
  {X : ℝ≥0 → Ω → ℝ}

namespace Adapted

theorem _root_.Prove2MeSourceProof.h_541913de150c81e147df976a (hX : Adapted F X)
    (hc : ∀ ω, Continuous (X · ω)) (a : ℝ) :
    IsStoppingTime F (hittingAfter X {x | a ≤ |x|} 0) := by
  intro T
  have hs : IsClosed {x : ℝ | a ≤ |x|} := isClosed_le continuous_const continuous_abs
  have heq : {ω | hittingAfter X {x | a ≤ |x|} 0 ω ≤ T} =
      {ω | ENNReal.ofReal a ≤
        ProbabilityTheory.denseRunningSupremum (fun t ω ↦ |X t ω|) T ω} := by
    ext ω
    rw [mem_ofPred_eq, _root_.Prove2MeSourceProof.h_8060b70dbd7753b7696a7230 (hc ω) hs,
      mem_ofPred_eq, _root_.Prove2MeSourceProof.h_3db4205103ad8412e26caea6
        (hc ω).abs (fun t ↦ abs_nonneg (X t ω))]
    simp only [mem_Icc, mem_ofPred_eq, zero_le, true_and]
  rw [heq]
  apply measurableSet_le measurable_const
  apply Measurable.iSup
  intro n
  exact ENNReal.measurable_ofReal.comp (continuous_abs.measurable.comp
    ((hX (ProbabilityTheory.denseTimeUpTo T n)).mono (F.mono (min_le_left _ _)) le_rfl))
end Adapted

end MeasureTheory


