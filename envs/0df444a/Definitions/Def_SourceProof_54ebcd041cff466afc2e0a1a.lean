-- Prove2me | Definitions.Def_SourceProof_54ebcd041cff466afc2e0a1a
-- name    : SourceProof_54ebcd041cff466afc2e0a1a
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-24T23:27:11.263799+00:00
-- url     : https://prove2.me/theorems/c23519ad-f218-49b6-bc6a-84fd7e199f2d
-- title:
--   StochLean source theorem: MeasureTheory.hittingAfter_abs_mono

import Definitions.Def_StochLean_Probability_Process_Path_Supremum_F000
import Definitions.Def_StochLean_Probability_Process_Path_Supremum_F001
import Definitions.Def_SourceProof_30e624a971e34de8e1028e01
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


theorem _root_.Prove2MeSourceProof.h_54ebcd041cff466afc2e0a1a {ω : Ω} (hc : Continuous (X · ω)) :
    Monotone (fun a : ℝ ↦ hittingAfter X {x | a ≤ |x|} 0 ω) := by
  intro a b hab
  change hittingAfter X {x | a ≤ |x|} 0 ω ≤ hittingAfter X {x | b ≤ |x|} 0 ω
  by_cases hb : hittingAfter X {x | b ≤ |x|} 0 ω = ⊤
  · rw [hb]
    exact le_top
  have hm := _root_.Prove2MeSourceProof.h_30e624a971e34de8e1028e01 hc
    (isClosed_le continuous_const continuous_abs) hb
  have hle := hittingAfter_le_of_mem (u := X) (s := {x | a ≤ |x|}) bot_le (hab.trans hm)
  rwa [WithTop.untopA_eq_untop hb, WithTop.coe_untop] at hle
end MeasureTheory


