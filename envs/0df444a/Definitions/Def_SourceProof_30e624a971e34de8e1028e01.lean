-- Prove2me | Definitions.Def_SourceProof_30e624a971e34de8e1028e01
-- name    : SourceProof_30e624a971e34de8e1028e01
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-24T21:58:21.16361+00:00
-- url     : https://prove2.me/theorems/4187fdbd-d036-429f-82f8-b09c2ed78a86
-- title:
--   StochLean source theorem: MeasureTheory.hittingAfter_mem_of_continuous

import Definitions.Def_StochLean_Probability_Process_Path_Supremum_F000
import Definitions.Def_StochLean_Probability_Process_Path_Supremum_F001
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

theorem _root_.Prove2MeSourceProof.h_30e624a971e34de8e1028e01 {X : ℝ≥0 → Ω → E} {s : Set E}
    {a : ℝ≥0} {ω : Ω} (hX : Continuous (X · ω)) (hs : IsClosed s)
    (hne : hittingAfter X s a ω ≠ ⊤) :
    X (hittingAfter X s a ω).untopA ω ∈ s := by
  classical
  have hex : ∃ t, a ≤ t ∧ X t ω ∈ s := by
    simpa only [ne_eq, hittingAfter_eq_top_iff, not_forall, not_not, exists_prop] using hne
  have hc : IsClosed {t : ℝ≥0 | a ≤ t ∧ X t ω ∈ s} :=
    isClosed_Ici.inter (hs.preimage hX)
  have hm := hc.csInf_mem hex (bddBelow_Ici.inter_of_left)
  rw [hittingAfter, if_pos hex]
  exact hm.2
end MeasureTheory

namespace ProbabilityTheory

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {X : ℝ≥0 → Ω → ℝ}

end ProbabilityTheory

namespace MeasureTheory

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {F : Filtration ℝ≥0 mΩ}
  {X : ℝ≥0 → Ω → ℝ}

end MeasureTheory


