-- Prove2me | Definitions.Def_SourceProof_b74f6a65e2b4b7aa5b730057
-- name    : SourceProof_b74f6a65e2b4b7aa5b730057
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-25T08:00:04.162346+00:00
-- url     : https://prove2.me/theorems/396bf59a-18bb-47a9-9317-0528d85dde6f
-- title:
--   StochLean source theorem: MeasureTheory.abs_le_of_le_hittingAfter

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

end MeasureTheory

namespace ProbabilityTheory

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {X : ℝ≥0 → Ω → ℝ}

end ProbabilityTheory

namespace MeasureTheory

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {F : Filtration ℝ≥0 mΩ}
  {X : ℝ≥0 → Ω → ℝ}


theorem _root_.Prove2MeSourceProof.h_b74f6a65e2b4b7aa5b730057 {a : ℝ} {ω : Ω} (hc : Continuous (X · ω))
    (hzero : |X 0 ω| ≤ a) {t : ℝ≥0}
    (ht : (t : WithTop ℝ≥0) ≤ hittingAfter X {x | a ≤ |x|} 0 ω) : |X t ω| ≤ a := by
  by_cases hz : t = 0
  · simpa only [hz] using hzero
  have hpos : 0 < t := bot_lt_iff_ne_bot.mpr hz
  have hcl : t ∈ closure (Iio t) := by
    rw [closure_Iio' (a := t) ⟨(0 : ℝ≥0), hpos⟩]
    exact mem_Iic.mpr (le_refl t)
  apply closure_minimal (s := Iio t) (t := {u | |X u ω| ≤ a}) ?_
    (isClosed_le hc.abs continuous_const) hcl
  intro u hu
  change |X u ω| ≤ a
  exact (lt_of_not_ge (notMem_of_lt_hittingAfter (u := X) (s := {x | a ≤ |x|})
    ((WithTop.coe_lt_coe.mpr hu).trans_le ht) bot_le)).le
end MeasureTheory


