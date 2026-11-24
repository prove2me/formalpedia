-- Prove2me | Definitions.Def_SourceProof_c55d17120c217e6f4e472165
-- name    : SourceProof_c55d17120c217e6f4e472165
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-24T23:01:29.140296+00:00
-- url     : https://prove2.me/theorems/e7715ab1-f473-4ffb-82f8-bf142c66cb2a
-- title:
--   StochLean source theorem: ProbabilityTheory.TendstoUCP.add

import Definitions.Def_StochLean_Probability_Process_UCP_F001
import Definitions.Def_SourceProof_c85f5070e7769bac711d7f66

/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/

/-! # Linear operations and indistinguishable changes in UCP

These statements use the canonical UCP owner and outer-measure event bounds.
No additional path measurability or regularity assumptions are necessary.
-/

@[expose] public section

open MeasureTheory Filter Set
open scoped NNReal ENNReal Topology

namespace ProbabilityTheory

variable {Ω ι : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} {l : Filter ι}
  {X Z : ι → ℝ≥0 → Ω → ℝ} {Y W : ℝ≥0 → Ω → ℝ}

namespace TendstoUCP
theorem _root_.Prove2MeSourceProof.h_c55d17120c217e6f4e472165 (hX : TendstoUCP P X l Y) (hZ : TendstoUCP P Z l W) :
    TendstoUCP P (fun i ↦ X i + Z i) l (Y + W) := by
  apply _root_.Prove2MeSourceProof.h_c85f5070e7769bac711d7f66.mpr
  intro T ε hε
  have hsum := (_root_.Prove2MeSourceProof.h_c85f5070e7769bac711d7f66.mp hX T (ε / 2) (half_pos hε)).add
    (_root_.Prove2MeSourceProof.h_c85f5070e7769bac711d7f66.mp hZ T (ε / 2) (half_pos hε))
  rw [zero_add] at hsum
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hsum (fun _ ↦ bot_le)
  intro i
  apply (measure_mono (t := {ω | ∃ t ≤ T, ε / 2 < ‖X i t ω - Y t ω‖} ∪
    {ω | ∃ t ≤ T, ε / 2 < ‖Z i t ω - W t ω‖}) ?_).trans (measure_union_le _ _)
  rintro ω ⟨t, ht, hω⟩
  by_cases hXY : ε / 2 < ‖X i t ω - Y t ω‖
  · exact Or.inl ⟨t, ht, hXY⟩
  · refine Or.inr ⟨t, ht, ?_⟩
    change ε < ‖X i t ω + Z i t ω - (Y t ω + W t ω)‖ at hω
    rw [show X i t ω + Z i t ω - (Y t ω + W t ω) =
      (X i t ω - Y t ω) + (Z i t ω - W t ω) by ring] at hω
    have hb := norm_add_le (X i t ω - Y t ω) (Z i t ω - W t ω)
    have hXY := le_of_not_gt hXY
    linarith
end TendstoUCP

end ProbabilityTheory


