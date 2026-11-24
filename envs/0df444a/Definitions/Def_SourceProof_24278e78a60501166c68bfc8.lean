-- Prove2me | Definitions.Def_SourceProof_24278e78a60501166c68bfc8
-- name    : SourceProof_24278e78a60501166c68bfc8
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-24T23:00:42.732208+00:00
-- url     : https://prove2.me/theorems/78a144ca-2f3f-48ab-bed4-252e292ab7f1
-- title:
--   StochLean source theorem: ProbabilityTheory.TendstoUCP.smul

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
theorem _root_.Prove2MeSourceProof.h_24278e78a60501166c68bfc8 (h : TendstoUCP P X l Y) (c : ℝ) :
    TendstoUCP P (fun i ↦ c • X i) l (c • Y) := by
  apply _root_.Prove2MeSourceProof.h_c85f5070e7769bac711d7f66.mpr
  intro T ε hε
  have hd : 0 < ε / (‖c‖ + 1) := div_pos hε (by positivity)
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds
    (_root_.Prove2MeSourceProof.h_c85f5070e7769bac711d7f66.mp h T _ hd) (fun _ ↦ bot_le)
  intro i
  apply measure_mono
  rintro ω ⟨t, ht, hω⟩
  refine ⟨t, ht, ?_⟩
  change ε < ‖c • X i t ω - c • Y t ω‖ at hω
  rw [← smul_sub, norm_smul] at hω
  by_contra hn
  have hn := le_of_not_gt hn
  have hb := mul_le_mul_of_nonneg_left hn (norm_nonneg c)
  have heq : ε / (‖c‖ + 1) * (‖c‖ + 1) = ε := div_mul_cancel₀ ε (by positivity)
  nlinarith
end TendstoUCP

end ProbabilityTheory


