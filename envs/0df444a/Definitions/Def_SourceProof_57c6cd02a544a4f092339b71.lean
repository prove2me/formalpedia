-- Prove2me | Definitions.Def_SourceProof_57c6cd02a544a4f092339b71
-- name    : SourceProof_57c6cd02a544a4f092339b71
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-24T23:27:41.254578+00:00
-- url     : https://prove2.me/theorems/a9ccef9f-9dce-4ef1-8b4e-32fb948ad886
-- title:
--   StochLean source theorem: ProbabilityTheory.TendstoUCP.cutoffIntegrand

import Definitions.Def_StochLean_Probability_Process_Stopping_Integrand_F000
import Definitions.Def_StochLean_Probability_Process_UCP_F001
import Definitions.Def_SourceProof_c85f5070e7769bac711d7f66

/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/

/-! # Stopping and cutting off preserve UCP convergence

The event bounds hold for arbitrary possibly infinite random times, even without
a stopping-time hypothesis. The evaluation time of a stopped process is always finite.
-/

@[expose] public section

open MeasureTheory Filter Set
open scoped NNReal ENNReal Topology

namespace ProbabilityTheory

variable {Ω ι : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} {l : Filter ι}
  {X : ι → ℝ≥0 → Ω → ℝ} {Y : ℝ≥0 → Ω → ℝ}

namespace TendstoUCP
theorem _root_.Prove2MeSourceProof.h_57c6cd02a544a4f092339b71 (h : TendstoUCP P X l Y) (τ : Ω → WithTop ℝ≥0) :
    TendstoUCP P (fun i ↦ cutoffIntegrand (X i) τ) l (cutoffIntegrand Y τ) := by
  apply _root_.Prove2MeSourceProof.h_c85f5070e7769bac711d7f66.mpr
  intro T ε hε
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds
    (_root_.Prove2MeSourceProof.h_c85f5070e7769bac711d7f66.mp h T ε hε) (fun _ ↦ bot_le)
  intro i
  apply measure_mono
  rintro ω ⟨t, ht, hω⟩
  by_cases hτ : (t : WithTop ℝ≥0) ≤ τ ω
  · exact ⟨t, ht, by simpa only [ProbabilityTheory.cutoffIntegrand, if_pos hτ] using hω⟩
  · simp only [ProbabilityTheory.cutoffIntegrand, if_neg hτ, sub_self, norm_zero] at hω
    exact (not_lt_of_ge hε.le hω).elim
end TendstoUCP

end ProbabilityTheory


