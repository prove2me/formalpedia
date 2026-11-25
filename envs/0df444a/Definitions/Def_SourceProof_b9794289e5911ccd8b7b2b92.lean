-- Prove2me | Definitions.Def_SourceProof_b9794289e5911ccd8b7b2b92
-- name    : SourceProof_b9794289e5911ccd8b7b2b92
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-25T08:00:53.496013+00:00
-- url     : https://prove2.me/theorems/52082d88-96f7-4088-a940-414c33fa8867
-- title:
--   StochLean source theorem: ProbabilityTheory.tendstoUCP_of_tendstoUniformly

import Definitions.Def_SourceProof_c85f5070e7769bac711d7f66

/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/

/-! # Uniform input convergence implies UCP convergence -/

@[expose] public section

open MeasureTheory Filter Set
open scoped NNReal ENNReal Topology

namespace ProbabilityTheory

variable {Ω ι : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} {l : Filter ι}
  {X : ι → ℝ≥0 → Ω → ℝ} {Y : ℝ≥0 → Ω → ℝ}

theorem _root_.Prove2MeSourceProof.h_b9794289e5911ccd8b7b2b92
    (hu : TendstoUniformly (fun n (z : ℝ≥0 × Ω) ↦ X n z.1 z.2)
      (fun z ↦ Y z.1 z.2) l) : TendstoUCP P X l Y := by
  apply _root_.Prove2MeSourceProof.h_c85f5070e7769bac711d7f66.mpr
  intro T ε hε
  apply tendsto_const_nhds.congr'
  filter_upwards [Metric.tendstoUniformly_iff.mp hu ε hε] with n hn
  have heq : {ω | ∃ t ≤ T, ε < ‖X n t ω - Y t ω‖} = ∅ := by
    apply Set.eq_empty_iff_forall_notMem.mpr
    rintro ω ⟨t, _, ht⟩
    have hb := hn (t, ω)
    rw [dist_eq_norm_sub, norm_sub_rev] at hb
    exact (not_lt_of_ge hb.le) ht
  rw [heq, measure_empty]
end ProbabilityTheory


