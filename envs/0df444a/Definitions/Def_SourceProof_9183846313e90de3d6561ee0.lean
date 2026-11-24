-- Prove2me | Definitions.Def_SourceProof_9183846313e90de3d6561ee0
-- name    : SourceProof_9183846313e90de3d6561ee0
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-24T22:15:27.812402+00:00
-- url     : https://prove2.me/theorems/df90615a-a30e-4707-a027-530efd3754de
-- title:
--   StochLean source theorem: ProbabilityTheory.tendsto_compactDeviation_iff_tendstoUniformlyOn

import Definitions.Def_StochLean_Probability_Process_UCP_F001
import Definitions.Def_SourceProof_845eb3d5bff7aa74f6afa784
import Mathlib.MeasureTheory.Integral.Indicator
import Mathlib.Order.Filter.AtTopBot.CountablyGenerated

/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/

/-! # Uniform path convergence and a subsequence criterion for UCP

Measurability of the output compact deviations is explicit in the converse.
No continuity of an outer measure on arbitrary decreasing sets is used.
-/

@[expose] public section

open MeasureTheory Filter Set
open scoped NNReal ENNReal Topology

namespace ProbabilityTheory

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω}

theorem _root_.Prove2MeSourceProof.h_9183846313e90de3d6561ee0 {ι : Type*} {l : Filter ι}
    {X : ι → ℝ≥0 → Ω → ℝ} {Y : ℝ≥0 → Ω → ℝ} {T : ℝ≥0} {ω : Ω} :
    Tendsto (fun i ↦ compactDeviation (X i) Y T ω) l (𝓝 0) ↔
      TendstoUniformlyOn (fun i t ↦ X i t ω) (fun t ↦ Y t ω) l (Icc 0 T) := by
  constructor
  · intro h
    apply EMetric.tendstoUniformlyOn_iff.mpr
    intro ε hε
    filter_upwards [h.eventually_lt_const hε] with i hi
    intro t ht
    rw [edist_comm, edist_dist, dist_eq_norm_sub]
    exact (_root_.Prove2MeSourceProof.h_845eb3d5bff7aa74f6afa784 ht.2 ω).trans_lt hi
  · intro h
    apply ENNReal.tendsto_nhds_zero.mpr
    intro ε hε
    filter_upwards [EMetric.tendstoUniformlyOn_iff.mp h ε hε] with i hi
    apply iSup_le
    intro t
    apply iSup_le
    intro ht
    have hh := (hi t ⟨bot_le, ht⟩).le
    simpa only [edist_dist, dist_eq_norm_sub, norm_sub_rev] using hh
end ProbabilityTheory


