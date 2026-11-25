-- Prove2me | Definitions.Def_SourceProof_bdc7d79620058d0bf6b1336e
-- name    : SourceProof_bdc7d79620058d0bf6b1336e
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-25T12:39:06.770135+00:00
-- url     : https://prove2.me/theorems/447f8590-f774-585b-a693-a0191aa3ed4a
-- title:
--   StochLean source theorem: ProbabilityTheory.norm_leftLimit_sub_le_of_oscillation_interval

import Definitions.Def_StochLean_Probability_Process_Stopping_Oscillation_F000
import Definitions.Def_SourceProof_186a2772edad25f4bcf59290
import Definitions.Def_SourceProof_1e52c15149bd45e1ab3198d1
import Definitions.Def_SourceProof_60e710b522febb5ad2df8d23

/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/

/-! # Recursive oscillation stopping times

The next time is the existing first hit of `X - X^tau`, so it never evaluates an
unprovided value `X_infinity`. For a positive threshold, finite successive times
are strictly separated and their sampled values differ by at least the threshold.
Cadlag paths therefore force the actual recursive times to tend to infinity.
-/

@[expose] public section

open MeasureTheory Filter Set
open scoped NNReal Topology

namespace ProbabilityTheory

variable {Ω : Type*} {X : ℝ≥0 → Ω → ℝ}


theorem _root_.Prove2MeSourceProof.h_bdc7d79620058d0bf6b1336e (τ : Ω → WithTop ℝ≥0)
    {ω : Ω} (hX : IsCadlagPath (X · ω)) {ε : ℝ} {t : ℝ≥0}
    (hτt : τ ω < (t : WithTop ℝ≥0)) (htR : (t : WithTop ℝ≥0) ≤ nextOscillationTime X ε τ ω) :
    ‖leftLimitProcess X t ω - X (τ ω).untopA ω‖ ≤ ε := by
  have hne : τ ω ≠ ⊤ := ne_top_of_le_ne_top WithTop.coe_ne_top hτt.le
  have hcoe : ((τ ω).untopA : WithTop ℝ≥0) = τ ω := by
    rw [WithTop.untopA_eq_untop hne, WithTop.coe_untop]
  have hleft : (τ ω).untopA < t := WithTop.coe_lt_coe.mp (by rw [hcoe]; exact hτt)
  have ht0 : (0 : ℝ≥0) < t := (bot_le : (0 : ℝ≥0) ≤ (τ ω).untopA).trans_lt hleft
  let : (𝓝[<] t).NeBot := nhdsLT_neBot_of_exists_lt ⟨0, ht0⟩
  have hlim : Tendsto (fun s ↦ ‖X s ω - X (τ ω).untopA ω‖) (𝓝[<] t)
      (𝓝 ‖ProbabilityTheory.leftLimitProcess X t ω - X (τ ω).untopA ω‖) :=
    (((_root_.Prove2MeSourceProof.h_186a2772edad25f4bcf59290 hX) (ne_of_gt ht0)).sub tendsto_const_nhds).norm
  apply le_of_tendsto hlim
  filter_upwards [Ioo_mem_nhdsLT hleft] with s hs
  have hbefore := _root_.Prove2MeSourceProof.h_1e52c15149bd45e1ab3198d1 (X := X - stoppedProcess X τ)
    ((WithTop.coe_lt_coe.mpr hs.2).trans_le htR)
  change ‖X s ω - stoppedProcess X τ s ω‖ ≤ ε at hbefore
  have hτs : τ ω ≤ (s : WithTop ℝ≥0) := by
    rw [← hcoe]
    exact WithTop.coe_le_coe.mpr hs.1.le
  rwa [stoppedProcess_eq_of_ge hτs] at hbefore
variable {mΩ : MeasurableSpace Ω} {F : Filtration ℝ≥0 mΩ} {P : Measure Ω}

end ProbabilityTheory


