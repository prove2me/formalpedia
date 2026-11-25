-- Prove2me | Definitions.Def_SourceProof_fb98cafaf4269dae3b77bad4
-- name    : SourceProof_fb98cafaf4269dae3b77bad4
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-25T14:33:37.275045+00:00
-- url     : https://prove2.me/theorems/5dc78ba6-7865-47ce-983d-b00ac7d30428
-- title:
--   StochLean source theorem: ProbabilityTheory.IsCadlagPath.finite_large_jumps_Ioc

import Definitions.Def_SourceProof_1801c6c77d95e21c42f22870
import Definitions.Def_SourceProof_186a2772edad25f4bcf59290
import Mathlib.Data.Finset.Max

/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/

/-! # Actual large jumps of cadlag paths are locally finite

A compact cadlag path has only finitely many positive-time jumps larger than
any fixed positive threshold. The proof first finds finitely many oscillation
separators, then proves that every large jump is among them. The separators
are not asserted to be jumps themselves.

The finite set also supplies an actual earliest large jump after a given
finite time, whenever any such jump exists. These are pathwise assertions;
no measurability or stopping-time property of the earliest jump is claimed.
The initial source jump is deliberately excluded.
-/

@[expose] public section

open Filter Set Metric
open scoped NNReal Topology

namespace ProbabilityTheory

variable {Ω : Type*} {X : ℝ≥0 → Ω → ℝ} {ω : Ω}

namespace IsCadlagPath
theorem _root_.Prove2MeSourceProof.h_fb98cafaf4269dae3b77bad4 (hX : IsCadlagPath (X · ω))
    (T : ℝ≥0) {b : ℝ} (hb : 0 < b) :
    {t : ℝ≥0 | 0 < t ∧ t ≤ T ∧ b < ‖jumpProcess X t ω‖}.Finite := by
  classical
  obtain ⟨A, _, δ, hδ, hosc⟩ := (_root_.Prove2MeSourceProof.h_1801c6c77d95e21c42f22870 hX) T hb
  apply A.finite_toSet.subset
  rintro t ⟨ht, htT, hj⟩
  by_contra htA
  have havoid : ∀ᶠ s in 𝓝[<] t, ∀ a ∈ A, a ∉ Ioc s t := by
    apply A.eventually_all.mpr
    intro a ha
    by_cases hat : a ≤ t
    · have halt : a < t := lt_of_le_of_ne hat (fun he ↦ htA (he ▸ ha))
      filter_upwards [nhdsWithin_le_nhds (Ioi_mem_nhds halt)] with s hs
      exact fun hmem ↦ (not_lt_of_ge (show a ≤ s from (show a < s from hs).le)) hmem.1
    · exact Eventually.of_forall fun s hmem ↦ hat hmem.2
  have hd : ∀ᶠ s in 𝓝[<] t, dist s t < δ :=
    nhdsWithin_le_nhds (Metric.ball_mem_nhds t hδ)
  have hbound : ∀ᶠ s in 𝓝[<] t, ‖X t ω - X s ω‖ ≤ b := by
    filter_upwards [havoid, hd, self_mem_nhdsWithin] with s hs hst hlt
    have hsle : s ≤ t := (show s < t from hlt).le
    have h := hosc s ⟨bot_le, hsle.trans htT⟩ t ⟨bot_le, htT⟩ hsle hst hs
    simpa only [dist_eq_norm, norm_sub_rev] using h.le
  let : (𝓝[<] t).NeBot := nhdsLT_neBot_of_exists_lt ⟨0, ht⟩
  have hlim : Tendsto (fun s ↦ ‖X t ω - X s ω‖) (𝓝[<] t)
      (𝓝 ‖X t ω - ProbabilityTheory.leftLimitProcess X t ω‖) :=
    (tendsto_const_nhds.sub ((_root_.Prove2MeSourceProof.h_186a2772edad25f4bcf59290 hX) ht.ne')).norm
  have hle : ‖ProbabilityTheory.jumpProcess X t ω‖ ≤ b := le_of_tendsto hlim hbound
  exact (not_le_of_gt hj) hle
end IsCadlagPath

end ProbabilityTheory


