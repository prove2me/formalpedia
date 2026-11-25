-- Prove2me | Definitions.Def_SourceProof_6fe8e798f5fa5227db6c7521
-- name    : SourceProof_6fe8e798f5fa5227db6c7521
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-25T16:34:42.470349+00:00
-- url     : https://prove2.me/theorems/ba55c195-08c7-53a8-9cdd-19bbec4f57eb
-- title:
--   StochLean source theorem: MeasureTheory.Adapted.leftLimitProcess_of_cadlag

import Definitions.Def_StochLean_Probability_Process_Measurability_Progressive_F001
import Definitions.Def_StochLean_Probability_Process_Path_LeftLimit_F000
import Definitions.Def_SourceProof_12d34a5d964556d97aab2788
import Definitions.Def_SourceProof_186a2772edad25f4bcf59290
import Definitions.Def_SourceProof_60e710b522febb5ad2df8d23

/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/

/-! # Adaptedness of the source left-limit and jump processes -/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal Topology

namespace MeasureTheory

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {F : Filtration ℝ≥0 mΩ}
  {X : ℝ≥0 → Ω → ℝ} {P : Measure Ω}

namespace Adapted

theorem _root_.Prove2MeSourceProof.h_6fe8e798f5fa5227db6c7521 (ha : Adapted F X)
    (hc : ∀ ω, IsCadlagPath (fun t ↦ X t ω)) :
    Adapted F (ProbabilityTheory.leftLimitProcess X) := by
  intro t
  by_cases ht : t = 0
  · subst t
    rw [_root_.Prove2MeSourceProof.h_12d34a5d964556d97aab2788]
    exact measurable_const
  obtain ⟨u, _, hu, hlim⟩ := exists_seq_strictMono_tendsto' (pos_iff_ne_zero.mpr ht)
  have hlu : Tendsto u atTop (𝓝[<] t) :=
    tendsto_nhdsWithin_iff.mpr ⟨hlim, Eventually.of_forall (fun n ↦ (hu n).2)⟩
  let : MeasurableSpace Ω := F t
  change Measurable (fun ω ↦ ProbabilityTheory.leftLimitProcess X t ω)
  exact measurable_of_tendsto_metrizable
    (fun n ↦ (ha (u n)).mono (F.mono (hu n).2.le) le_rfl)
    (tendsto_pi_nhds.mpr (fun ω ↦ ((_root_.Prove2MeSourceProof.h_186a2772edad25f4bcf59290 (hc ω)) ht).comp hlu))
end Adapted

end MeasureTheory


