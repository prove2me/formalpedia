-- Prove2me | Definitions.Def_SourceProof_eff9df1f090a05dc4bbe1884
-- name    : SourceProof_eff9df1f090a05dc4bbe1884
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-25T17:45:56.829183+00:00
-- url     : https://prove2.me/theorems/786e189f-3ec2-5a22-9970-955a384a7f74
-- title:
--   StochLean source theorem: MeasureTheory.Adapted.rightLimitProcess_of_rightLimits

import Definitions.Def_StochLean_Probability_Process_Filtration_Usual_F001
import Definitions.Def_StochLean_Probability_Process_Path_RightLimit_F000
import Definitions.Def_SourceProof_a3bc82106adf606a13e0e393
import Mathlib.MeasureTheory.Constructions.Polish.Basic
import Mathlib.Probability.Process.Adapted

/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/

/-! # Adaptedness of a caglad process's right-limit process

The right limit at `t` is measurable in every `F_u`, `u > t`, by actual sequences
inside `(t,u)`. Right continuity of the filtration then gives `F_t` measurability.
Usual completeness transports the statement on one common exceptional path event.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal Topology

namespace MeasureTheory

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {F : Filtration ℝ≥0 mΩ}
  {X : ℝ≥0 → Ω → ℝ} {P : Measure Ω}

namespace Adapted
theorem _root_.Prove2MeSourceProof.h_eff9df1f090a05dc4bbe1884 [F.IsRightContinuous]
    (ha : Adapted F X)
    (hr : ∀ ω t, ∃ y : ℝ, Tendsto (X · ω) (𝓝[>] t) (𝓝 y)) :
    Adapted F (ProbabilityTheory.rightLimitProcess X) := by
  intro t
  have hu (u : ℝ≥0) (htu : t < u) : Measurable[F u] (ProbabilityTheory.rightLimitProcess X t) := by
    obtain ⟨v, _, hv, hlim⟩ := exists_seq_strictAnti_tendsto' htu
    have hvlim : Tendsto v atTop (𝓝[>] t) :=
      tendsto_nhdsWithin_iff.mpr ⟨hlim, Eventually.of_forall fun n ↦ (hv n).1⟩
    let : MeasurableSpace Ω := F u
    change Measurable (fun ω ↦ ProbabilityTheory.rightLimitProcess X t ω)
    exact measurable_of_tendsto_metrizable
      (fun n ↦ (ha (v n)).mono (F.mono (hv n).2.le) le_rfl)
      (tendsto_pi_nhds.mpr fun ω ↦ (tendsto_rightLim_of_tendsto (hr ω t)).comp hvlim)
  intro s hs
  apply Filtration.IsRightContinuous.measurableSet (𝓕 := F)
  rw [F.rightCont_eq]
  exact MeasurableSpace.measurableSet_iInf.mpr fun u ↦
    MeasurableSpace.measurableSet_iInf.mpr fun htu ↦ hu u htu hs
end Adapted

end MeasureTheory


