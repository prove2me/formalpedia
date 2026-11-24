-- Prove2me | Definitions.Def_SourceProof_c85f5070e7769bac711d7f66
-- name    : SourceProof_c85f5070e7769bac711d7f66
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-24T22:15:07.153572+00:00
-- url     : https://prove2.me/theorems/815caa41-d766-46a3-8c11-718e6eb9f864
-- title:
--   StochLean source theorem: ProbabilityTheory.tendstoUCP_iff_measure_exists_norm_lt

import Definitions.Def_StochLean_Probability_Process_UCP_F001
import Definitions.Def_SourceProof_845eb3d5bff7aa74f6afa784

/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/

/-! # Strict real-threshold event characterization of UCP

Strict exceedance events avoid assuming that a compact maximum is attained.
The comparison with the canonical extended compact deviation is order-theoretic;
it needs neither path regularity nor measurability of an uncountable supremum.
-/

@[expose] public section

open MeasureTheory Filter Set
open scoped NNReal ENNReal Topology

namespace ProbabilityTheory

variable {Ω ι : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω}
  {X : ι → ℝ≥0 → Ω → ℝ} {Y : ℝ≥0 → Ω → ℝ} {l : Filter ι}

theorem _root_.Prove2MeSourceProof.h_c85f5070e7769bac711d7f66 :
    TendstoUCP P X l Y ↔ ∀ T : ℝ≥0, ∀ ε : ℝ, 0 < ε →
      Tendsto (fun i ↦ P {ω | ∃ t ≤ T, ε < ‖X i t ω - Y t ω‖}) l (𝓝 0) := by
  constructor
  · intro h T ε hε
    apply tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds
      (h T (ENNReal.ofReal ε) (ENNReal.ofReal_pos.mpr hε)) (fun _ ↦ bot_le)
    intro i
    apply measure_mono
    rintro ω ⟨t, ht, hω⟩
    exact (ENNReal.ofReal_le_ofReal hω.le).trans (_root_.Prove2MeSourceProof.h_845eb3d5bff7aa74f6afa784 ht ω)
  · intro h T ε hε
    obtain ⟨r, hr0, hrε⟩ := ENNReal.lt_iff_exists_nnreal_btwn.mp hε
    have hr : 0 < (r : ℝ) := by exact_mod_cast hr0
    apply tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds
      (h T r hr) (fun _ ↦ bot_le)
    intro i
    apply measure_mono
    intro ω hω
    have hlt : (r : ℝ≥0∞) < ProbabilityTheory.compactDeviation (X i) Y T ω := hrε.trans_le hω
    simp only [ProbabilityTheory.compactDeviation, lt_iSup_iff] at hlt
    obtain ⟨t, ht, htr⟩ := hlt
    refine ⟨t, ht, ?_⟩
    by_contra hn
    have hle := ENNReal.ofReal_le_ofReal (le_of_not_gt hn)
    exact (not_le_of_gt htr) (by simpa using hle)
end ProbabilityTheory


