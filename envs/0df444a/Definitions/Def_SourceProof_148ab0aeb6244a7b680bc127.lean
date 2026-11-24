-- Prove2me | Definitions.Def_SourceProof_148ab0aeb6244a7b680bc127
-- name    : SourceProof_148ab0aeb6244a7b680bc127
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-24T23:20:03.180901+00:00
-- url     : https://prove2.me/theorems/36ad3012-dab4-4a33-a948-4bb46bc716f1
-- title:
--   StochLean source theorem: ProbabilityTheory.compactDeviation_comp_nonexpansive_le

import Definitions.Def_StochLean_Probability_Process_UCP_F001
import Definitions.Def_SourceProof_845eb3d5bff7aa74f6afa784
import Mathlib.Topology.MetricSpace.Lipschitz

/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/

/-! # Nonexpansive scalar maps act continuously in UCP

The event comparison works for outer measures; no path measurability or
finite-measure premise is imposed.
-/

@[expose] public section

open MeasureTheory Filter
open scoped NNReal ENNReal Topology

namespace ProbabilityTheory

variable {Ω ι : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} {l : Filter ι}
  {X Y : ℝ≥0 → Ω → ℝ}

theorem _root_.Prove2MeSourceProof.h_148ab0aeb6244a7b680bc127 {f : ℝ → ℝ} (hf : LipschitzWith 1 f)
    (T : ℝ≥0) (ω : Ω) :
    compactDeviation (fun t ω ↦ f (X t ω)) (fun t ω ↦ f (Y t ω)) T ω ≤
      compactDeviation X Y T ω := by
  apply iSup_le
  intro t
  apply iSup_le
  intro ht
  have hb : ‖f (X t ω) - f (Y t ω)‖ ≤ ‖X t ω - Y t ω‖ := by
    simpa only [dist_eq_norm_sub, NNReal.coe_one, one_mul] using hf.dist_le_mul (X t ω) (Y t ω)
  exact (ENNReal.ofReal_le_ofReal hb).trans (_root_.Prove2MeSourceProof.h_845eb3d5bff7aa74f6afa784 ht ω)
end ProbabilityTheory


