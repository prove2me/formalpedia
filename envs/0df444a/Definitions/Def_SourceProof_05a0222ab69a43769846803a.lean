-- Prove2me | Definitions.Def_SourceProof_05a0222ab69a43769846803a
-- name    : SourceProof_05a0222ab69a43769846803a
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-24T23:20:04.669604+00:00
-- url     : https://prove2.me/theorems/67227a4e-9e63-4d0e-a586-73ed6730f53e
-- title:
--   StochLean source theorem: ProbabilityTheory.compactDeviation_rightLimitProcess_le

import Definitions.Def_SourceProof_1ba1a2c21f7033732d51d48a
import Definitions.Def_SourceProof_845eb3d5bff7aa74f6afa784
import Definitions.Def_SourceProof_a307e422895411519841ce97
import Definitions.Def_SourceProof_a3bc82106adf606a13e0e393

/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/

/-! # Right-limit transformation is continuous in UCP on caglad paths

A slightly larger input horizon controls the right limit at the target horizon.
The transformation need not preserve the original initial value or give a
modification. Its continuity is proved by pathwise deviation comparison.
-/

@[expose] public section

open MeasureTheory Filter Set
open scoped NNReal ENNReal Topology

namespace ProbabilityTheory

variable {Ω ι : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} {l : Filter ι}
  {X Y : ℝ≥0 → Ω → ℝ}

theorem _root_.Prove2MeSourceProof.h_05a0222ab69a43769846803a {ω : Ω}
    (hX : IsCagladPath (X · ω)) (hY : IsCagladPath (Y · ω)) (T : ℝ≥0) :
    compactDeviation (rightLimitProcess X) (rightLimitProcess Y) T ω ≤
      compactDeviation X Y (T + 1) ω := by
  apply iSup_le
  intro t
  apply iSup_le
  intro ht
  apply le_of_tendsto (ENNReal.continuous_ofReal.continuousAt.tendsto.comp
    (((_root_.Prove2MeSourceProof.h_1ba1a2c21f7033732d51d48a hX) t).sub ((_root_.Prove2MeSourceProof.h_1ba1a2c21f7033732d51d48a hY) t)).norm)
  filter_upwards [(eventually_lt_nhds (ht.trans_lt (lt_add_one T))).filter_mono
    nhdsWithin_le_nhds] with u hu
  exact _root_.Prove2MeSourceProof.h_845eb3d5bff7aa74f6afa784 hu.le ω
end ProbabilityTheory


