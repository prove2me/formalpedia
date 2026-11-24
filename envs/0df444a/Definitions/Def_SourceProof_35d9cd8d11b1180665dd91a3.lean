-- Prove2me | Definitions.Def_SourceProof_35d9cd8d11b1180665dd91a3
-- name    : SourceProof_35d9cd8d11b1180665dd91a3
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-24T23:21:11.927151+00:00
-- url     : https://prove2.me/theorems/c35f7b1a-ad70-4cc9-94d1-61e91828210b
-- title:
--   StochLean source theorem: ProbabilityTheory.compactDeviation_mul_right_le

import Definitions.Def_StochLean_Probability_Process_UCP_F000
import Definitions.Def_SourceProof_845eb3d5bff7aa74f6afa784
import Mathlib.Analysis.Normed.Group.Continuity
import Mathlib.MeasureTheory.Integral.Indicator
import Mathlib.Order.Filter.AtTopBot.CountablyGenerated
import Mathlib.Topology.Algebra.Monoid
import Mathlib.Topology.Compactness.Compact

/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/

/-! # UCP multiplication by a fixed caglad process

The multiplier need only be pathwise bounded on compact intervals, not bounded
uniformly in the sample point or integrable. Countable dense deviations provide
the needed measurability, including an independent initial value.
-/

@[expose] public section

open MeasureTheory Filter Set
open scoped NNReal ENNReal Topology

namespace ProbabilityTheory

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω}
  {X Y H : ℝ≥0 → Ω → ℝ}

theorem _root_.Prove2MeSourceProof.h_35d9cd8d11b1180665dd91a3 {T : ℝ≥0} {ω : Ω} {C : ℝ}
    (hC : ∀ t ≤ T, ‖H t ω‖ ≤ C) :
    compactDeviation (X * H) (Y * H) T ω ≤
      compactDeviation X Y T ω * ENNReal.ofReal C := by
  apply iSup_le
  intro t
  apply iSup_le
  intro ht
  change ENNReal.ofReal ‖X t ω * H t ω - Y t ω * H t ω‖ ≤ _
  rw [← sub_mul, norm_mul, ENNReal.ofReal_mul (norm_nonneg _)]
  exact mul_le_mul' (_root_.Prove2MeSourceProof.h_845eb3d5bff7aa74f6afa784 ht ω) (ENNReal.ofReal_le_ofReal (hC t ht))
end ProbabilityTheory


