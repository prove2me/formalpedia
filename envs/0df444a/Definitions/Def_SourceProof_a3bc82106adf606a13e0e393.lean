-- Prove2me | Definitions.Def_SourceProof_a3bc82106adf606a13e0e393
-- name    : SourceProof_a3bc82106adf606a13e0e393
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-24T23:13:35.364013+00:00
-- url     : https://prove2.me/theorems/22a0e7fd-82cc-441b-9795-5801d0c1e742
-- title:
--   StochLean source theorem: ProbabilityTheory.Indistinguishable.rightLimitProcess

import Definitions.Def_StochLean_Probability_Process_Path_RightLimit_F000

/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/

/-! # The right-limit process of a caglad input

Mathlib owns the strict-right-limit selector. Its limit and reconstruction identities
are proved on the caglad path domain. In general `H_(0+)` differs from `H_0`, so this
transformation is not a modification and does not normalize or overwrite the source initial value.
-/

@[expose] public section

open MeasureTheory Filter Set
open scoped NNReal Topology

namespace ProbabilityTheory

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω}
  {X Y : ℝ≥0 → Ω → ℝ}

namespace Indistinguishable
theorem _root_.Prove2MeSourceProof.h_a3bc82106adf606a13e0e393 (hXY : Indistinguishable X Y P) :
    Indistinguishable (rightLimitProcess X) (rightLimitProcess Y) P := by
  filter_upwards [hXY] with ω hω t
  simp only [ProbabilityTheory.rightLimitProcess, hω]
end Indistinguishable

end ProbabilityTheory


