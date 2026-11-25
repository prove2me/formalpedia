-- Prove2me | Definitions.Def_SourceProof_ee0958f607118d8fce16af89
-- name    : SourceProof_ee0958f607118d8fce16af89
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-25T17:41:43.073319+00:00
-- url     : https://prove2.me/theorems/2611fc16-5a85-4352-b23d-b7b7d0f121a6
-- title:
--   StochLean source theorem: ProbabilityTheory.IsCagladPath.leftLimitProcess_rightLimitProcess

import Definitions.Def_StochLean_Probability_Process_Path_RightLimit_F000
import Definitions.Def_SourceProof_60e710b522febb5ad2df8d23
import Definitions.Def_SourceProof_8da091e9abd21017e0adf845

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

namespace IsCagladPath
theorem _root_.Prove2MeSourceProof.h_ee0958f607118d8fce16af89 {ω : Ω}
    (hX : IsCagladPath (X · ω)) {t : ℝ≥0} (ht : t ≠ 0) :
    leftLimitProcess (rightLimitProcess X) t ω = X t ω := by
  let : (𝓝[<] t).NeBot := nhdsLT_neBot_of_exists_lt ⟨0, pos_iff_ne_zero.mpr ht⟩
  simp only [ProbabilityTheory.leftLimitProcess, if_neg ht]
  exact leftLim_eq_of_tendsto ((_root_.Prove2MeSourceProof.h_8da091e9abd21017e0adf845 hX) t)
end IsCagladPath

end ProbabilityTheory


