-- Prove2me | Definitions.Def_SourceProof_4429ff27e307e8c02b004131
-- name    : SourceProof_4429ff27e307e8c02b004131
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-25T20:14:13.515882+00:00
-- url     : https://prove2.me/theorems/dd460ec0-f4bb-543a-8113-b25fc1c63a7a
-- title:
--   StochLean source theorem: ProbabilityTheory.IsSemimartingale.jumpProcess_quadraticVariation

import Definitions.Def_StochLean_Probability_Process_Semimartingale_QuadraticVariation_F000
import Definitions.Def_SourceProof_1cdab28abe8ba1d0e72d086f
import Definitions.Def_SourceProof_2cbb2ed1687ae3057f41e0d2
import Definitions.Def_SourceProof_2d0886ee2025f07cabb3dec2
import Definitions.Def_SourceProof_3bbaad58387c4561f0731fe5
import Definitions.Def_SourceProof_4d9ac1d8fdeead36a7d9ab22
import Definitions.Def_SourceProof_60b183cce884b1ffa7a599f8
import Definitions.Def_SourceProof_60b56e0d38c6166660de298f
import Definitions.Def_SourceProof_ab0a4cce00e53a6efb5054a6
import Definitions.Def_SourceProof_af256655daa15d2226a5ad92
import Definitions.Def_SourceProof_dff15d58aea8e47b608598ba

/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/

/-! # The canonical raw quadratic variation of a semimartingale

The source definition is `X² - 2 (X₋ . X)`. It retains the original initial
square and uses only the previously constructed Chapter II integral. There is
no bracket for an arbitrary process outside the semimartingale domain, and no
separate zero-start or continuous-martingale bracket is constructed here.
-/

@[expose] public section

open MeasureTheory
open scoped NNReal

namespace ProbabilityTheory

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsFiniteMeasure P]
  {F : Filtration ℝ≥0 mΩ} {X Y : ℝ≥0 → Ω → ℝ}

namespace IsSemimartingale
theorem _root_.Prove2MeSourceProof.h_4429ff27e307e8c02b004131
    (hX : IsSemimartingale X F P) (hF : F.IsUsual P) :
    Indistinguishable (jumpProcess (hX.quadraticVariation hF))
      (fun t ω ↦ (jumpProcess X t ω) ^ 2) P := by
  let ha := (_root_.Prove2MeSourceProof.h_2d0886ee2025f07cabb3dec2 (_root_.Prove2MeSourceProof.h_2cbb2ed1687ae3057f41e0d2 hX)) hF (_root_.Prove2MeSourceProof.h_60b183cce884b1ffa7a599f8 hX)
  let hr := (_root_.Prove2MeSourceProof.h_dff15d58aea8e47b608598ba (_root_.Prove2MeSourceProof.h_60b183cce884b1ffa7a599f8 hX))
  let J := hX.stochasticIntegral hF ha hr
  filter_upwards [(_root_.Prove2MeSourceProof.h_60b183cce884b1ffa7a599f8 hX), (_root_.Prove2MeSourceProof.h_3bbaad58387c4561f0731fe5 hX) hF ha hr]
    with ω hXω hJjump t
  have hJω : ProbabilityTheory.IsCadlagPath (J · ω) := (_root_.Prove2MeSourceProof.h_ab0a4cce00e53a6efb5054a6 hX) hF ha hr ω
  have hsq : ProbabilityTheory.IsCadlagPath (fun u ↦ (X u ω) ^ 2) :=
    (_root_.Prove2MeSourceProof.h_60b56e0d38c6166660de298f hXω) (continuous_id.pow 2)
  have hmul : ProbabilityTheory.IsCadlagPath (fun u ↦ (2 : ℝ) * J u ω) :=
    (_root_.Prove2MeSourceProof.h_60b56e0d38c6166660de298f hJω) (continuous_const.mul continuous_id)
  change ProbabilityTheory.jumpProcess ((fun u v ↦ (X u v) ^ 2) - (fun u v ↦ 2 * J u v)) t ω = _
  rw [_root_.Prove2MeSourceProof.h_1cdab28abe8ba1d0e72d086f (X := fun u v ↦ (X u v) ^ 2)
    (Y := fun u v ↦ 2 * J u v) (ω := ω) hsq hmul t,
    (_root_.Prove2MeSourceProof.h_af256655daa15d2226a5ad92 hXω) t, (_root_.Prove2MeSourceProof.h_4d9ac1d8fdeead36a7d9ab22 hJω) 2 t]
  change (X t ω) ^ 2 - (ProbabilityTheory.leftLimitProcess X t ω) ^ 2 -
    2 * ProbabilityTheory.jumpProcess (hX.stochasticIntegral hF ha hr) t ω = _
  rw [hJjump t]
  simp only [ProbabilityTheory.jumpProcess, Pi.sub_apply]
  ring
end IsSemimartingale

end ProbabilityTheory


