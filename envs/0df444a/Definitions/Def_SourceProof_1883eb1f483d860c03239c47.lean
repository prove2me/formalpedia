-- Prove2me | Definitions.Def_SourceProof_1883eb1f483d860c03239c47
-- name    : SourceProof_1883eb1f483d860c03239c47
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-25T20:14:21.599502+00:00
-- url     : https://prove2.me/theorems/79b76a12-906a-56a4-8463-4801a416b8ab
-- title:
--   StochLean source theorem: ProbabilityTheory.IsSemimartingale.quadraticVariation_zero_ae

import Definitions.Def_StochLean_Probability_Process_Semimartingale_QuadraticVariation_F000
import Definitions.Def_SourceProof_12d34a5d964556d97aab2788
import Definitions.Def_SourceProof_2cbb2ed1687ae3057f41e0d2
import Definitions.Def_SourceProof_2d0886ee2025f07cabb3dec2
import Definitions.Def_SourceProof_60b183cce884b1ffa7a599f8
import Definitions.Def_SourceProof_d2b77a9c3200634f142d37a0
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
theorem _root_.Prove2MeSourceProof.h_1883eb1f483d860c03239c47
    (hX : IsSemimartingale X F P) (hF : F.IsUsual P) :
    hX.quadraticVariation hF 0 =ᵐ[P] fun ω ↦ (X 0 ω) ^ 2 := by
  filter_upwards [(_root_.Prove2MeSourceProof.h_d2b77a9c3200634f142d37a0 hX) hF
    ((_root_.Prove2MeSourceProof.h_2d0886ee2025f07cabb3dec2 (_root_.Prove2MeSourceProof.h_2cbb2ed1687ae3057f41e0d2 hX)) hF (_root_.Prove2MeSourceProof.h_60b183cce884b1ffa7a599f8 hX))
    (_root_.Prove2MeSourceProof.h_dff15d58aea8e47b608598ba (_root_.Prove2MeSourceProof.h_60b183cce884b1ffa7a599f8 hX))] with ω hω
  simp only [_root_.Prove2MeSourceProof.h_12d34a5d964556d97aab2788, Pi.zero_apply, zero_mul] at hω
  simp only [ProbabilityTheory.IsSemimartingale.quadraticVariation, hω, mul_zero, sub_zero]
end IsSemimartingale

end ProbabilityTheory


