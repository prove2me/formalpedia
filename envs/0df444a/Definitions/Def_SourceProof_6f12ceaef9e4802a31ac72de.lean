-- Prove2me | Definitions.Def_SourceProof_6f12ceaef9e4802a31ac72de
-- name    : SourceProof_6f12ceaef9e4802a31ac72de
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-25T20:33:08.649068+00:00
-- url     : https://prove2.me/theorems/00fdc84b-7b9f-52ac-8592-bf41c9a537a0
-- title:
--   StochLean source theorem: ProbabilityTheory.IsSemimartingale.quadraticVariation_congr

import Definitions.Def_StochLean_Probability_Process_Semimartingale_QuadraticVariation_F000
import Definitions.Def_SourceProof_2cbb2ed1687ae3057f41e0d2
import Definitions.Def_SourceProof_2d0886ee2025f07cabb3dec2
import Definitions.Def_SourceProof_3f47dd2e31d438d877ce48c9
import Definitions.Def_SourceProof_60b183cce884b1ffa7a599f8
import Definitions.Def_SourceProof_60e710b522febb5ad2df8d23
import Definitions.Def_SourceProof_73c70764ff89ea6093f75bd8
import Definitions.Def_SourceProof_79b70fbdac96840530cd88fc
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
theorem _root_.Prove2MeSourceProof.h_6f12ceaef9e4802a31ac72de
    (hX : IsSemimartingale X F P) (hY : IsSemimartingale Y F P) (hF : F.IsUsual P)
    (hXY : Indistinguishable X Y P) :
    Indistinguishable (hX.quadraticVariation hF) (hY.quadraticVariation hF) P := by
  let haX := (_root_.Prove2MeSourceProof.h_2d0886ee2025f07cabb3dec2 (_root_.Prove2MeSourceProof.h_2cbb2ed1687ae3057f41e0d2 hX)) hF (_root_.Prove2MeSourceProof.h_60b183cce884b1ffa7a599f8 hX)
  let hrX := (_root_.Prove2MeSourceProof.h_dff15d58aea8e47b608598ba (_root_.Prove2MeSourceProof.h_60b183cce884b1ffa7a599f8 hX))
  let haY := (_root_.Prove2MeSourceProof.h_2d0886ee2025f07cabb3dec2 (_root_.Prove2MeSourceProof.h_2cbb2ed1687ae3057f41e0d2 hY)) hF (_root_.Prove2MeSourceProof.h_60b183cce884b1ffa7a599f8 hY)
  let hrY := (_root_.Prove2MeSourceProof.h_dff15d58aea8e47b608598ba (_root_.Prove2MeSourceProof.h_60b183cce884b1ffa7a599f8 hY))
  have hi := (_root_.Prove2MeSourceProof.h_73c70764ff89ea6093f75bd8 ((_root_.Prove2MeSourceProof.h_3f47dd2e31d438d877ce48c9 hX) hY hF haX hrX hXY))
    ((_root_.Prove2MeSourceProof.h_79b70fbdac96840530cd88fc hY) hF haX hrX haY hrY (_root_.Prove2MeSourceProof.h_60e710b522febb5ad2df8d23 hXY))
  filter_upwards [hXY, hi] with ω hω hiω t
  change (X t ω) ^ 2 - 2 * hX.stochasticIntegral hF haX hrX t ω =
    (Y t ω) ^ 2 - 2 * hY.stochasticIntegral hF haY hrY t ω
  rw [hω t, hiω t]
end IsSemimartingale

end ProbabilityTheory


