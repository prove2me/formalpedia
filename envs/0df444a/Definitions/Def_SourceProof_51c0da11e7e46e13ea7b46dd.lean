-- Prove2me | Definitions.Def_SourceProof_51c0da11e7e46e13ea7b46dd
-- name    : SourceProof_51c0da11e7e46e13ea7b46dd
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-25T20:28:54.04901+00:00
-- url     : https://prove2.me/theorems/6bf4b385-27cd-47e6-9bc5-496d6dbdc517
-- title:
--   StochLean source theorem: ProbabilityTheory.IsSemimartingale.hasCadlagPaths_quadraticVariation

import Definitions.Def_StochLean_Probability_Process_Semimartingale_QuadraticVariation_F000
import Definitions.Def_SourceProof_264b430747bbe6ee020dbafc
import Definitions.Def_SourceProof_2cbb2ed1687ae3057f41e0d2
import Definitions.Def_SourceProof_2d0886ee2025f07cabb3dec2
import Definitions.Def_SourceProof_44c235d61a2cdcb446e715a4
import Definitions.Def_SourceProof_470edda0db5866af621dc0b9
import Definitions.Def_SourceProof_60b183cce884b1ffa7a599f8
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
theorem _root_.Prove2MeSourceProof.h_51c0da11e7e46e13ea7b46dd
    (hX : IsSemimartingale X F P) (hF : F.IsUsual P) :
    HasCadlagPaths (hX.quadraticVariation hF) P := by
  have hJ := (_root_.Prove2MeSourceProof.h_470edda0db5866af621dc0b9 hX) hF
    ((_root_.Prove2MeSourceProof.h_2d0886ee2025f07cabb3dec2 (_root_.Prove2MeSourceProof.h_2cbb2ed1687ae3057f41e0d2 hX)) hF (_root_.Prove2MeSourceProof.h_60b183cce884b1ffa7a599f8 hX))
    (_root_.Prove2MeSourceProof.h_dff15d58aea8e47b608598ba (_root_.Prove2MeSourceProof.h_60b183cce884b1ffa7a599f8 hX))
  exact (_root_.Prove2MeSourceProof.h_44c235d61a2cdcb446e715a4 ((_root_.Prove2MeSourceProof.h_264b430747bbe6ee020dbafc (_root_.Prove2MeSourceProof.h_60b183cce884b1ffa7a599f8 hX)) (continuous_id.pow 2)))
    ((_root_.Prove2MeSourceProof.h_264b430747bbe6ee020dbafc hJ) (continuous_const.mul continuous_id))
end IsSemimartingale

end ProbabilityTheory


