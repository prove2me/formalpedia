-- Prove2me | Definitions.Def_SourceProof_98bda33797c63c6cacfeb839
-- name    : SourceProof_98bda33797c63c6cacfeb839
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-25T20:06:46.610126+00:00
-- url     : https://prove2.me/theorems/4fbfe518-eea8-527e-a9bf-3c8a3bdbab28
-- title:
--   StochLean source theorem: ProbabilityTheory.IsSemimartingale.adapted_quadraticVariation

import Definitions.Def_StochLean_Probability_Process_Semimartingale_QuadraticVariation_F000
import Definitions.Def_SourceProof_2cbb2ed1687ae3057f41e0d2
import Definitions.Def_SourceProof_2d0886ee2025f07cabb3dec2
import Definitions.Def_SourceProof_60b183cce884b1ffa7a599f8
import Definitions.Def_SourceProof_a306c42680d425170aa442b0
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
theorem _root_.Prove2MeSourceProof.h_98bda33797c63c6cacfeb839
    (hX : IsSemimartingale X F P) (hF : F.IsUsual P) :
    Adapted F (hX.quadraticVariation hF) := by
  intro t
  exact ((_root_.Prove2MeSourceProof.h_2cbb2ed1687ae3057f41e0d2 hX) t).pow_const 2 |>.sub
    (((_root_.Prove2MeSourceProof.h_a306c42680d425170aa442b0 hX) hF
      ((_root_.Prove2MeSourceProof.h_2d0886ee2025f07cabb3dec2 (_root_.Prove2MeSourceProof.h_2cbb2ed1687ae3057f41e0d2 hX)) hF (_root_.Prove2MeSourceProof.h_60b183cce884b1ffa7a599f8 hX))
      (_root_.Prove2MeSourceProof.h_dff15d58aea8e47b608598ba (_root_.Prove2MeSourceProof.h_60b183cce884b1ffa7a599f8 hX)) t).const_mul 2)
end IsSemimartingale

end ProbabilityTheory


