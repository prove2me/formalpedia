-- Prove2me | Definitions.Def_StochLean_Probability_Process_Semimartingale_QuadraticVariation_F000
-- name    : StochLean_Probability_Process_Semimartingale_QuadraticVariation_F000
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-25T19:57:51.636486+00:00
-- url     : https://prove2.me/theorems/e7797af4-c74c-5c85-b7e8-f6c28101c04b
-- title:
--   StochLean: Probability.Process.Semimartingale.QuadraticVariation F000

import Definitions.Def_StochLean_Probability_Process_Path_LeftLimit_F000
import Definitions.Def_StochLean_Probability_Process_Semimartingale_StochasticIntegral_F000
import Definitions.Def_SourceProof_2cbb2ed1687ae3057f41e0d2
import Definitions.Def_SourceProof_2d0886ee2025f07cabb3dec2
import Definitions.Def_SourceProof_60b183cce884b1ffa7a599f8
import Definitions.Def_SourceProof_dff15d58aea8e47b608598ba
import Mathlib.Topology.Algebra.Group.Basic

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

noncomputable def IsSemimartingale.quadraticVariation
    (hX : IsSemimartingale X F P) (hF : F.IsUsual P) : ℝ≥0 → Ω → ℝ :=
  fun t ω ↦ (X t ω) ^ 2 - 2 *
    hX.stochasticIntegral hF ((_root_.Prove2MeSourceProof.h_2d0886ee2025f07cabb3dec2 (_root_.Prove2MeSourceProof.h_2cbb2ed1687ae3057f41e0d2 hX)) hF (_root_.Prove2MeSourceProof.h_60b183cce884b1ffa7a599f8 hX))
      (_root_.Prove2MeSourceProof.h_dff15d58aea8e47b608598ba (_root_.Prove2MeSourceProof.h_60b183cce884b1ffa7a599f8 hX)) t ω
end ProbabilityTheory


