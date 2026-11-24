-- Prove2me | Definitions.Def_SourceProof_487832d6cb2410ff018577d0
-- name    : SourceProof_487832d6cb2410ff018577d0
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-24T23:26:32.478168+00:00
-- url     : https://prove2.me/theorems/e90b2493-b824-449e-ac53-af7645dca9cd
-- title:
--   StochLean source theorem: ProbabilityTheory.IsSimplePredictable.elementaryIntegral_add_integrator

import Definitions.Def_StochLean_Probability_Process_Semimartingale_SimplePredictable_F001
import Definitions.Def_StochLean_Probability_Process_Semimartingale_SimplePredictable_F002
import Definitions.Def_StochLean_Probability_Process_Semimartingale_SimplePredictable_F003
import Definitions.Def_SourceProof_2d015c300a40edcbe97cb76a

/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/

/-! # Elementary linearity in the integrator

These declarations retain their original public names and statements. They live below
good-integrator stability so that the source simple-process algebra can reuse them directly.
-/

@[expose] public section

open MeasureTheory Finset
open scoped NNReal

namespace ProbabilityTheory

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {F : Filtration ℝ≥0 mΩ}

namespace IsSimplePredictable
theorem _root_.Prove2MeSourceProof.h_487832d6cb2410ff018577d0
    {H : ℝ≥0 → Ω → ℝ} (hH : IsSimplePredictable H F) (X Y : ℝ≥0 → Ω → ℝ) :
    hH.elementaryIntegral (X + Y) = hH.elementaryIntegral X + hH.elementaryIntegral Y :=
  (_root_.Prove2MeSourceProof.h_2d015c300a40edcbe97cb76a hH.choose) X Y
end IsSimplePredictable

end ProbabilityTheory


