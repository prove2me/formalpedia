-- Prove2me | Definitions.Def_SourceProof_b7da9b0e051f7ca793d67cb5
-- name    : SourceProof_b7da9b0e051f7ca793d67cb5
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-25T12:39:51.513823+00:00
-- url     : https://prove2.me/theorems/a805a3f7-72a4-4057-8457-7685f1ea4351
-- title:
--   StochLean source theorem: ProbabilityTheory.IsGoodIntegrator.congr

import Definitions.Def_StochLean_Probability_Process_Semimartingale_Basic_F001
import Definitions.Def_StochLean_Probability_Process_Stopping_Finite_F002
import Definitions.Def_StochLean_Probability_Process_Stopping_Finite_F003
import Definitions.Def_StochLean_Probability_Process_Stopping_Finite_F006
import Definitions.Def_SourceProof_0de7ac3f2379dbed4c736869
import Mathlib.MeasureTheory.Integral.Indicator
import Mathlib.Probability.Process.LocalProperty

/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/

/-! # Localization of source good integrators and semimartingales

Elementary integrals agree when entire integrator paths agree. This proves closure under
approximation outside sets of vanishing probability and then the local-to-global direction
for ordinary semimartingales, including the Protter time-zero mask.
-/

@[expose] public section

open MeasureTheory Filter Set Finset
open scoped NNReal ENNReal Topology

namespace ProbabilityTheory

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {F : Filtration ℝ≥0 mΩ}
  {P : Measure Ω} {X Y : ℝ≥0 → Ω → ℝ}

namespace IsGoodIntegrator
theorem _root_.Prove2MeSourceProof.h_b7da9b0e051f7ca793d67cb5 (hX : IsGoodIntegrator X F P) (hXY : Indistinguishable X Y P) :
    IsGoodIntegrator Y F P := by
  intro H hH hu
  exact TendstoInMeasure.congr_left
    (fun n ↦ (_root_.Prove2MeSourceProof.h_0de7ac3f2379dbed4c736869 (hH n)) hXY) (hX H hH hu)
end IsGoodIntegrator

variable [IsFiniteMeasure P]

end ProbabilityTheory


