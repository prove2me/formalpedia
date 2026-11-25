-- Prove2me | Definitions.Def_SourceProof_d0b901b94fc3806e9c302bc2
-- name    : SourceProof_d0b901b94fc3806e9c302bc2
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-25T17:40:21.988318+00:00
-- url     : https://prove2.me/theorems/63b99140-cb69-5ce7-bd55-094d68e4d796
-- title:
--   StochLean source theorem: ProbabilityTheory.IsSimplePredictable.elementaryIntegralProcess_stoppedProcess

import Definitions.Def_StochLean_Probability_Process_Semimartingale_SimplePredictable_IntegralProcess_F000
import Definitions.Def_StochLean_Probability_Process_Semimartingale_SimplePredictable_IntegralProcess_F001
import Definitions.Def_StochLean_Probability_Process_Semimartingale_SimplePredictable_Stopping_F000
import Definitions.Def_SourceProof_5b100e4daa8b4172c8e4c869

/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/

/-! # Stopping the source elementary integral process

The integrator-stopping identity is pathwise even for an arbitrary raw random time,
possibly infinite. The integrand-cutoff identity additionally needs a stopping time
to keep the cutoff in the source simple predictable class. Cutoff is not frozen stopping.
-/

@[expose] public section

open MeasureTheory
open scoped NNReal

namespace ProbabilityTheory

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {F : Filtration ℝ≥0 mΩ}

namespace IsSimplePredictable

variable {H : ℝ≥0 → Ω → ℝ}

theorem _root_.Prove2MeSourceProof.h_d0b901b94fc3806e9c302bc2 (hH : IsSimplePredictable H F)
    (X : ℝ≥0 → Ω → ℝ) (τ : Ω → WithTop ℝ≥0) :
    hH.elementaryIntegralProcess (stoppedProcess X τ) =
      stoppedProcess (hH.elementaryIntegralProcess X) τ :=
  (_root_.Prove2MeSourceProof.h_5b100e4daa8b4172c8e4c869 hH.choose) X τ
end IsSimplePredictable
end ProbabilityTheory


