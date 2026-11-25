-- Prove2me | Definitions.Def_SourceProof_f2daf40b88ac8840065b16fc
-- name    : SourceProof_f2daf40b88ac8840065b16fc
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-25T18:37:18.4348+00:00
-- url     : https://prove2.me/theorems/450f2b1b-921f-4f3c-8de1-069db1470248
-- title:
--   StochLean source theorem: ProbabilityTheory.IsSimplePredictable.elementaryIntegralProcess_cutoff

import Definitions.Def_StochLean_Probability_Process_Semimartingale_SimplePredictable_IntegralProcess_F000
import Definitions.Def_StochLean_Probability_Process_Semimartingale_SimplePredictable_IntegralProcess_F001
import Definitions.Def_StochLean_Probability_Process_Semimartingale_SimplePredictable_Stopping_F000
import Definitions.Def_SourceProof_3ef5f6d86cdc9a68c55760b0
import Definitions.Def_SourceProof_d0b901b94fc3806e9c302bc2
import Definitions.Def_SourceProof_d14c6a5c22923c1d07f1756e
import Definitions.Def_SourceProof_ebaf9e73dbb24b573c624591

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

theorem _root_.Prove2MeSourceProof.h_f2daf40b88ac8840065b16fc (hH : IsSimplePredictable H F)
    {τ : Ω → WithTop ℝ≥0} (hτ : IsStoppingTime F τ) (X : ℝ≥0 → Ω → ℝ) :
    ((_root_.Prove2MeSourceProof.h_ebaf9e73dbb24b573c624591 hH) hτ).elementaryIntegralProcess X =
      stoppedProcess (hH.elementaryIntegralProcess X) τ := by
  rw [← (_root_.Prove2MeSourceProof.h_d0b901b94fc3806e9c302bc2 hH)]
  funext t
  rw [(_root_.Prove2MeSourceProof.h_3ef5f6d86cdc9a68c55760b0 ((_root_.Prove2MeSourceProof.h_ebaf9e73dbb24b573c624591 hH) hτ)),
    (_root_.Prove2MeSourceProof.h_d14c6a5c22923c1d07f1756e hH) hτ, (_root_.Prove2MeSourceProof.h_3ef5f6d86cdc9a68c55760b0 hH),
    stoppedProcess_stoppedProcess', stoppedProcess_stoppedProcess']
  apply congrArg (fun σ : Ω → WithTop ℝ≥0 ↦ hH.elementaryIntegral (stoppedProcess X σ))
  funext ω
  exact min_comm (τ ω) (t : WithTop ℝ≥0)
end IsSimplePredictable
end ProbabilityTheory


