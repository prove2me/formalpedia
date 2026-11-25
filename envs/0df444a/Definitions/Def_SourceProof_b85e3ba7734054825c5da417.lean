-- Prove2me | Definitions.Def_SourceProof_b85e3ba7734054825c5da417
-- name    : SourceProof_b85e3ba7734054825c5da417
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-25T19:13:41.865054+00:00
-- url     : https://prove2.me/theorems/b903766c-228c-5f87-b53b-6eb6941b40a0
-- title:
--   StochLean source theorem: ProbabilityTheory.StoppingTimePartition.adapted_leftRiemannSumProcess

import Definitions.Def_StochLean_Probability_Process_Partition_LeftSampling_F000
import Definitions.Def_StochLean_Probability_Process_Partition_LeftSampling_F001
import Definitions.Def_StochLean_Probability_Process_Partition_LeftSampling_F002
import Definitions.Def_SourceProof_44c235d61a2cdcb446e715a4
import Definitions.Def_SourceProof_7c758b3f54acb965f59f9d0b
import Definitions.Def_SourceProof_824b0e2c6cd9530a7cfac3d4
import Definitions.Def_SourceProof_d33983359663d20877640616

/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/

/-! # Adaptedness and cadlag paths of increment-only random Riemann sums

These properties follow from the existing source representation and its
independent initial term. The integrator need not be a semimartingale.
-/

@[expose] public section

open MeasureTheory
open scoped NNReal

namespace ProbabilityTheory.StoppingTimePartition

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {F : Filtration ℝ≥0 mΩ}
  {P : Measure Ω} {Y X : ℝ≥0 → Ω → ℝ}

theorem _root_.Prove2MeSourceProof.h_b85e3ba7734054825c5da417 (π : StoppingTimePartition F)
    (h0 : Measurable[F 0] (Y 0))
    (hcoef : ∀ i : Fin π.size,
      Measurable[(π.point i.castSucc).measurableSpace] (fun ω ↦ Y (π.point i.castSucc ω) ω))
    (haX : Adapted F X) (hF : F.IsUsual P) (hrX : HasRightContinuousPaths X P) :
    Adapted F (π.leftRiemannSumProcess Y X) := by
  rw [(_root_.Prove2MeSourceProof.h_824b0e2c6cd9530a7cfac3d4 π) Y X h0 hcoef]
  intro t
  exact ((_root_.Prove2MeSourceProof.h_d33983359663d20877640616 (π.leftSampleRep Y h0 hcoef)) haX hF hrX t).sub
    ((h0.mul (haX 0)).mono (F.mono bot_le) le_rfl)
end ProbabilityTheory.StoppingTimePartition


