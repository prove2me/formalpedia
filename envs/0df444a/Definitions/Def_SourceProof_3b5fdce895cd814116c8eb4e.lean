-- Prove2me | Definitions.Def_SourceProof_3b5fdce895cd814116c8eb4e
-- name    : SourceProof_3b5fdce895cd814116c8eb4e
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-25T17:35:34.992541+00:00
-- url     : https://prove2.me/theorems/0aff521c-6e23-4d1c-a1c9-6939e7d7e9fc
-- title:
--   StochLean source theorem: ProbabilityTheory.StoppingTimePartition.hasCadlagPaths_leftRiemannSumProcess

import Definitions.Def_StochLean_Probability_Process_Partition_LeftSampling_F000
import Definitions.Def_StochLean_Probability_Process_Partition_LeftSampling_F001
import Definitions.Def_StochLean_Probability_Process_Partition_LeftSampling_F002
import Definitions.Def_SourceProof_3bfb9ef0d258afe6eedb13c5
import Definitions.Def_SourceProof_44c235d61a2cdcb446e715a4
import Definitions.Def_SourceProof_7c758b3f54acb965f59f9d0b
import Definitions.Def_SourceProof_824b0e2c6cd9530a7cfac3d4
import Definitions.Def_SourceProof_a2cb63993a652b5632791121

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

theorem _root_.Prove2MeSourceProof.h_3b5fdce895cd814116c8eb4e (π : StoppingTimePartition F)
    (h0 : Measurable[F 0] (Y 0))
    (hcoef : ∀ i : Fin π.size,
      Measurable[(π.point i.castSucc).measurableSpace] (fun ω ↦ Y (π.point i.castSucc ω) ω))
    (hrX : HasCadlagPaths X P) : HasCadlagPaths (π.leftRiemannSumProcess Y X) P := by
  rw [(_root_.Prove2MeSourceProof.h_824b0e2c6cd9530a7cfac3d4 π) Y X h0 hcoef]
  exact (_root_.Prove2MeSourceProof.h_44c235d61a2cdcb446e715a4 ((_root_.Prove2MeSourceProof.h_3bfb9ef0d258afe6eedb13c5 (π.leftSampleRep Y h0 hcoef)) hrX))
    (ae_of_all _ fun _ ↦ _root_.Prove2MeSourceProof.h_a2cb63993a652b5632791121 continuous_const)
end ProbabilityTheory.StoppingTimePartition


