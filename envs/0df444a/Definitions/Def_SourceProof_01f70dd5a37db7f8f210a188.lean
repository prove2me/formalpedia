-- Prove2me | Definitions.Def_SourceProof_01f70dd5a37db7f8f210a188
-- name    : SourceProof_01f70dd5a37db7f8f210a188
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-25T19:21:57.881042+00:00
-- url     : https://prove2.me/theorems/9054a11a-6926-57dc-b5e3-02b9f494e2c1
-- title:
--   StochLean source theorem: ProbabilityTheory.StoppingTimePartition.martingale_sampledProcess_of_ui

import Definitions.Def_StochLean_Probability_Process_Partition_Sampling_F001
import Definitions.Def_StochLean_Probability_Process_Partition_Sampling_F002
import Definitions.Def_SourceProof_11164a054fb3128d67bf4e54
import Definitions.Def_SourceProof_7ed134b1bc2c6d08d6fe0b39
import Definitions.Def_SourceProof_e8e88fba5b0d0c5182c1aea7

/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/

/-! # Discrete sampling on a source stopping-time partition

The finite ordered endpoint family is extended constantly after its last index. Its canonical
stopping sigma-fields and sampled process are then indexed by natural numbers, so the existing
discrete martingale and integral owners can be reused without a second finite-index calculus.
-/

@[expose] public section

open MeasureTheory Filter
open scoped NNReal ENNReal

namespace ProbabilityTheory.StoppingTimePartition

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {F : Filtration ℝ≥0 mΩ}

variable {P : Measure Ω} {X : ℝ≥0 → Ω → ℝ} [IsFiniteMeasure P]

theorem _root_.Prove2MeSourceProof.h_01f70dd5a37db7f8f210a188 (π : StoppingTimePartition F)
    (hX : Martingale X F P) (hu : UniformIntegrable X 1 P)
    (hF : F.IsUsual P) (hr : HasRightContinuousPaths X P) :
    Martingale (π.sampledProcess X) π.sampledFiltration P := by
  exact (_root_.Prove2MeSourceProof.h_e8e88fba5b0d0c5182c1aea7 hX) hu hF hr
    (fun n ↦ (π.pointNat n).withTop) (fun n ↦ (π.pointNat n).isStoppingTime)
    (_root_.Prove2MeSourceProof.h_11164a054fb3128d67bf4e54 π) (fun n ↦ ae_of_all _ (_root_.Prove2MeSourceProof.h_7ed134b1bc2c6d08d6fe0b39 (π.pointNat n)))
variable [SigmaFiniteFiltration P F]

end ProbabilityTheory.StoppingTimePartition


