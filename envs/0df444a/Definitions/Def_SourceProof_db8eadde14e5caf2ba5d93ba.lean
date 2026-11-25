-- Prove2me | Definitions.Def_SourceProof_db8eadde14e5caf2ba5d93ba
-- name    : SourceProof_db8eadde14e5caf2ba5d93ba
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-25T17:37:02.910339+00:00
-- url     : https://prove2.me/theorems/fd2c426f-0bed-586f-865a-9ad26bba8801
-- title:
--   StochLean source theorem: ProbabilityTheory.StoppingTimePartition.quadraticCovariationSumProcess_polarization

import Definitions.Def_StochLean_Probability_Process_Partition_CrossSums_F000
import Definitions.Def_SourceProof_4654496346907e7968291676

/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/

/-! # Raw mixed increment sums and their pointwise algebra

The original pure deterministic covariation sum is used, with the separate
initial product. No adaptedness, regularity or integrability is needed here.
-/

@[expose] public section

open MeasureTheory
open scoped NNReal

namespace ProbabilityTheory.StoppingTimePartition

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {F : Filtration ℝ≥0 mΩ}

theorem _root_.Prove2MeSourceProof.h_db8eadde14e5caf2ba5d93ba (π : StoppingTimePartition F)
    (X Y : ℝ≥0 → Ω → ℝ) :
    π.quadraticCovariationSumProcess X Y = fun t ω ↦ (1 / 2 : ℝ) *
      (π.quadraticVariationSumProcess (X + Y) t ω - π.quadraticVariationSumProcess X t ω -
        π.quadraticVariationSumProcess Y t ω) := by
  funext t ω
  have h := _root_.Prove2MeSourceProof.h_4654496346907e7968291676 (π.path ω)
    (fun u ↦ X (min u t) ω) (fun u ↦ Y (min u t) ω)
  change StochLean.quadraticVariationSum (π.path ω) (fun u ↦ (X + Y) (min u t) ω) = _ at h
  simp only [Pi.add_apply] at h
  simp only [ProbabilityTheory.StoppingTimePartition.quadraticCovariationSumProcess, ProbabilityTheory.StoppingTimePartition.quadraticVariationSumProcess, h, Pi.add_apply]
  ring
end ProbabilityTheory.StoppingTimePartition


