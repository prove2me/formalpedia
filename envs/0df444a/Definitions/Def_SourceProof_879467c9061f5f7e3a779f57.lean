-- Prove2me | Definitions.Def_SourceProof_879467c9061f5f7e3a779f57
-- name    : SourceProof_879467c9061f5f7e3a779f57
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-25T19:24:04.381676+00:00
-- url     : https://prove2.me/theorems/8fff4450-8e9a-4798-815a-219c2a7de0d1
-- title:
--   StochLean source theorem: ProbabilityTheory.IsPoissonProcess.isSemimartingale_real

import Definitions.Def_SourceProof_00a8a291a5ec377d57feab0f
import Definitions.Def_SourceProof_5abd8ef5abbb365343c607a9
import Definitions.Def_SourceProof_8ba5e1d4066cc49c9a78b37c

/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/

/-! # The real-valued Poisson counting process is a semimartingale

Real left limits follow from monotonicity; right continuity is transported from the
canonical counting-process predicate. No cadlag path realization is assumed in addition
to those existing path properties. Adaptedness to the chosen filtration remains explicit.
-/

@[expose] public section

open MeasureTheory Filter Set
open scoped NNReal ENNReal Topology

namespace ProbabilityTheory.IsPoissonProcess

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsProbabilityMeasure P]
  {N : ℝ≥0 → Ω → ℕ} {rate : ℝ≥0}

theorem _root_.Prove2MeSourceProof.h_879467c9061f5f7e3a779f57 (hN : IsPoissonProcess N rate P)
    {F : Filtration ℝ≥0 mΩ} (hF : F.IsUsual P) (ha : Adapted F N) :
    IsSemimartingale (fun t ω ↦ (N t ω : ℝ)) F P := by
  apply (_root_.Prove2MeSourceProof.h_00a8a291a5ec377d57feab0f (_root_.Prove2MeSourceProof.h_8ba5e1d4066cc49c9a78b37c hN)) ?_ hF (_root_.Prove2MeSourceProof.h_5abd8ef5abbb365343c607a9 hN)
  intro t
  exact (continuous_of_discreteTopology : Continuous (fun n : ℕ ↦ (n : ℝ))).measurable.comp (ha t)
end ProbabilityTheory.IsPoissonProcess


