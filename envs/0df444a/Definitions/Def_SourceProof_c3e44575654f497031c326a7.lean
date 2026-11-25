-- Prove2me | Definitions.Def_SourceProof_c3e44575654f497031c326a7
-- name    : SourceProof_c3e44575654f497031c326a7
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-25T17:47:12.972311+00:00
-- url     : https://prove2.me/theorems/ba87cd9f-4e17-4faf-be47-66066928d83b
-- title:
--   StochLean source theorem: ProbabilityTheory.SimplePredictableRep.isSimplePredictable_cutoff

import Definitions.Def_StochLean_Probability_Process_Semimartingale_SimplePredictable_Stopping_F000
import Definitions.Def_SourceProof_335ae0b6c99b920a26294278
import Definitions.Def_SourceProof_c3c7921df94e85b3cc715c88
import Definitions.Def_SourceProof_dda4b24463a1d067fd5419cb

/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/

/-! # Stopping the full source simple predictable class

The cutoff is `H 1_[0,τ]`, not the frozen stopped process `H^τ`. The source initial
coefficient is retained, including when the stopping time is zero. No boundedness
of coefficients or deterministic bound on the finite partition endpoints is imposed.
-/

@[expose] public section

open MeasureTheory Finset Set
open scoped NNReal

namespace ProbabilityTheory

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {F : Filtration ℝ≥0 mΩ}

namespace SimplePredictableRep


theorem _root_.Prove2MeSourceProof.h_c3e44575654f497031c326a7 (H : SimplePredictableRep F)
    {τ : Ω → WithTop ℝ≥0} (hτ : IsStoppingTime F τ) :
    IsSimplePredictable (cutoffIntegrand H.toProcess τ) F := by
  let σ := ProbabilityTheory.FiniteStoppingTime.ofNotTop (H.partition.terminal.isStoppingTime.min hτ)
    (fun ω ↦ ne_top_of_le_ne_top WithTop.coe_ne_top (min_le_left _ _))
  refine ⟨H.cutoffFinite σ, ((_root_.Prove2MeSourceProof.h_dda4b24463a1d067fd5419cb H) σ).trans ?_⟩
  have hσ : σ.withTop = fun ω ↦ min (H.partition.terminal ω : WithTop ℝ≥0) (τ ω) :=
    _root_.Prove2MeSourceProof.h_c3c7921df94e85b3cc715c88 _ _
  rw [hσ]
  funext t ω
  by_cases ht : t ≤ H.partition.terminal ω
  · simp only [ProbabilityTheory.cutoffIntegrand, le_min_iff, WithTop.coe_le_coe, ht, true_and]
  · rw [ProbabilityTheory.cutoffIntegrand, ProbabilityTheory.cutoffIntegrand,
      (_root_.Prove2MeSourceProof.h_335ae0b6c99b920a26294278 H) (lt_of_not_ge ht)]
    simp only [ite_self]
end SimplePredictableRep

namespace IsSimplePredictable

variable {H : ℝ≥0 → Ω → ℝ}

end IsSimplePredictable
end ProbabilityTheory


