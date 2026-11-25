-- Prove2me | Definitions.Def_SourceProof_dda4b24463a1d067fd5419cb
-- name    : SourceProof_dda4b24463a1d067fd5419cb
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-25T17:38:57.690744+00:00
-- url     : https://prove2.me/theorems/b08087e3-2bda-46c3-a42d-7a219b6f077b
-- title:
--   StochLean source theorem: ProbabilityTheory.SimplePredictableRep.toProcess_cutoffFinite

import Definitions.Def_StochLean_Probability_Process_Semimartingale_SimplePredictable_Stopping_F000
import Definitions.Def_SourceProof_335ae0b6c99b920a26294278
import Definitions.Def_SourceProof_45763a1547f08491c4364e73
import Definitions.Def_SourceProof_5db9266dc6535252f1f5c0f9
import Definitions.Def_SourceProof_701610429fa16d24c6724a4a
import Definitions.Def_SourceProof_88489cf844867d47930cc1e7
import Definitions.Def_SourceProof_8f7895612117943074291d58
import Definitions.Def_SourceProof_96c840413a5bd52fd9e42aec
import Definitions.Def_SourceProof_a741dec55cf454b50f9420c0
import Definitions.Def_SourceProof_a9c44e06617a4753cffd0417
import Definitions.Def_SourceProof_c1f91df6c360f9f8d687e8dd
import Definitions.Def_SourceProof_d23ff5479f0301df9bb337e0

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

theorem _root_.Prove2MeSourceProof.h_dda4b24463a1d067fd5419cb (H : SimplePredictableRep F) (σ : FiniteStoppingTime F) :
    (H.cutoffFinite σ).toProcess = cutoffIntegrand H.toProcess σ.withTop := by
  let ρ := H.partition.splitAt σ
  have hρ : ρ.Refines H.partition := (_root_.Prove2MeSourceProof.h_a741dec55cf454b50f9420c0 H.partition) σ
  have heq := (_root_.Prove2MeSourceProof.h_96c840413a5bd52fd9e42aec H) hρ
  funext t ω
  by_cases ht : t = 0
  · subst t
    simp only [_root_.Prove2MeSourceProof.h_a9c44e06617a4753cffd0417, _root_.Prove2MeSourceProof.h_88489cf844867d47930cc1e7]
    rfl
  by_cases hterm : t ≤ ρ.terminal ω
  · have hcell : ∃ i : Fin ρ.size, ρ.point i.castSucc ω < t ∧ t ≤ ρ.point i.succ ω :=
      (_root_.Prove2MeSourceProof.h_8f7895612117943074291d58 (ρ.path ω)) ⟨lt_of_le_of_ne bot_le (Ne.symm ht), hterm⟩
    obtain ⟨i, hi⟩ := hcell
    have hj : ∃ j, ρ.point j ω = σ ω := (_root_.Prove2MeSourceProof.h_5db9266dc6535252f1f5c0f9 H.partition) σ ω
    obtain ⟨j, hj⟩ := hj
    have hσ : t ≤ σ ω ↔ ρ.point i.castSucc ω < σ ω := by
      simpa only [hj] using (_root_.Prove2MeSourceProof.h_701610429fa16d24c6724a4a (_root_.Prove2MeSourceProof.h_d23ff5479f0301df9bb337e0 ρ)) hi j
    rw [(_root_.Prove2MeSourceProof.h_45763a1547f08491c4364e73 (i := i) (H.cutoffFinite σ)) hi]
    change (if ρ.point i.castSucc ω < σ ω then (H.repartition ρ).coefficient i ω else 0) = _
    rw [ProbabilityTheory.cutoffIntegrand]
    simp only [ProbabilityTheory.FiniteStoppingTime.withTop, WithTop.coe_le_coe]
    rw [← heq, (_root_.Prove2MeSourceProof.h_45763a1547f08491c4364e73 (i := i) (H.repartition ρ)) hi]
    simp only [hσ]
  · have hρt : ρ.terminal ω < t := lt_of_not_ge hterm
    rw [(_root_.Prove2MeSourceProof.h_335ae0b6c99b920a26294278 (H.cutoffFinite σ)) hρt,
      ProbabilityTheory.cutoffIntegrand, (_root_.Prove2MeSourceProof.h_335ae0b6c99b920a26294278 H) (((_root_.Prove2MeSourceProof.h_c1f91df6c360f9f8d687e8dd hρ) ω).trans_lt hρt)]
    simp only [ite_self]
end SimplePredictableRep

namespace IsSimplePredictable

variable {H : ℝ≥0 → Ω → ℝ}

end IsSimplePredictable
end ProbabilityTheory


