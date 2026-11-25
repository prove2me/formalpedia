-- Prove2me | Definitions.Def_SourceProof_30142169a7dbed2f4e087a36
-- name    : SourceProof_30142169a7dbed2f4e087a36
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-25T12:40:02.92371+00:00
-- url     : https://prove2.me/theorems/8298875c-dcd7-43c2-9600-e96ae1d4752f
-- title:
--   StochLean source theorem: ProbabilityTheory.SimplePredictableRep.integral_eq_stopped_of_cutoff

import Definitions.Def_StochLean_Probability_Process_Semimartingale_SimplePredictable_Refinement_F000
import Definitions.Def_StochLean_Probability_Process_Stopping_Integrand_F000
import Definitions.Def_SourceProof_335ae0b6c99b920a26294278
import Definitions.Def_SourceProof_9ebbc06fcb43cb43e60fa156

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


theorem _root_.Prove2MeSourceProof.h_30142169a7dbed2f4e087a36 (H K : SimplePredictableRep F)
    (τ : Ω → WithTop ℝ≥0) (hHK : K.toProcess = cutoffIntegrand H.toProcess τ)
    (X : ℝ≥0 → Ω → ℝ) : K.integral X = H.integral (stoppedProcess X τ) := by
  funext ω
  have heq (t) := congrFun (congrFun hHK t) ω
  cases hτω : τ ω with
  | top =>
    have hpath (t) : K.toProcess t ω =
        if t ≤ H.partition.terminal ω then H.toProcess t ω else 0 := by
      have h := heq t
      simp only [ProbabilityTheory.cutoffIntegrand, hτω, le_top, if_true] at h
      by_cases ht : t ≤ H.partition.terminal ω
      · simpa only [if_pos ht] using h
      · simpa only [if_neg ht, (_root_.Prove2MeSourceProof.h_335ae0b6c99b920a26294278 H) (lt_of_not_ge ht)] using h
    have h := (_root_.Prove2MeSourceProof.h_9ebbc06fcb43cb43e60fa156 H) K X ω (H.partition.terminal ω) hpath
    have hpoint (i : Fin (H.partition.size + 1)) :
        min (H.partition.point i ω) (H.partition.terminal ω) = H.partition.point i ω :=
      min_eq_left (H.partition.monotone_point ω (Fin.le_last i))
    have hstop (t : ℝ≥0) : stoppedProcess X τ t ω = X t ω :=
      stoppedProcess_eq_of_le (by rw [hτω]; exact le_top)
    exact h.trans (by simp only [ProbabilityTheory.SimplePredictableRep.integral, hpoint, hstop]; simp)
  | coe T =>
    have hpath (t) : K.toProcess t ω = if t ≤ T then H.toProcess t ω else 0 := by
      simpa only [ProbabilityTheory.cutoffIntegrand, hτω, WithTop.coe_le_coe] using heq t
    have h := (_root_.Prove2MeSourceProof.h_9ebbc06fcb43cb43e60fa156 H) K X ω T hpath
    have hstop (t : ℝ≥0) : stoppedProcess X τ t ω = X (min t T) ω := by
      change X (min (t : WithTop ℝ≥0) (τ ω)).untopA ω = _
      rw [hτω, ← WithTop.coe_min]
      rfl
    exact h.trans (by simp only [ProbabilityTheory.SimplePredictableRep.integral, hstop])
end SimplePredictableRep

namespace IsSimplePredictable

variable {H : ℝ≥0 → Ω → ℝ}

end IsSimplePredictable
end ProbabilityTheory


