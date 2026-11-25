-- Prove2me | Definitions.Def_SourceProof_9ebbc06fcb43cb43e60fa156
-- name    : SourceProof_9ebbc06fcb43cb43e60fa156
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-25T00:45:35.052488+00:00
-- url     : https://prove2.me/theorems/22df257e-02e7-43f6-985b-6c3a8ff8732f
-- title:
--   StochLean source theorem: ProbabilityTheory.SimplePredictableRep.integral_eq_stopped_of_cutoff_path

import Definitions.Def_StochLean_Probability_Process_Semimartingale_SimplePredictable_Refinement_F000
import Definitions.Def_StochLean_Probability_Process_Stopping_Integrand_F000
import Definitions.Def_SourceProof_a9c44e06617a4753cffd0417
import Definitions.Def_SourceProof_f663a9831488630e6f3e2684
import Definitions.Def_SourceProof_fc4a2bac5634cdbfe2b154e5

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


theorem _root_.Prove2MeSourceProof.h_9ebbc06fcb43cb43e60fa156 (H K : SimplePredictableRep F)
    (X : ℝ≥0 → Ω → ℝ) (ω : Ω) (T : ℝ≥0)
    (hHK : ∀ t, K.toProcess t ω = if t ≤ T then H.toProcess t ω else 0) :
    K.integral X ω = H.integral (fun t v ↦ X (min t T) v) ω := by
  have hinit : K.initial ω = H.initial ω := by
    simpa using hHK 0
  have hsum := _root_.Prove2MeSourceProof.h_f663a9831488630e6f3e2684
    (fun i : Fin K.partition.size ↦ K.partition.point i.castSucc ω)
    (fun i : Fin K.partition.size ↦ K.partition.point i.succ ω)
    (fun i : Fin K.partition.size ↦ K.coefficient i ω)
    (fun i : Fin H.partition.size ↦ min (H.partition.point i.castSucc ω) T)
    (fun i : Fin H.partition.size ↦ min (H.partition.point i.succ ω) T)
    (fun i : Fin H.partition.size ↦ H.coefficient i ω)
    (fun i ↦ (_root_.Prove2MeSourceProof.h_fc4a2bac5634cdbfe2b154e5 (K.partition.path ω)) i)
    (fun i ↦ min_le_min_right T ((_root_.Prove2MeSourceProof.h_fc4a2bac5634cdbfe2b154e5 (H.partition.path ω)) i))
    (fun t ht ↦ by
      have heq := hHK t
      simp only [ProbabilityTheory.SimplePredictableRep.toProcess, ne_of_gt ht, if_false] at heq
      by_cases hT : t ≤ T
      · simpa only [min_lt_iff, le_min_iff, not_lt_of_ge hT, or_false, hT,
          and_true, if_true] using heq
      · simpa only [le_min_iff, hT, and_false, if_false, sum_const_zero] using heq)
    (fun t ↦ X t ω)
  change K.initial ω * X 0 ω + _ = H.initial ω * X (min 0 T) ω + _
  have hzero : min (0 : ℝ≥0) T = 0 := by simp
  rw [hinit, hzero, hsum]
end SimplePredictableRep

namespace IsSimplePredictable

variable {H : ℝ≥0 → Ω → ℝ}

end IsSimplePredictable
end ProbabilityTheory


