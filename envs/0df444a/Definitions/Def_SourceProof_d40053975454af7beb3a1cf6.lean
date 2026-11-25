-- Prove2me | Definitions.Def_SourceProof_d40053975454af7beb3a1cf6
-- name    : SourceProof_d40053975454af7beb3a1cf6
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-25T18:48:24.912971+00:00
-- url     : https://prove2.me/theorems/ea1a79d7-3a45-404a-8e98-4dba9a8ec16f
-- title:
--   StochLean source theorem: ProbabilityTheory.norm_firstExitTruncation_le

import Definitions.Def_SourceProof_1d54cd29abd24002abe388d1
import Definitions.Def_SourceProof_c9eacbbef1c8e0923f7b8eda
import Mathlib.Analysis.Normed.Group.Continuity
import Mathlib.Probability.Process.LocalProperty
import Mathlib.Topology.Compactness.Compact

/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/

/-! # Bounded masked cutoffs of adapted caglad processes

Open norm exits need not attain their target. Compact path bounds prove divergence
without an attainment claim. The closed cutoff remains bounded at a positive exit
by left continuity; the initial mask handles arbitrary initial values.
-/

@[expose] public section

open MeasureTheory Filter Set
open scoped NNReal Topology

namespace ProbabilityTheory

variable {Ω : Type*} {H : ℝ≥0 → Ω → ℝ}

theorem _root_.Prove2MeSourceProof.h_d40053975454af7beb3a1cf6 {a : ℝ} (ha : 0 ≤ a) {ω : Ω}
    (hl : IsLeftContinuousPath (H · ω)) (t : ℝ≥0) :
    ‖firstExitTruncation H a t ω‖ ≤ a := by
  classical
  by_cases hpos : (0 : WithTop ℝ≥0) < hittingAfter H {x | a < ‖x‖} 0 ω
  · rw [ProbabilityTheory.firstExitTruncation, indicator_of_mem
      (show ω ∈ {v | (0 : WithTop ℝ≥0) < hittingAfter H {x | a < ‖x‖} 0 v} from hpos)]
    by_cases ht : (t : WithTop ℝ≥0) ≤ hittingAfter H {x | a < ‖x‖} 0 ω
    · simp only [ProbabilityTheory.cutoffIntegrand, if_pos ht]
      exact _root_.Prove2MeSourceProof.h_1d54cd29abd24002abe388d1 hl hpos ht
    · simpa only [ProbabilityTheory.cutoffIntegrand, if_neg ht, norm_zero] using ha
  · simpa only [ProbabilityTheory.firstExitTruncation, indicator_of_notMem
      (show ω ∉ {v | (0 : WithTop ℝ≥0) < hittingAfter H {x | a < ‖x‖} 0 v} from hpos),
      norm_zero] using ha
end ProbabilityTheory

namespace MeasureTheory

open ProbabilityTheory

end MeasureTheory


