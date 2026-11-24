-- Prove2me | Definitions.Def_SourceProof_056f0ffa0965e1b3a522e2ff
-- name    : SourceProof_056f0ffa0965e1b3a522e2ff
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-24T22:15:17.880031+00:00
-- url     : https://prove2.me/theorems/e5e9a011-eff2-40fb-9398-d408b43111b3
-- title:
--   StochLean source theorem: ProbabilityTheory.IsCadlagPath.min_const

import Definitions.Def_StochLean_Probability_Process_Path_Cadlag_F000
import Definitions.Def_StochLean_Probability_Process_Path_Cadlag_F001
import Definitions.Def_SourceProof_38b6716030de814054336ad8
import Mathlib.Probability.Process.Stopping

/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/

/-! # Stopping preserves common-event path regularity -/

@[expose] public section

open MeasureTheory Filter Set
open scoped NNReal Topology

namespace ProbabilityTheory

variable {E : Type*} [TopologicalSpace E] {x : ℝ≥0 → E}

namespace IsCadlagPath
theorem _root_.Prove2MeSourceProof.h_056f0ffa0965e1b3a522e2ff (hx : IsCadlagPath x) (T : ℝ≥0) :
    IsCadlagPath (fun t ↦ x (min t T)) := by
  refine ⟨(_root_.Prove2MeSourceProof.h_38b6716030de814054336ad8 hx.1) T, ?_⟩
  intro t ht
  by_cases h : t ≤ T
  · obtain ⟨y, hy⟩ := hx.2 t ht
    refine ⟨y, hy.congr' ?_⟩
    filter_upwards [self_mem_nhdsWithin] with s hs
    rw [min_eq_left (hs.le.trans h)]
  · refine ⟨x T, tendsto_const_nhds.congr' ?_⟩
    have hTt : T < t := lt_of_not_ge h
    filter_upwards [eventually_nhdsWithin_of_eventually_nhds (eventually_gt_nhds hTt)] with s hs
    rw [min_eq_right hs.le]
end IsCadlagPath

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω}
  {X : ℝ≥0 → Ω → E}

end ProbabilityTheory


