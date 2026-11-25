-- Prove2me | Definitions.Def_SourceProof_bdc784f4a82031949787bf4c
-- name    : SourceProof_bdc784f4a82031949787bf4c
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-25T08:00:49.979576+00:00
-- url     : https://prove2.me/theorems/7b1bb900-46f6-4db5-890e-87f28979753a
-- title:
--   StochLean source theorem: ProbabilityTheory.IsCagladPath.indicator_Iic

import Definitions.Def_StochLean_Probability_Process_Path_Caglad_F000
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.MeasureTheory.Function.Floor
import Mathlib.MeasureTheory.Measure.NullMeasurable
import Mathlib.Probability.Process.Adapted
import Mathlib.Probability.Process.Filtration
import Mathlib.Probability.Process.Predictable
import Mathlib.Probability.Process.Stopping
import Mathlib.Topology.Order.LeftRightLim

/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/

/-! # Cutting an integrand off after a stopping time

Unlike a stopped process, the cutoff is zero strictly after the stopping time.
The closed endpoint preserves the stopping jump and the initial value.
-/

@[expose] public section

open MeasureTheory Filter Set
open scoped NNReal Topology

namespace ProbabilityTheory

namespace IsCagladPath
theorem _root_.Prove2MeSourceProof.h_bdc784f4a82031949787bf4c {x : ℝ≥0 → ℝ} (hx : IsCagladPath x) (T : ℝ≥0) :
    IsCagladPath ((Iic T).indicator x) := by
  constructor
  · intro t
    by_cases ht : t ≤ T
    · change Tendsto _ (𝓝[≤] t) _
      rw [indicator_of_mem (s := Iic T) (a := t) ht]
      apply (hx.1 t).congr'
      filter_upwards [self_mem_nhdsWithin] with u hu
      exact (indicator_of_mem (s := Iic T) (a := u)
        (show u ≤ T from (show u ≤ t from hu).trans ht) x).symm
    · change Tendsto _ (𝓝[≤] t) _
      rw [indicator_of_notMem (s := Iic T) (a := t) ht]
      apply tendsto_const_nhds.congr'
      filter_upwards [nhdsWithin_le_nhds (Ioi_mem_nhds (lt_of_not_ge ht))] with u hu
      exact (indicator_of_notMem (s := Iic T) (a := u)
        (show ¬u ≤ T from not_le_of_gt hu) x).symm
  · intro t
    by_cases ht : t < T
    · obtain ⟨y, hy⟩ := hx.2 t
      refine ⟨y, hy.congr' ?_⟩
      filter_upwards [nhdsWithin_le_nhds (Iio_mem_nhds ht)] with u hu
      exact (indicator_of_mem (s := Iic T) (a := u)
        (show u ≤ T from (show u < T from hu).le) x).symm
    · refine ⟨0, tendsto_const_nhds.congr' ?_⟩
      filter_upwards [self_mem_nhdsWithin] with u hu
      exact (indicator_of_notMem (s := Iic T) (a := u)
        (show ¬u ≤ T from not_le_of_gt ((le_of_not_gt ht).trans_lt (show t < u from hu))) x).symm
end IsCagladPath

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {F : Filtration ℝ≥0 mΩ}

end ProbabilityTheory


