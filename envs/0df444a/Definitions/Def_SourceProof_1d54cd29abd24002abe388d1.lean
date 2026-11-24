-- Prove2me | Definitions.Def_SourceProof_1d54cd29abd24002abe388d1
-- name    : SourceProof_1d54cd29abd24002abe388d1
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-24T22:07:25.972465+00:00
-- url     : https://prove2.me/theorems/60a2d64c-a6e5-498e-8907-86b0cef2c12b
-- title:
--   StochLean source theorem: MeasureTheory.norm_le_of_le_hittingAfter_norm_of_pos

import Definitions.Def_StochLean_Probability_Process_Path_Cadlag_F000
import Definitions.Def_StochLean_Probability_Process_Path_Cadlag_F001
import Definitions.Def_SourceProof_1e52c15149bd45e1ab3198d1
import Mathlib.MeasureTheory.Constructions.BorelSpace.Real
import Mathlib.MeasureTheory.Measure.NullMeasurable
import Mathlib.Probability.Process.Filtration
import Mathlib.Probability.Process.HittingTime
import Mathlib.Probability.Process.Stopping
import Mathlib.Topology.Order.Compact

/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/

/-! # Open-target hitting and exit bounds for left-continuous paths

Dense detection must include the initial time separately: a left-continuous path
on a half-line can have an isolated initial value. At a positive first exit the
norm remains bounded from above, unlike a cadlag first exit with jump overshoot.
-/

@[expose] public section

open MeasureTheory Filter Set TopologicalSpace
open scoped NNReal Topology

namespace ProbabilityTheory

variable {E : Type*} [TopologicalSpace E]

end ProbabilityTheory

namespace MeasureTheory

variable {Ω E : Type*} [TopologicalSpace E] {X : ℝ≥0 → Ω → E}

variable {mΩ : MeasurableSpace Ω} [MeasurableSpace E] [OpensMeasurableSpace E]
  {F : Filtration ℝ≥0 mΩ}

end MeasureTheory

namespace MeasureTheory

variable {Ω : Type*} {X : ℝ≥0 → Ω → ℝ}

theorem _root_.Prove2MeSourceProof.h_1d54cd29abd24002abe388d1 {a : ℝ} {t : ℝ≥0} {ω : Ω}
    (hl : ProbabilityTheory.IsLeftContinuousPath (X · ω))
    (hpos : (0 : WithTop ℝ≥0) < hittingAfter X {x | a < ‖x‖} 0 ω)
    (ht : (t : WithTop ℝ≥0) ≤ hittingAfter X {x | a < ‖x‖} 0 ω) : ‖X t ω‖ ≤ a := by
  by_cases hlt : (t : WithTop ℝ≥0) < hittingAfter X {x | a < ‖x‖} 0 ω
  · exact _root_.Prove2MeSourceProof.h_1e52c15149bd45e1ab3198d1 hlt
  · have heq : (t : WithTop ℝ≥0) = hittingAfter X {x | a < ‖x‖} 0 ω :=
      le_antisymm ht (le_of_not_gt hlt)
    have ht0 : (0 : ℝ≥0) < t := WithTop.coe_lt_coe.mp (hpos.trans_eq heq.symm)
    obtain ⟨u, _, hu, hlim⟩ := exists_seq_strictMono_tendsto' ht0
    have hwithin : Tendsto u atTop (𝓝[≤] t) :=
      tendsto_nhdsWithin_iff.mpr
        ⟨hlim, Eventually.of_forall fun n ↦ (hu n).2.le⟩
    apply le_of_tendsto ((hl t).norm.tendsto.comp hwithin)
    exact Eventually.of_forall fun n ↦ _root_.Prove2MeSourceProof.h_1e52c15149bd45e1ab3198d1
      ((WithTop.coe_lt_coe.mpr (hu n).2).trans_eq heq)
end MeasureTheory


