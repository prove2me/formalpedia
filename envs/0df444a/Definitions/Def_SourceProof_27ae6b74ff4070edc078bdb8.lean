-- Prove2me | Definitions.Def_SourceProof_27ae6b74ff4070edc078bdb8
-- name    : SourceProof_27ae6b74ff4070edc078bdb8
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-25T18:30:08.459159+00:00
-- url     : https://prove2.me/theorems/36da6728-5952-5fe4-923f-71d509f0d187
-- title:
--   StochLean source theorem: MeasureTheory.IsStoppingTime.isStronglyPredictable_indicator_lt

import Definitions.Def_SourceProof_354b37228f98fe5fdec5bcbb
import Definitions.Def_SourceProof_7cdb042af88bfa80a4278508
import Mathlib.Analysis.Normed.Group.Basic
import Mathlib.MeasureTheory.MeasurableSpace.Prod
import Mathlib.Probability.Process.Stopping
import Mathlib.Topology.Algebra.Monoid

/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/

/-! # Finite-time graphs of stopping times

Protter III.2 includes time zero in a stopping-time graph and excludes infinity.
The strict-future region is predictable, the closed-future region is optional,
and every stopping-time graph is optional. Predictability of the graph is not
asserted for an arbitrary stopping time.
-/

@[expose] public section

open MeasureTheory Set
open scoped NNReal

namespace ProbabilityTheory

end ProbabilityTheory

namespace MeasureTheory.IsStoppingTime

open ProbabilityTheory

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {F : Filtration ℝ≥0 mΩ}
  {τ : Ω → WithTop ℝ≥0}

theorem _root_.Prove2MeSourceProof.h_27ae6b74ff4070edc078bdb8 (hτ : IsStoppingTime F τ) :
    IsStronglyPredictable F (fun t : ℝ≥0 ↦ {ω | τ ω < (t : WithTop ℝ≥0)}.indicator
      (fun _ ↦ (1 : ℝ))) := by
  classical
  have ha : Adapted F (fun t : ℝ≥0 ↦ {ω | τ ω < (t : WithTop ℝ≥0)}.indicator
      (fun _ ↦ (1 : ℝ))) :=
    fun t ↦ measurable_const.indicator (hτ.measurableSet_lt t)
  apply (_root_.Prove2MeSourceProof.h_354b37228f98fe5fdec5bcbb ha)
  intro ω
  cases ht : τ ω with
  | top =>
    have he : (fun t : ℝ≥0 ↦ {ω | τ ω < (t : WithTop ℝ≥0)}.indicator
        (fun _ ↦ (1 : ℝ)) ω) = 0 := by
      funext t
      simp only [Set.indicator_apply, mem_ofPred_eq, ht, not_top_lt, if_false, Pi.zero_apply]
    rw [he]
    exact fun _ ↦ continuousWithinAt_const
  | coe a =>
    simpa only [Set.indicator_apply, mem_ofPred_eq, ht, WithTop.coe_lt_coe] using
      (_root_.Prove2MeSourceProof.h_7cdb042af88bfa80a4278508 a 1).1
end MeasureTheory.IsStoppingTime


