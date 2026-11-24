-- Prove2me | Definitions.Def_SourceProof_6e9bb4c834a1b44d569cca8b
-- name    : SourceProof_6e9bb4c834a1b44d569cca8b
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-24T23:02:02.777773+00:00
-- url     : https://prove2.me/theorems/f7c134fe-dbda-4079-98cc-a541f0422abb
-- title:
--   StochLean source theorem: ProbabilityTheory.TendstoUCP.stoppedProcess

import Definitions.Def_StochLean_Probability_Process_UCP_F001
import Definitions.Def_SourceProof_c85f5070e7769bac711d7f66
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

/-! # Stopping and cutting off preserve UCP convergence

The event bounds hold for arbitrary possibly infinite random times, even without
a stopping-time hypothesis. The evaluation time of a stopped process is always finite.
-/

@[expose] public section

open MeasureTheory Filter Set
open scoped NNReal ENNReal Topology

namespace ProbabilityTheory

variable {Ω ι : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} {l : Filter ι}
  {X : ι → ℝ≥0 → Ω → ℝ} {Y : ℝ≥0 → Ω → ℝ}

namespace TendstoUCP
theorem _root_.Prove2MeSourceProof.h_6e9bb4c834a1b44d569cca8b (h : TendstoUCP P X l Y) (τ : Ω → WithTop ℝ≥0) :
    TendstoUCP P (fun i ↦ stoppedProcess (X i) τ) l (stoppedProcess Y τ) := by
  apply _root_.Prove2MeSourceProof.h_c85f5070e7769bac711d7f66.mpr
  intro T ε hε
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds
    (_root_.Prove2MeSourceProof.h_c85f5070e7769bac711d7f66.mp h T ε hε) (fun _ ↦ bot_le)
  intro i
  apply measure_mono
  rintro ω ⟨t, ht, hω⟩
  cases hτ : τ ω with
  | top =>
    refine ⟨t, ht, ?_⟩
    simpa only [MeasureTheory.stoppedProcess, hτ, min_eq_left le_top,
      WithTop.untopA, WithTop.untopD_coe] using hω
  | coe S =>
    refine ⟨min t S, (min_le_left _ _).trans ht, ?_⟩
    simpa only [MeasureTheory.stoppedProcess, hτ, ← WithTop.coe_min,
      WithTop.untopA, WithTop.untopD_coe] using hω
end TendstoUCP

end ProbabilityTheory


