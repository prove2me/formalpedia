-- Prove2me | Definitions.Def_SourceProof_f275ad31254934483f67a202
-- name    : SourceProof_f275ad31254934483f67a202
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-25T17:51:30.320801+00:00
-- url     : https://prove2.me/theorems/c577ae32-7b69-4d99-a1a6-458b3cc49d32
-- title:
--   StochLean source theorem: MeasureTheory.hittingAfter_mem_closure_of_rightContinuous

import Definitions.Def_StochLean_Probability_Process_Path_RightContinuous_F000
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

/-! # Open-set hitting times for right-continuous processes

The owner is Mathlib's `hittingAfter`. Open hits strictly before a deterministic time
are detected on a fixed countable dense grid. Right continuity of the filtration then
gives the stopping-time property. At a finite hit the path belongs to the closure of
the target, not necessarily the open target itself.
-/

@[expose] public section

open MeasureTheory Filter Set TopologicalSpace
open scoped NNReal Topology

namespace ProbabilityTheory

variable {E : Type*} [TopologicalSpace E]

end ProbabilityTheory

namespace MeasureTheory

variable {Ω E : Type*} [TopologicalSpace E] {X : ℝ≥0 → Ω → E}


theorem _root_.Prove2MeSourceProof.h_f275ad31254934483f67a202 {s : Set E} {a : ℝ≥0} {ω : Ω}
    (hX : ProbabilityTheory.IsRightContinuousPath (X · ω))
    (hne : hittingAfter X s a ω ≠ ⊤) :
    X (hittingAfter X s a ω).untopA ω ∈ closure s := by
  classical
  have hex : ∃ t, a ≤ t ∧ X t ω ∈ s := by
    simpa only [ne_eq, hittingAfter_eq_top_iff, not_forall, not_not, exists_prop] using hne
  let S : Set ℝ≥0 := {t | a ≤ t ∧ X t ω ∈ s}
  have hS : S.Nonempty := hex
  have hbelow : BddBelow S := ⟨0, fun _ _ ↦ bot_le⟩
  obtain ⟨u, _, hlim, hu⟩ := exists_seq_tendsto_sInf hS hbelow
  have hwithin : Tendsto u atTop (𝓝[≥] sInf S) :=
    tendsto_nhdsWithin_iff.mpr
      ⟨hlim, Eventually.of_forall fun n ↦ csInf_le hbelow (hu n)⟩
  have hxu : Tendsto (fun n ↦ X (u n) ω) atTop (𝓝 (X (sInf S) ω)) :=
    (hX (sInf S)).tendsto.comp hwithin
  have hmem : X (sInf S) ω ∈ closure s :=
    isClosed_closure.mem_of_tendsto hxu (Eventually.of_forall fun n ↦ subset_closure (hu n).2)
  rw [hittingAfter, if_pos hex]
  exact hmem
variable {mΩ : MeasurableSpace Ω} [MeasurableSpace E] [OpensMeasurableSpace E]
  {F : Filtration ℝ≥0 mΩ}

end MeasureTheory


