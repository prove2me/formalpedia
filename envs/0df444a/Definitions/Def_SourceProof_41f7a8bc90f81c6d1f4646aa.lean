-- Prove2me | Definitions.Def_SourceProof_41f7a8bc90f81c6d1f4646aa
-- name    : SourceProof_41f7a8bc90f81c6d1f4646aa
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-24T23:21:26.338145+00:00
-- url     : https://prove2.me/theorems/8bbb5f69-3e6e-43fd-85b9-ff8c384f9474
-- title:
--   StochLean source theorem: ProbabilityTheory.tendstoUCP_min_of_ae_tendsto_atTop

import Definitions.Def_StochLean_Probability_Process_Partition_F001
import Definitions.Def_SourceProof_c85f5070e7769bac711d7f66
import Mathlib.MeasureTheory.Integral.Indicator

/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/

/-! # UCP exhaustion by finite stopping endpoints

On each compact interval, stopping eventually changes nothing on almost every
path. Measurable endpoint events bound the possibly nonmeasurable deviation
events, so no regularity or measurability assumption on the process is needed.
-/

@[expose] public section

open MeasureTheory Filter Set
open scoped NNReal Topology

namespace ProbabilityTheory

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsFiniteMeasure P]

theorem _root_.Prove2MeSourceProof.h_41f7a8bc90f81c6d1f4646aa {τ : ℕ → Ω → ℝ≥0}
    (hm : ∀ n (T : ℝ≥0), MeasurableSet {ω | τ n ω < T})
    (hτ : ∀ᵐ ω ∂P, Tendsto (fun n ↦ τ n ω) atTop atTop) (X : ℝ≥0 → Ω → ℝ) :
    TendstoUCP P (fun n t ω ↦ X (min (τ n ω) t) ω) atTop X := by
  apply _root_.Prove2MeSourceProof.h_c85f5070e7769bac711d7f66.mpr
  intro T ε hε
  have hbad : Tendsto (fun n ↦ P {ω | τ n ω < T}) atTop (𝓝 0) := by
    have h := tendsto_measure_of_ae_tendsto_indicator_of_isFiniteMeasure
      (μ := P) (As := fun n ↦ {ω | τ n ω < T}) atTop (A := ∅)
      MeasurableSet.empty (fun n ↦ hm n T) (hτ.mono fun ω hω ↦ ?_)
    · simpa only [measure_empty] using h
    · filter_upwards [hω.eventually (eventually_ge_atTop T)] with n hn
      exact iff_of_false (not_lt_of_ge hn) (Set.notMem_empty ω)
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hbad (fun _ ↦ bot_le)
  intro n
  apply measure_mono
  rintro ω ⟨t, ht, hω⟩
  by_contra hn
  have htn : t ≤ τ n ω := ht.trans (le_of_not_gt hn)
  rw [min_eq_right htn, sub_self, norm_zero] at hω
  exact (not_lt_of_ge hε.le) hω
end ProbabilityTheory


