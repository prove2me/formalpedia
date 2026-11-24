-- Prove2me | Definitions.Def_SourceProof_53d90595c026ce14255ca40b
-- name    : SourceProof_53d90595c026ce14255ca40b
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-24T22:15:28.557639+00:00
-- url     : https://prove2.me/theorems/d1a795be-0c68-40e7-a765-e47cc2b363f9
-- title:
--   StochLean source theorem: ProbabilityTheory.tendstoUCP_of_ae_compactDeviation_of_aemeasurable

import Definitions.Def_StochLean_Probability_Process_UCP_F001
import Mathlib.MeasureTheory.Integral.Indicator
import Mathlib.Order.Filter.AtTopBot.CountablyGenerated

/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/

/-! # Uniform path convergence and a subsequence criterion for UCP

Measurability of the output compact deviations is explicit in the converse.
No continuity of an outer measure on arbitrary decreasing sets is used.
-/

@[expose] public section

open MeasureTheory Filter Set
open scoped NNReal ENNReal Topology

namespace ProbabilityTheory

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω}

theorem _root_.Prove2MeSourceProof.h_53d90595c026ce14255ca40b [IsFiniteMeasure P]
    {X : ℕ → ℝ≥0 → Ω → ℝ} {Y : ℝ≥0 → Ω → ℝ}
    (hm : ∀ n T, AEMeasurable (compactDeviation (X n) Y T) P)
    (hXY : ∀ᵐ ω ∂P, ∀ T, Tendsto (fun n ↦ compactDeviation (X n) Y T ω) atTop (𝓝 0)) :
    TendstoUCP P X atTop Y := by
  intro T ε hε
  let d (n : ℕ) := (hm n T).mk (ProbabilityTheory.compactDeviation (X n) Y T)
  have hd : ∀ᵐ ω ∂P, ∀ n, ProbabilityTheory.compactDeviation (X n) Y T ω = d n ω :=
    ae_all_iff.mpr (fun n ↦ (hm n T).ae_eq_mk)
  have hlim : ∀ᵐ ω ∂P, Tendsto (fun n ↦ d n ω) atTop (𝓝 0) := by
    filter_upwards [hd, hXY] with ω hdω hω
    simpa only [hdω] using hω T
  have h := tendsto_measure_of_ae_tendsto_indicator_of_isFiniteMeasure
    (μ := P) (As := fun n ↦ {ω | ε ≤ d n ω})
    atTop (A := ∅) MeasurableSet.empty
    (fun n ↦ measurableSet_le measurable_const (hm n T).measurable_mk)
    (hlim.mono fun ω hω ↦ (hω.eventually_lt_const hε).mono fun n hn ↦ by
      exact iff_of_false (not_le_of_gt hn) (Set.notMem_empty ω))
  have heq (n : ℕ) : P {ω | ε ≤ ProbabilityTheory.compactDeviation (X n) Y T ω} = P {ω | ε ≤ d n ω} := by
    apply measure_congr
    filter_upwards [hd] with ω hω
    change (ε ≤ ProbabilityTheory.compactDeviation (X n) Y T ω) = (ε ≤ d n ω)
    rw [hω]
  simpa only [heq, measure_empty] using h
end ProbabilityTheory


