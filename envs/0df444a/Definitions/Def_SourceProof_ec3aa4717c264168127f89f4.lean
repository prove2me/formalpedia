-- Prove2me | Definitions.Def_SourceProof_ec3aa4717c264168127f89f4
-- name    : SourceProof_ec3aa4717c264168127f89f4
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-25T17:41:39.80128+00:00
-- url     : https://prove2.me/theorems/60eb8b96-21a5-43e0-8d4f-c1f88b7c0787
-- title:
--   StochLean source theorem: ProbabilityTheory.tendstoUCP_of_ae_compactDeviation

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

theorem _root_.Prove2MeSourceProof.h_ec3aa4717c264168127f89f4 [IsFiniteMeasure P]
    {X : ℕ → ℝ≥0 → Ω → ℝ} {Y : ℝ≥0 → Ω → ℝ}
    (hm : ∀ n T, Measurable (compactDeviation (X n) Y T))
    (hXY : ∀ᵐ ω ∂P, ∀ T, Tendsto (fun n ↦ compactDeviation (X n) Y T ω) atTop (𝓝 0)) :
    TendstoUCP P X atTop Y := by
  intro T ε hε
  have h := tendsto_measure_of_ae_tendsto_indicator_of_isFiniteMeasure
    (μ := P) (As := fun n ↦ {ω | ε ≤ ProbabilityTheory.compactDeviation (X n) Y T ω})
    atTop (A := ∅) MeasurableSet.empty
    (fun n ↦ measurableSet_le measurable_const (hm n T))
    (hXY.mono fun ω hω ↦ ((hω T).eventually_lt_const hε).mono fun n hn ↦ by
      exact iff_of_false (not_le_of_gt hn) (Set.notMem_empty ω))
  simpa only [measure_empty] using h
end ProbabilityTheory


