-- Prove2me | Definitions.Def_SourceProof_87f0a7a067d30089e512c6db
-- name    : SourceProof_87f0a7a067d30089e512c6db
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-24T22:15:19.709857+00:00
-- url     : https://prove2.me/theorems/6d412938-04af-4ffd-9ec1-4e97fde71f57
-- title:
--   StochLean source theorem: ProbabilityTheory.TendstoUCP.congr_left

import Definitions.Def_StochLean_Probability_Process_UCP_F001

/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/

/-! # Linear operations and indistinguishable changes in UCP

These statements use the canonical UCP owner and outer-measure event bounds.
No additional path measurability or regularity assumptions are necessary.
-/

@[expose] public section

open MeasureTheory Filter Set
open scoped NNReal ENNReal Topology

namespace ProbabilityTheory

variable {Ω ι : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} {l : Filter ι}
  {X Z : ι → ℝ≥0 → Ω → ℝ} {Y W : ℝ≥0 → Ω → ℝ}

namespace TendstoUCP
theorem _root_.Prove2MeSourceProof.h_87f0a7a067d30089e512c6db (h : TendstoUCP P X l Y)
    (hXZ : ∀ i, Indistinguishable (X i) (Z i) P) : TendstoUCP P Z l Y := by
  intro T ε hε
  have heq : (fun i ↦ P {ω | ε ≤ ProbabilityTheory.compactDeviation (X i) Y T ω}) =
      fun i ↦ P {ω | ε ≤ ProbabilityTheory.compactDeviation (Z i) Y T ω} := by
    funext i
    apply measure_congr
    filter_upwards [hXZ i] with ω hω
    change (ε ≤ ProbabilityTheory.compactDeviation (X i) Y T ω) = (ε ≤ ProbabilityTheory.compactDeviation (Z i) Y T ω)
    simp only [ProbabilityTheory.compactDeviation, hω]
  rw [← heq]
  exact h T ε hε
end TendstoUCP

end ProbabilityTheory


