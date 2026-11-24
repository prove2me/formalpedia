-- Prove2me | Definitions.Def_SourceProof_9c5e30e37c7ae3d824080fb0
-- name    : SourceProof_9c5e30e37c7ae3d824080fb0
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-24T22:15:37.969475+00:00
-- url     : https://prove2.me/theorems/3d0bcb1e-4338-4b5d-a1f3-a01fba5ee0a3
-- title:
--   StochLean source theorem: ProbabilityTheory.TendstoUCP.congr_right

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
theorem _root_.Prove2MeSourceProof.h_9c5e30e37c7ae3d824080fb0 (h : TendstoUCP P X l Y)
    (hYW : Indistinguishable Y W P) : TendstoUCP P X l W := by
  intro T ε hε
  have heq : (fun i ↦ P {ω | ε ≤ ProbabilityTheory.compactDeviation (X i) Y T ω}) =
      fun i ↦ P {ω | ε ≤ ProbabilityTheory.compactDeviation (X i) W T ω} := by
    funext i
    apply measure_congr
    filter_upwards [hYW] with ω hω
    change (ε ≤ ProbabilityTheory.compactDeviation (X i) Y T ω) = (ε ≤ ProbabilityTheory.compactDeviation (X i) W T ω)
    simp only [ProbabilityTheory.compactDeviation, hω]
  rw [← heq]
  exact h T ε hε
end TendstoUCP

end ProbabilityTheory


