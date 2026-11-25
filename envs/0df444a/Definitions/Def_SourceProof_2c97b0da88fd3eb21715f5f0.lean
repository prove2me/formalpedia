-- Prove2me | Definitions.Def_SourceProof_2c97b0da88fd3eb21715f5f0
-- name    : SourceProof_2c97b0da88fd3eb21715f5f0
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-25T19:17:57.424265+00:00
-- url     : https://prove2.me/theorems/a8d5e22a-6a4d-4614-8bba-169383a04695
-- title:
--   StochLean source theorem: ProbabilityTheory.IsLocalMartingale.stoppedProcess

import Definitions.Def_SourceProof_1557efb7e848f4cf57c0170c
import Definitions.Def_SourceProof_7e41a7708f0759111a0ce622
import Definitions.Def_SourceProof_9f2f3563711c68b81e63664c
import Definitions.Def_SourceProof_aa372c8273bcd3cd6307f406
import Definitions.Def_SourceProof_d758c5fe1bf7eec6f7a3ad7f
import Mathlib.Probability.Martingale.Convergence

/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/

/-!
# Stopping and linear stability of Protter local martingales

Fundamental sequences are actual witnesses. A shared localizer is the pointwise
minimum of two existing localizers. Its time-zero mask is the intersection of
their masks; the unmasked Klenke definition is not silently substituted.

Source: Protter I.48 (stopping and linear operations).
-/

@[expose] public section

open MeasureTheory Filter Set
open scoped NNReal ENNReal Topology

namespace ProbabilityTheory

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {F : Filtration ℝ≥0 mΩ}
  {P : Measure Ω} {X Y : ℝ≥0 → Ω → ℝ} [IsFiniteMeasure P]

namespace IsLocalMartingale
theorem _root_.Prove2MeSourceProof.h_2c97b0da88fd3eb21715f5f0 (hX : IsLocalMartingale X F P)
    (hF : F.IsUsual P) {σ : Ω → WithTop ℝ≥0} (hσ : IsStoppingTime F σ) :
    IsLocalMartingale (MeasureTheory.stoppedProcess X σ) F P := by
  refine ⟨((_root_.Prove2MeSourceProof.h_d758c5fe1bf7eec6f7a3ad7f hX.1.stronglyAdapted) hF (_root_.Prove2MeSourceProof.h_9f2f3563711c68b81e63664c hX.2.1)
    hσ).adapted, (_root_.Prove2MeSourceProof.h_1557efb7e848f4cf57c0170c hX.2.1) σ, ?_⟩
  obtain ⟨τ, hτ⟩ := hX.2.2
  refine ⟨τ, hτ.1, hτ.2.1, fun n ↦ ?_⟩
  have hr := (_root_.Prove2MeSourceProof.h_9f2f3563711c68b81e63664c ((_root_.Prove2MeSourceProof.h_1557efb7e848f4cf57c0170c ((_root_.Prove2MeSourceProof.h_7e41a7708f0759111a0ce622 hX.2.1) {ω | 0 < τ n ω})) (τ n)))
  have hstop := (_root_.Prove2MeSourceProof.h_aa372c8273bcd3cd6307f406 (hτ.2.2 n)) hF hr hσ
  simpa only [← stoppedProcess_indicator_comm', stoppedProcess_stoppedProcess, inf_comm]
    using hstop
end IsLocalMartingale

end ProbabilityTheory


