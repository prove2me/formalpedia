-- Prove2me | Definitions.Def_SourceProof_33622c9aa55480ec75c122c4
-- name    : SourceProof_33622c9aa55480ec75c122c4
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-24T21:47:53.556403+00:00
-- url     : https://prove2.me/theorems/1c339ce6-655c-4d5c-a159-3a16ee1727a1
-- title:
--   StochLean source theorem: ProbabilityTheory.HasMonotonePaths.stoppedProcess

import Definitions.Def_StochLean_Probability_Process_Path_Monotone_F000
import Mathlib.Probability.Martingale.Basic
import Mathlib.Probability.Process.Stopping

/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/

/-! # Integrable adapted increasing processes are submartingales -/

@[expose] public section

open MeasureTheory Filter Set
open scoped NNReal

namespace ProbabilityTheory

namespace HasMonotonePaths
theorem _root_.Prove2MeSourceProof.h_33622c9aa55480ec75c122c4 {Ω : Type*} {mΩ : MeasurableSpace Ω}
    {P : Measure Ω} {X : ℝ≥0 → Ω → ℝ}
    (hX : HasMonotonePaths X P) (τ : Ω → WithTop ℝ≥0) :
    HasMonotonePaths (stoppedProcess X τ) P := by
  filter_upwards [hX] with ω hω s t hst
  cases ht : τ ω with
  | top => simpa only [MeasureTheory.stoppedProcess, ht, min_eq_left le_top,
      WithTop.untopA, WithTop.untopD_coe] using hω hst
  | coe u => simpa only [MeasureTheory.stoppedProcess, ht, ← WithTop.coe_min,
      WithTop.untopA, WithTop.untopD_coe] using hω (min_le_min_right u hst)
end HasMonotonePaths

end ProbabilityTheory


