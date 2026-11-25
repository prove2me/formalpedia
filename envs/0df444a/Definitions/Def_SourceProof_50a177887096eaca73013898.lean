-- Prove2me | Definitions.Def_SourceProof_50a177887096eaca73013898
-- name    : SourceProof_50a177887096eaca73013898
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-25T19:06:23.042423+00:00
-- url     : https://prove2.me/theorems/9a662831-1039-5510-932e-54cef1b121a6
-- title:
--   StochLean source theorem: ProbabilityTheory.eVariationOn_univ_stoppedProcess_le

import Definitions.Def_SourceProof_407218b22ae1495f01bcf52b
import Definitions.Def_SourceProof_6da37c641e8d3b5ccb3dfebc
import Definitions.Def_SourceProof_c1f3beb58834c65ab1c84683

/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/

/-! # Whole-half-line variation after stopping

The actual extended variation of a stopped path is its variation up to the
stopping time, including the stopping endpoint. Infinite times use the
original whole-half-line variation through the existing terminal-valued
sampling owner. None of these pathwise statements require stopping-time
measurability, cadlag paths, or finite variation.
-/

@[expose] public section

open MeasureTheory StochLean Set
open scoped NNReal ENNReal

namespace ProbabilityTheory

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω}
  {X : ℝ≥0 → Ω → ℝ}


theorem _root_.Prove2MeSourceProof.h_50a177887096eaca73013898 (X : ℝ≥0 → Ω → ℝ)
    (τ : Ω → WithTop ℝ≥0) (ω : Ω) :
    eVariationOn (fun t ↦ stoppedProcess X τ t ω) univ ≤
      eVariationOn (X · ω) univ := by
  rw [_root_.Prove2MeSourceProof.h_c1f3beb58834c65ab1c84683]
  cases ht : τ ω with
  | top => rw [_root_.Prove2MeSourceProof.h_407218b22ae1495f01bcf52b ht]
  | coe T =>
      rw [_root_.Prove2MeSourceProof.h_6da37c641e8d3b5ccb3dfebc (ht ▸ WithTop.coe_ne_top)]
      simp only [stoppedValue, ht, WithTop.untopA, WithTop.untopD_coe, ProbabilityTheory.eTotalVariationProcess]
      exact eVariationOn.mono _ (subset_univ _)
end ProbabilityTheory


