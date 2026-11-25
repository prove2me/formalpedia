-- Prove2me | Definitions.Def_SourceProof_91cbcdd434ea8c8e4843298e
-- name    : SourceProof_91cbcdd434ea8c8e4843298e
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-25T16:14:08.023948+00:00
-- url     : https://prove2.me/theorems/afe01839-3dc6-5e8e-846a-10c7d539a970
-- title:
--   StochLean source theorem: ProbabilityTheory.isTotalSemimartingale_const_initial

import Definitions.Def_StochLean_Probability_Process_Semimartingale_Basic_F001
import Definitions.Def_SourceProof_079b841d0081fb5cbd939ad6

/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/

/-!
# Semimartingales as good integrators

The canonical predicate is zero-sequential continuity of the elementary
integral for uniform convergence in `(t,ω)`. The epsilon/delta source
continuity criterion is proved equivalent. Classical decompositions are not
part of this definition. This file does not select a stochastic integral for
general caglad integrands or a quadratic variation.
-/

@[expose] public section

open MeasureTheory Filter Set
open scoped NNReal ENNReal Topology

namespace ProbabilityTheory

variable {Ω : Type*} {mΩ : MeasurableSpace Ω}

variable {X : ℝ≥0 → Ω → ℝ} {F : Filtration ℝ≥0 mΩ} {P : Measure Ω}

theorem _root_.Prove2MeSourceProof.h_91cbcdd434ea8c8e4843298e [IsFiniteMeasure P] {Z : Ω → ℝ}
    (hZ : Measurable[F 0] Z) : IsTotalSemimartingale (fun _ : ℝ≥0 ↦ Z) F P := by
  refine ⟨fun t ↦ hZ.mono (F.mono bot_le) le_rfl, ?_,
    _root_.Prove2MeSourceProof.h_079b841d0081fb5cbd939ad6 (hZ.mono (F.le 0) le_rfl)⟩
  apply ae_of_all
  intro ω
  exact ⟨fun _ ↦ continuousWithinAt_const, fun _ _ ↦ ⟨Z ω, tendsto_const_nhds⟩⟩
end ProbabilityTheory


