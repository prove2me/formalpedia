-- Prove2me | Definitions.Def_SourceProof_079b841d0081fb5cbd939ad6
-- name    : SourceProof_079b841d0081fb5cbd939ad6
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-25T14:34:09.947226+00:00
-- url     : https://prove2.me/theorems/812e282f-0d89-4715-9b91-8152173d962e
-- title:
--   StochLean source theorem: ProbabilityTheory.isGoodIntegrator_const_initial

import Definitions.Def_StochLean_Probability_Process_Semimartingale_Basic_F000
import Definitions.Def_SourceProof_2de3ac64de8bd31f1d59bd9f
import Definitions.Def_SourceProof_c7146fcba0ddaff31080bf76

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


theorem _root_.Prove2MeSourceProof.h_079b841d0081fb5cbd939ad6 [IsFiniteMeasure P] {Z : Ω → ℝ}
    (hZ : Measurable Z) : IsGoodIntegrator (fun _ : ℝ≥0 ↦ Z) F P := by
  intro H hH hu
  simp only [_root_.Prove2MeSourceProof.h_c7146fcba0ddaff31080bf76]
  apply tendstoInMeasure_of_tendsto_ae
  · intro n
    exact (((_root_.Prove2MeSourceProof.h_2de3ac64de8bd31f1d59bd9f (hH n)).mono (F.le 0) le_rfl).mul hZ).aestronglyMeasurable
  · apply ae_of_all
    intro ω
    simpa only [zero_mul, Pi.zero_apply] using (hu.tendsto_at (0, ω)).mul_const (Z ω)
end ProbabilityTheory


