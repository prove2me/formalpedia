-- Prove2me | Definitions.Def_SourceProof_f4d8a21bf210a12aba5a0fa0
-- name    : SourceProof_f4d8a21bf210a12aba5a0fa0
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-25T17:52:41.257915+00:00
-- url     : https://prove2.me/theorems/458a7316-7f6c-4dcc-ae00-3b4fc29691e6
-- title:
--   StochLean source theorem: ProbabilityTheory.isGoodIntegrator_zero

import Definitions.Def_StochLean_Probability_Process_Semimartingale_Basic_F000
import Definitions.Def_SourceProof_68823977c59f3c333b9b1272

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

theorem _root_.Prove2MeSourceProof.h_f4d8a21bf210a12aba5a0fa0 (F : Filtration ℝ≥0 mΩ) (P : Measure Ω) :
    IsGoodIntegrator (0 : ℝ≥0 → Ω → ℝ) F P := by
  intro H hH _
  simp only [_root_.Prove2MeSourceProof.h_68823977c59f3c333b9b1272]
  intro ε hε
  simp [not_le_of_gt hε]
end ProbabilityTheory


