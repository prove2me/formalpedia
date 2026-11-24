-- Prove2me | Definitions.Def_SourceProof_80ab6b03444941f707fbb65e
-- name    : SourceProof_80ab6b03444941f707fbb65e
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-24T23:45:38.7349+00:00
-- url     : https://prove2.me/theorems/4a199a9d-f190-46ba-94e2-b9fa154caefb
-- title:
--   StochLean source theorem: ProbabilityTheory.IsSquareIntegrableMartingale.congr

import Definitions.Def_StochLean_Probability_Process_LocalMartingale_F000
import Definitions.Def_SourceProof_4a9b239e53ad8f8a45b491f1
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.MeasureTheory.Function.ConditionalExpectation.Real
import Mathlib.MeasureTheory.Function.Floor
import Mathlib.MeasureTheory.Measure.NullMeasurable
import Mathlib.Probability.Martingale.OptionalSampling
import Mathlib.Probability.Process.Adapted
import Mathlib.Probability.Process.Filtration
import Mathlib.Probability.Process.Stopping
import Mathlib.Topology.Algebra.Monoid

/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/

/-! # Initial masking and stability of finite-time L2 martingales

The stable local property includes common-event cadlag paths. No global second
moment bound is introduced.
-/

@[expose] public section

open MeasureTheory Set
open scoped NNReal ENNReal

namespace MeasureTheory.Martingale

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {F : Filtration ℝ≥0 mΩ}
  {P : Measure Ω} {X : ℝ≥0 → Ω → ℝ}

end MeasureTheory.Martingale

namespace ProbabilityTheory

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {F : Filtration ℝ≥0 mΩ}
  {P : Measure Ω} {X Y : ℝ≥0 → Ω → ℝ}

namespace IsSquareIntegrableMartingale
theorem _root_.Prove2MeSourceProof.h_80ab6b03444941f707fbb65e
    (hX : IsSquareIntegrableMartingale X F P) (ha : Adapted F Y)
    (heq : Indistinguishable X Y P) : IsSquareIntegrableMartingale Y F P :=
  ⟨hX.1.congr ha.stronglyAdapted (_root_.Prove2MeSourceProof.h_4a9b239e53ad8f8a45b491f1 heq), fun t ↦ (hX.2 t).ae_eq ((_root_.Prove2MeSourceProof.h_4a9b239e53ad8f8a45b491f1 heq) t)⟩
end IsSquareIntegrableMartingale

end ProbabilityTheory


