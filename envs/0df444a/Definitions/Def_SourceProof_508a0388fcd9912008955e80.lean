-- Prove2me | Definitions.Def_SourceProof_508a0388fcd9912008955e80
-- name    : SourceProof_508a0388fcd9912008955e80
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-24T21:58:16.098024+00:00
-- url     : https://prove2.me/theorems/d7b3fa30-5d5d-40da-a7b6-1bf7b48e704c
-- title:
--   StochLean source theorem: ProbabilityTheory.HasIntegrableVariation.congr

import Definitions.Def_StochLean_Probability_Process_FiniteVariation_Integrable_F000

/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/

/-! # Integrable variation on the whole half-line

The variation owner is Mathlib's `eVariationOn`, not a new terminal process.
Finiteness almost surely is an explicit part of the predicate: integrability
of `toReal` alone would incorrectly accept infinite variation, since that
conversion sends infinity to zero.

Adaptedness, cadlag paths, and the zero initial value in Protter's normalized
FV convention are separate hypotheses. In particular an arbitrary random
process constant in time has zero variation, even without a measurable or
integrable initial value. This module does not define local integrable
variation or choose a terminal limit of the process.
-/

@[expose] public section

open MeasureTheory Set
open scoped NNReal ENNReal

namespace ProbabilityTheory

variable {Ω : Type*} {mΩ : MeasurableSpace Ω}

variable {X Y : ℝ≥0 → Ω → ℝ} {P : Measure Ω}

namespace HasIntegrableVariation
theorem _root_.Prove2MeSourceProof.h_508a0388fcd9912008955e80 (hX : HasIntegrableVariation X P)
    (hXY : Indistinguishable X Y P) : HasIntegrableVariation Y P := by
  constructor
  · filter_upwards [hX.1, hXY] with ω hω hXYω
    simpa only [hXYω] using hω
  · apply hX.2.congr
    filter_upwards [hXY] with ω hω
    simp only [hω]
end HasIntegrableVariation

end ProbabilityTheory


