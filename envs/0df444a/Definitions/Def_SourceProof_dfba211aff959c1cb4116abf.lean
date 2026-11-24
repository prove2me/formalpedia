-- Prove2me | Definitions.Def_SourceProof_dfba211aff959c1cb4116abf
-- name    : SourceProof_dfba211aff959c1cb4116abf
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-24T23:01:51.504282+00:00
-- url     : https://prove2.me/theorems/ec3f24e9-b417-43dc-b9c6-860e7aa4d6ab
-- title:
--   StochLean source theorem: ProbabilityTheory.adapted_cutoffIntegrand

import Definitions.Def_StochLean_Probability_Process_Stopping_Integrand_F000

/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/

/-! # Cutting an integrand off after a stopping time

Unlike a stopped process, the cutoff is zero strictly after the stopping time.
The closed endpoint preserves the stopping jump and the initial value.
-/

@[expose] public section

open MeasureTheory Filter Set
open scoped NNReal Topology

namespace ProbabilityTheory

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {F : Filtration ℝ≥0 mΩ}

theorem _root_.Prove2MeSourceProof.h_dfba211aff959c1cb4116abf {H : ℝ≥0 → Ω → ℝ} (hH : Adapted F H)
    {τ : Ω → WithTop ℝ≥0} (hτ : IsStoppingTime F τ) : Adapted F (cutoffIntegrand H τ) :=
  fun t ↦ Measurable.ite (hτ.measurableSet_ge t) (hH t) measurable_const
end ProbabilityTheory


