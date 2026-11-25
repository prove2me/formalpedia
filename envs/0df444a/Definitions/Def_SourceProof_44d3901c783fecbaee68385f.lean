-- Prove2me | Definitions.Def_SourceProof_44d3901c783fecbaee68385f
-- name    : SourceProof_44d3901c783fecbaee68385f
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-25T12:44:38.318042+00:00
-- url     : https://prove2.me/theorems/12e3ff73-cede-447d-94ee-15242620154d
-- title:
--   StochLean source theorem: ProbabilityTheory.isCagladPath_cutoffIntegrand

import Definitions.Def_StochLean_Probability_Process_Stopping_Integrand_F000
import Definitions.Def_SourceProof_bdc784f4a82031949787bf4c

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

theorem _root_.Prove2MeSourceProof.h_44d3901c783fecbaee68385f {H : ℝ≥0 → Ω → ℝ}
    (hH : ∀ ω, IsCagladPath (fun t ↦ H t ω)) (τ : Ω → WithTop ℝ≥0) (ω : Ω) :
    IsCagladPath (fun t ↦ cutoffIntegrand H τ t ω) := by
  cases hτ : τ ω with
  | top => simpa only [ProbabilityTheory.cutoffIntegrand, hτ, le_top, if_true] using hH ω
  | coe T =>
      have h := (_root_.Prove2MeSourceProof.h_bdc784f4a82031949787bf4c (hH ω)) T
      change ProbabilityTheory.IsCagladPath (fun t ↦ if t ≤ T then H t ω else 0) at h
      simpa only [ProbabilityTheory.cutoffIntegrand, hτ, WithTop.coe_le_coe] using h
end ProbabilityTheory


