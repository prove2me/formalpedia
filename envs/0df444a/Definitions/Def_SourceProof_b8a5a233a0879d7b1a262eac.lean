-- Prove2me | Definitions.Def_SourceProof_b8a5a233a0879d7b1a262eac
-- name    : SourceProof_b8a5a233a0879d7b1a262eac
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-25T19:23:05.985722+00:00
-- url     : https://prove2.me/theorems/2cfceb88-d053-4295-83f5-992bcfb242b2
-- title:
--   StochLean source theorem: MeasureTheory.Martingale.condExp_weighted_finiteStoppingTime_increment_min_of_le

import Definitions.Def_SourceProof_0f51da54d5b7a9d3fd68b580
import Definitions.Def_SourceProof_4a90e1998d81dac996f193f9

/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/

/-! # Bounded stopping-time coefficients and martingale increments

The martingale is capped at a deterministic horizon, but the two original
stopping endpoints may be unbounded. Coefficients are known at the left endpoint.
-/

@[expose] public section

open ProbabilityTheory Filter
open scoped NNReal ENNReal

namespace MeasureTheory.Martingale

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {F : Filtration ℝ≥0 mΩ}
  {P : Measure Ω} [IsFiniteMeasure P] [SigmaFiniteFiltration P F]
  {X : ℝ≥0 → Ω → ℝ}

theorem _root_.Prove2MeSourceProof.h_b8a5a233a0879d7b1a262eac
    (hX : Martingale X F P) (hF : F.IsUsual P) (hr : HasRightContinuousPaths X P)
    (α β : FiniteStoppingTime F) (hαβ : ∀ ω, α ω ≤ β ω) (T : ℝ≥0)
    {Z : Ω → ℝ} (hZ : Measurable[α.measurableSpace] Z)
    (C : ℝ) (hb : ∀ᵐ ω ∂P, ‖Z ω‖ ≤ C) {s : ℝ≥0} (hs : ∀ ω, s ≤ α ω) :
    P[fun ω ↦ Z ω * (X (min (β ω) T) ω - X (min (α ω) T) ω) | F s] =ᵐ[P] 0 := by
  have hle : F s ≤ α.measurableSpace := by
    have h := (isStoppingTime_const F s).measurableSpace_mono α.isStoppingTime
      (fun ω ↦ WithTop.coe_le_coe.mpr (hs ω))
    change (isStoppingTime_const F s).measurableSpace ≤ α.measurableSpace at h
    rw [IsStoppingTime.measurableSpace_const] at h
    exact h
  have hz := (_root_.Prove2MeSourceProof.h_0f51da54d5b7a9d3fd68b580 hX) hF hr α β hαβ T hZ C hb
  calc
    _ =ᵐ[P] P[P[fun ω ↦ Z ω * (X (min (β ω) T) ω - X (min (α ω) T) ω) |
      α.measurableSpace] | F s] := (condExp_condExp_of_le hle (_root_.Prove2MeSourceProof.h_4a90e1998d81dac996f193f9 α)).symm
    _ =ᵐ[P] P[(0 : Ω → ℝ) | F s] := condExp_congr_ae hz
    _ = 0 := condExp_zero
end MeasureTheory.Martingale


