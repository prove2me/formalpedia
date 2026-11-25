-- Prove2me | Definitions.Def_SourceProof_0f51da54d5b7a9d3fd68b580
-- name    : SourceProof_0f51da54d5b7a9d3fd68b580
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-25T19:17:51.96552+00:00
-- url     : https://prove2.me/theorems/e450c126-f5e0-4c1a-ae41-ba16ea84f2b4
-- title:
--   StochLean source theorem: MeasureTheory.Martingale.condExp_weighted_finiteStoppingTime_increment_min

import Definitions.Def_StochLean_Probability_Process_Filtration_Usual_F001
import Definitions.Def_StochLean_Probability_Process_Path_RightContinuous_F000
import Definitions.Def_StochLean_Probability_Process_Stopping_Finite_F004
import Definitions.Def_SourceProof_29d33b95cf42be6716ddb60d
import Definitions.Def_SourceProof_4a90e1998d81dac996f193f9
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.MeasureTheory.Function.ConditionalExpectation.Indicator
import Mathlib.MeasureTheory.Function.ConditionalExpectation.PullOut
import Mathlib.MeasureTheory.Function.ConditionalExpectation.Real
import Mathlib.MeasureTheory.Function.Floor
import Mathlib.MeasureTheory.Function.UniformIntegrable
import Mathlib.Probability.Martingale.Basic
import Mathlib.Probability.Martingale.OptionalSampling
import Mathlib.Probability.Process.Adapted
import Mathlib.Probability.Process.LocalProperty

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

theorem _root_.Prove2MeSourceProof.h_0f51da54d5b7a9d3fd68b580
    (hX : Martingale X F P) (hF : F.IsUsual P) (hr : HasRightContinuousPaths X P)
    (α β : FiniteStoppingTime F) (hαβ : ∀ ω, α ω ≤ β ω) (T : ℝ≥0)
    {Z : Ω → ℝ} (hZ : Measurable[α.measurableSpace] Z)
    (C : ℝ) (hb : ∀ᵐ ω ∂P, ‖Z ω‖ ≤ C) :
    P[fun ω ↦ Z ω * (X (min (β ω) T) ω - X (min (α ω) T) ω) |
      α.measurableSpace] =ᵐ[P] 0 := by
  let A : Ω → ℝ := fun ω ↦ X (min (α ω) T) ω
  let B : Ω → ℝ := fun ω ↦ X (min (β ω) T) ω
  have hA : A =ᵐ[P] P[X T | α.measurableSpace] :=
    (_root_.Prove2MeSourceProof.h_29d33b95cf42be6716ddb60d hX) hF hr α T
  have hB : B =ᵐ[P] P[X T | β.measurableSpace] :=
    (_root_.Prove2MeSourceProof.h_29d33b95cf42be6716ddb60d hX) hF hr β T
  have hiA : Integrable A P := integrable_condExp.congr hA.symm
  have hiB : Integrable B P := integrable_condExp.congr hB.symm
  have hle : α.measurableSpace ≤ β.measurableSpace :=
    α.isStoppingTime.measurableSpace_mono β.isStoppingTime
      (fun ω ↦ WithTop.coe_le_coe.mpr (hαβ ω))
  have hd : P[B - A | α.measurableSpace] =ᵐ[P] 0 := by
    calc
      P[B - A | α.measurableSpace] =ᵐ[P]
          P[B | α.measurableSpace] - P[A | α.measurableSpace] := condExp_sub hiB hiA _
      _ =ᵐ[P] P[X T | α.measurableSpace] - P[X T | α.measurableSpace] :=
        ((condExp_congr_ae hB).trans (condExp_condExp_of_le hle (_root_.Prove2MeSourceProof.h_4a90e1998d81dac996f193f9 β))).sub
          ((condExp_congr_ae hA).trans
            (condExp_condExp_of_le le_rfl (_root_.Prove2MeSourceProof.h_4a90e1998d81dac996f193f9 α)))
      _ = 0 := sub_self _
  have hiZ : Integrable (Z * (B - A)) P :=
    (hiB.sub hiA).bdd_smul C (hZ.mono (_root_.Prove2MeSourceProof.h_4a90e1998d81dac996f193f9 α) le_rfl).aestronglyMeasurable hb
  have hout := condExp_mul_of_aestronglyMeasurable_left hZ.aestronglyMeasurable hiZ (hiB.sub hiA)
  filter_upwards [hout, hd] with ω houtω hdω
  change P[Z * (B - A) | α.measurableSpace] ω = 0
  rw [houtω]
  change Z ω * P[B - A | α.measurableSpace] ω = 0
  rw [hdω, Pi.zero_apply, mul_zero]
end MeasureTheory.Martingale


