-- Prove2me | Definitions.Def_SourceProof_679fbec7203cd0a8616c5964
-- name    : SourceProof_679fbec7203cd0a8616c5964
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-19T21:52:42.408932+00:00
-- url     : https://prove2.me/theorems/669aaf35-af06-44b0-a476-9f0be3fd77d1
-- title:
--   LevyStochCalc source proof: LevyStochCalc.Brownian.Ito.ae_eq_add_of_sq_distances
-- statement:
--   Auxiliary theorem proved in the original LevyStochCalc source. Its proof and dependencies are retained verbatim from the certified extraction.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Brownian_ItoLinear_F000

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# Additivity of the L² Itô integral in the integrand

The Itô isometry and the isometry of differences determine every squared `L²`-distance among
`∫ H₁ dW`, `∫ H₂ dW` and `∫ (H₁ + H₂) dW` in terms of the energies of `H₁`, `H₂`, `H₁ + H₂` and
`H₁ − H₂`. The parallelogram law for those energies then forces
`∫ (H₁ + H₂) dW = ∫ H₁ dW + ∫ H₂ dW` almost everywhere.
-/

namespace LevyStochCalc.Brownian.Ito

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

universe u

variable {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]

section Energy

variable {H₁ H₂ : Ω → ℝ → ℝ}

end Energy

section Parallelogram

omit [IsProbabilityMeasure P] in

theorem _root_.Prove2MeSourceProof.h_679fbec7203cd0a8616c5964 {u v w : Ω → ℝ}
    (hu : MemLp u 2 P) (hv : MemLp v 2 P) (hw : MemLp w 2 P) {A B C D : ℝ≥0∞}
    (hA : A ≠ ⊤) (hB : B ≠ ⊤) (hC : C ≠ ⊤) (hD : D ≠ ⊤)
    (hSu : ∫⁻ ω, (‖u ω‖₊ : ℝ≥0∞) ^ 2 ∂P = A)
    (hSv : ∫⁻ ω, (‖v ω‖₊ : ℝ≥0∞) ^ 2 ∂P = B)
    (hSw : ∫⁻ ω, (‖w ω‖₊ : ℝ≥0∞) ^ 2 ∂P = C)
    (hSwu : ∫⁻ ω, (‖w ω - u ω‖₊ : ℝ≥0∞) ^ 2 ∂P = B)
    (hSwv : ∫⁻ ω, (‖w ω - v ω‖₊ : ℝ≥0∞) ^ 2 ∂P = A)
    (hSuv : ∫⁻ ω, (‖u ω - v ω‖₊ : ℝ≥0∞) ^ 2 ∂P = D)
    (hpar : C + D = 2 * A + 2 * B) :
    w =ᵐ[P] fun ω => u ω + v ω := by
  have eu : ∫ ω, u ω ^ 2 ∂P = A.toReal := by
    rw [LevyStochCalc.Brownian.Ito.integral_sq_eq_toReal hu.aestronglyMeasurable, hSu]
  have ev : ∫ ω, v ω ^ 2 ∂P = B.toReal := by
    rw [LevyStochCalc.Brownian.Ito.integral_sq_eq_toReal hv.aestronglyMeasurable, hSv]
  have ew : ∫ ω, w ω ^ 2 ∂P = C.toReal := by
    rw [LevyStochCalc.Brownian.Ito.integral_sq_eq_toReal hw.aestronglyMeasurable, hSw]
  have ewu : ∫ ω, (w ω - u ω) ^ 2 ∂P = B.toReal := by
    rw [LevyStochCalc.Brownian.Ito.integral_sq_eq_toReal (X := fun ω => w ω - u ω)
      (hw.aestronglyMeasurable.sub hu.aestronglyMeasurable), hSwu]
  have ewv : ∫ ω, (w ω - v ω) ^ 2 ∂P = A.toReal := by
    rw [LevyStochCalc.Brownian.Ito.integral_sq_eq_toReal (X := fun ω => w ω - v ω)
      (hw.aestronglyMeasurable.sub hv.aestronglyMeasurable), hSwv]
  have euv : ∫ ω, (u ω - v ω) ^ 2 ∂P = D.toReal := by
    rw [LevyStochCalc.Brownian.Ito.integral_sq_eq_toReal (X := fun ω => u ω - v ω)
      (hu.aestronglyMeasurable.sub hv.aestronglyMeasurable), hSuv]
  have hreal : C.toReal + D.toReal = 2 * A.toReal + 2 * B.toReal := by
    have h := congrArg ENNReal.toReal hpar
    rwa [ENNReal.toReal_add hC hD,
      ENNReal.toReal_add (ENNReal.mul_ne_top (by simp) hA) (ENNReal.mul_ne_top (by simp) hB),
      ENNReal.toReal_mul, ENNReal.toReal_mul,
      show ((2 : ℝ≥0∞)).toReal = (2 : ℝ) by simp] at h
  have hF : Integrable (fun ω => (w ω - u ω - v ω) ^ 2) P :=
    LevyStochCalc.Brownian.Ito.integrable_sq_of_memLp ((hw.sub hu).sub hv)
  have hW : Integrable (fun ω => w ω ^ 2) P := LevyStochCalc.Brownian.Ito.integrable_sq_of_memLp hw
  have hUV : Integrable (fun ω => (u ω - v ω) ^ 2) P := LevyStochCalc.Brownian.Ito.integrable_sq_of_memLp (hu.sub hv)
  have hU : Integrable (fun ω => u ω ^ 2) P := LevyStochCalc.Brownian.Ito.integrable_sq_of_memLp hu
  have hV : Integrable (fun ω => v ω ^ 2) P := LevyStochCalc.Brownian.Ito.integrable_sq_of_memLp hv
  have hWU : Integrable (fun ω => (w ω - u ω) ^ 2) P := LevyStochCalc.Brownian.Ito.integrable_sq_of_memLp (hw.sub hu)
  have hWV : Integrable (fun ω => (w ω - v ω) ^ 2) P := LevyStochCalc.Brownian.Ito.integrable_sq_of_memLp (hw.sub hv)
  have hkey : ∫ ω, (w ω - u ω - v ω) ^ 2 ∂P = 0 := by
    have hid : ∀ ω : Ω, (w ω - u ω - v ω) ^ 2 + w ω ^ 2 + (u ω - v ω) ^ 2
        = u ω ^ 2 + v ω ^ 2 + (w ω - u ω) ^ 2 + (w ω - v ω) ^ 2 := fun ω => by ring
    have heq : ∫ ω, ((w ω - u ω - v ω) ^ 2 + w ω ^ 2 + (u ω - v ω) ^ 2) ∂P
        = ∫ ω, (u ω ^ 2 + v ω ^ 2 + (w ω - u ω) ^ 2 + (w ω - v ω) ^ 2) ∂P :=
      integral_congr_ae (Filter.Eventually.of_forall hid)
    have hFW : Integrable (fun ω => (w ω - u ω - v ω) ^ 2 + w ω ^ 2) P := hF.add hW
    have hUV2 : Integrable (fun ω => u ω ^ 2 + v ω ^ 2) P := hU.add hV
    have hUV3 : Integrable (fun ω => u ω ^ 2 + v ω ^ 2 + (w ω - u ω) ^ 2) P := hUV2.add hWU
    rw [integral_add hFW hUV, integral_add hF hW,
      integral_add hUV3 hWV, integral_add hUV2 hWU,
      integral_add hU hV, eu, ev, ew, ewu, ewv, euv] at heq
    linarith
  have hzero : (fun ω => (w ω - u ω - v ω) ^ 2) =ᵐ[P] 0 :=
    (integral_eq_zero_iff_of_nonneg_ae
      (Filter.Eventually.of_forall fun ω => sq_nonneg _) hF).mp hkey
  filter_upwards [hzero] with ω hω
  have h2 : (w ω - u ω - v ω) ^ 2 = 0 := by simpa using hω
  have h0 : w ω - u ω - v ω = 0 := by nlinarith [h2, sq_nonneg (w ω - u ω - v ω)]
  linarith
end Parallelogram

section Additivity

variable (W : LevyStochCalc.Brownian.BrownianMotion P)
  (ℱ : Filtration ℝ ‹MeasurableSpace Ω›) (hℱ : IsBrownianFiltration W ℱ)

end Additivity

section Scaling

variable (W : LevyStochCalc.Brownian.BrownianMotion P)
  (ℱ : Filtration ℝ ‹MeasurableSpace Ω›) (hℱ : IsBrownianFiltration W ℱ)

end Scaling

end LevyStochCalc.Brownian.Ito


