-- Prove2me | Definitions.Def_SourceProof_b2a8a79da4bd7b154436ee26
-- name    : SourceProof_b2a8a79da4bd7b154436ee26
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-19T21:51:32.792481+00:00
-- url     : https://prove2.me/theorems/bf71b63f-0e6c-473b-a371-f481b9eb924d
-- title:
--   LevyStochCalc source proof: LevyStochCalc.Brownian.Ito.ae_eq_const_mul_of_sq_distances
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

end Parallelogram

section Additivity

variable (W : LevyStochCalc.Brownian.BrownianMotion P)
  (ℱ : Filtration ℝ ‹MeasurableSpace Ω›) (hℱ : IsBrownianFiltration W ℱ)

end Additivity

section Scaling

omit [IsProbabilityMeasure P] in

theorem _root_.Prove2MeSourceProof.h_b2a8a79da4bd7b154436ee26 {x y : Ω → ℝ} (hx : MemLp x 2 P) (hy : MemLp y 2 P)
    {c : ℝ} {X Y Z : ℝ≥0∞}
    (hSx : ∫⁻ ω, (‖x ω‖₊ : ℝ≥0∞) ^ 2 ∂P = X)
    (hSy : ∫⁻ ω, (‖y ω‖₊ : ℝ≥0∞) ^ 2 ∂P = Y)
    (hSxy : ∫⁻ ω, (‖x ω - y ω‖₊ : ℝ≥0∞) ^ 2 ∂P = Z)
    (hXY : X.toReal = c ^ 2 * Y.toReal) (hZY : Z.toReal = (c - 1) ^ 2 * Y.toReal) :
    x =ᵐ[P] fun ω => c * y ω := by
  have ex : ∫ ω, x ω ^ 2 ∂P = X.toReal := by
    rw [LevyStochCalc.Brownian.Ito.integral_sq_eq_toReal hx.aestronglyMeasurable, hSx]
  have ey : ∫ ω, y ω ^ 2 ∂P = Y.toReal := by
    rw [LevyStochCalc.Brownian.Ito.integral_sq_eq_toReal hy.aestronglyMeasurable, hSy]
  have exy : ∫ ω, (x ω - y ω) ^ 2 ∂P = Z.toReal := by
    rw [LevyStochCalc.Brownian.Ito.integral_sq_eq_toReal (X := fun ω => x ω - y ω)
      (hx.aestronglyMeasurable.sub hy.aestronglyMeasurable), hSxy]
  have hsub : Integrable (fun ω => (x ω - y ω) ^ 2) P := LevyStochCalc.Brownian.Ito.integrable_sq_of_memLp (hx.sub hy)
  have hX2 : Integrable (fun ω => (1 - c) * x ω ^ 2) P :=
    (LevyStochCalc.Brownian.Ito.integrable_sq_of_memLp hx).const_mul _
  have hY2 : Integrable (fun ω => (c ^ 2 - c) * y ω ^ 2) P :=
    (LevyStochCalc.Brownian.Ito.integrable_sq_of_memLp hy).const_mul _
  have hZ2 : Integrable (fun ω => c * (x ω - y ω) ^ 2) P := hsub.const_mul _
  have hF : Integrable (fun ω => (x ω - c * y ω) ^ 2) P := by
    have : MemLp (fun ω => x ω - c * y ω) 2 P := hx.sub (hy.const_mul c)
    exact LevyStochCalc.Brownian.Ito.integrable_sq_of_memLp this
  have hkey : ∫ ω, (x ω - c * y ω) ^ 2 ∂P = 0 := by
    have hid : ∀ ω : Ω, (x ω - c * y ω) ^ 2
        = (1 - c) * x ω ^ 2 + ((c ^ 2 - c) * y ω ^ 2 + c * (x ω - y ω) ^ 2) := fun ω => by ring
    have h1 : ∫ ω, (x ω - c * y ω) ^ 2 ∂P
        = ∫ ω, ((1 - c) * x ω ^ 2 + ((c ^ 2 - c) * y ω ^ 2 + c * (x ω - y ω) ^ 2)) ∂P :=
      integral_congr_ae (Filter.Eventually.of_forall hid)
    have hYZ : Integrable (fun ω => (c ^ 2 - c) * y ω ^ 2 + c * (x ω - y ω) ^ 2) P :=
      hY2.add hZ2
    rw [h1, integral_add hX2 hYZ, integral_add hY2 hZ2,
      integral_const_mul, integral_const_mul, integral_const_mul, ex, ey, exy, hXY, hZY]
    ring
  have hzero : (fun ω => (x ω - c * y ω) ^ 2) =ᵐ[P] 0 :=
    (integral_eq_zero_iff_of_nonneg_ae
      (Filter.Eventually.of_forall fun ω => sq_nonneg _) hF).mp hkey
  filter_upwards [hzero] with ω hω
  have h2 : (x ω - c * y ω) ^ 2 = 0 := by simpa using hω
  nlinarith [h2, sq_nonneg (x ω - c * y ω)]
variable (W : LevyStochCalc.Brownian.BrownianMotion P)
  (ℱ : Filtration ℝ ‹MeasurableSpace Ω›) (hℱ : IsBrownianFiltration W ℱ)

end Scaling

end LevyStochCalc.Brownian.Ito


