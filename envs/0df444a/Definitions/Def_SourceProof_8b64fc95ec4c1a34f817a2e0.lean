-- Prove2me | Definitions.Def_SourceProof_8b64fc95ec4c1a34f817a2e0
-- name    : SourceProof_8b64fc95ec4c1a34f817a2e0
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-19T21:50:14.825833+00:00
-- url     : https://prove2.me/theorems/018bce0f-6225-4f94-9553-6ed1ad9aa4a4
-- title:
--   LevyStochCalc source proof: LevyStochCalc.Brownian.Ito.lintegral_energy_const_mul
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

omit [IsProbabilityMeasure P] in

theorem _root_.Prove2MeSourceProof.h_8b64fc95ec4c1a34f817a2e0 {H : Ω → ℝ → ℝ} (hm : Measurable (Function.uncurry H))
    (c T : ℝ) :
    (∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T, (‖c * H ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P)
      = ENNReal.ofReal (c ^ 2)
        * ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T, (‖H ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P := by
  have hpt : ∀ a : ℝ, (‖c * a‖₊ : ℝ≥0∞) ^ 2
      = ENNReal.ofReal (c ^ 2) * (‖a‖₊ : ℝ≥0∞) ^ 2 := by
    intro a
    rw [LevyStochCalc.Brownian.Ito.sq_nnnorm_eq_ofReal_sq, LevyStochCalc.Brownian.Ito.sq_nnnorm_eq_ofReal_sq,
      ← ENNReal.ofReal_mul (sq_nonneg c)]
    congr 1
    ring
  have hinner : ∀ ω : Ω,
      (∫⁻ s in Set.Icc (0 : ℝ) T, (‖c * H ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume)
        = ENNReal.ofReal (c ^ 2)
          * ∫⁻ s in Set.Icc (0 : ℝ) T, (‖H ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume := by
    intro ω
    have h1 : Measurable fun s => (‖H ω s‖₊ : ℝ≥0∞) ^ 2 :=
      (((measurable_nnnorm.comp (hm.comp measurable_prodMk_left)).coe_nnreal_ennreal).pow_const 2)
    rw [← lintegral_const_mul _ h1]
    exact lintegral_congr fun s => hpt _
  rw [← lintegral_const_mul _ (LevyStochCalc.Brownian.Ito.measurable_energyDensity hm T)]
  exact lintegral_congr fun ω => hinner ω
end Energy

section Parallelogram

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


