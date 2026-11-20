-- Prove2me | Definitions.Def_SourceProof_700488d66fa58fc241f21293
-- name    : SourceProof_700488d66fa58fc241f21293
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-19T21:48:49.381729+00:00
-- url     : https://prove2.me/theorems/9c824354-b90a-440a-ba94-6131abca001e
-- title:
--   LevyStochCalc source proof: LevyStochCalc.Brownian.Ito.lintegral_energy_lt_top_of_bound
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

theorem _root_.Prove2MeSourceProof.h_700488d66fa58fc241f21293 {K : Ω → ℝ → ℝ}
    (hbound : ∀ ω s, (‖K ω s‖₊ : ℝ≥0∞) ^ 2
      ≤ 2 * ((‖H₁ ω s‖₊ : ℝ≥0∞) ^ 2 + (‖H₂ ω s‖₊ : ℝ≥0∞) ^ 2))
    (hm₁ : Measurable (Function.uncurry H₁)) (hm₂ : Measurable (Function.uncurry H₂))
    (hq₁ : ∀ T, 0 < T → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
      (‖H₁ ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤)
    (hq₂ : ∀ T, 0 < T → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
      (‖H₂ ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤) :
    ∀ T, 0 < T → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
      (‖K ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤ := by
  intro T hT
  have e1 := LevyStochCalc.Brownian.Ito.measurable_energyDensity hm₁ T
  have e2 := LevyStochCalc.Brownian.Ito.measurable_energyDensity hm₂ T
  have hstep : (∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T, (‖K ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P)
      ≤ 2 * (∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T, (‖H₁ ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P)
        + 2 * ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T, (‖H₂ ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P := by
    rw [← lintegral_const_mul 2 e1, ← lintegral_const_mul 2 e2,
      ← lintegral_add_left (e1.const_mul 2)]
    refine lintegral_mono fun ω => ?_
    have h1 : Measurable fun s => (‖H₁ ω s‖₊ : ℝ≥0∞) ^ 2 :=
      (((measurable_nnnorm.comp (hm₁.comp measurable_prodMk_left)).coe_nnreal_ennreal).pow_const 2)
    have h2 : Measurable fun s => (‖H₂ ω s‖₊ : ℝ≥0∞) ^ 2 :=
      (((measurable_nnnorm.comp (hm₂.comp measurable_prodMk_left)).coe_nnreal_ennreal).pow_const 2)
    rw [← lintegral_const_mul 2 h1, ← lintegral_const_mul 2 h2,
      ← lintegral_add_left (h1.const_mul 2)]
    refine lintegral_mono fun s => ?_
    calc (‖K ω s‖₊ : ℝ≥0∞) ^ 2
        ≤ 2 * ((‖H₁ ω s‖₊ : ℝ≥0∞) ^ 2 + (‖H₂ ω s‖₊ : ℝ≥0∞) ^ 2) := hbound ω s
      _ = 2 * (‖H₁ ω s‖₊ : ℝ≥0∞) ^ 2 + 2 * (‖H₂ ω s‖₊ : ℝ≥0∞) ^ 2 := by ring
  refine lt_of_le_of_lt hstep ?_
  exact ENNReal.add_lt_top.mpr
    ⟨ENNReal.mul_lt_top (by simp) (hq₁ T hT), ENNReal.mul_lt_top (by simp) (hq₂ T hT)⟩
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


