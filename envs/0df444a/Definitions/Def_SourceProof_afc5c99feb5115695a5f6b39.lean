-- Prove2me | Definitions.Def_SourceProof_afc5c99feb5115695a5f6b39
-- name    : SourceProof_afc5c99feb5115695a5f6b39
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-20T20:40:14.536017+00:00
-- url     : https://prove2.me/theorems/721fcd9d-3bc2-4ccc-b207-005a7156411e
-- title:
--   LevyStochCalc source module: SourceProof_afc5c99feb5115695a5f6b39
-- statement:
--   The original source theorem `LevyStochCalc.Ito.Picard.sq_nnnorm_add3_le` comes from the `LevyStochCalc.Ito.PicardOutputMoments` module. The staged Lean declaration includes its source proof and dependency references.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Ito_PicardIntegrandFrozen_F000
import Definitions.Def_LevyStochCalc_Ito_PicardSpaceBieleckiQuotient_F001
import Definitions.Def_LevyStochCalc_Probability_ProgressiveCadlag_F000
import Definitions.Def_LevyStochCalc_Probability_ProgressiveCadlag_F001

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# Second moments of the Picard step

Each of the three components of the Picard step — the Lebesgue drift integral, the Brownian
stochastic integral and the compensated jump integral — is bounded in `L²` uniformly over
`[0, T]` by the energies of its integrand, through Cauchy–Schwarz for the drift and the Itô
and Itô–Lévy isometries for the two stochastic components; summing the three bounds gives a
finite Bielecki norm for the step.
-/

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

namespace LevyStochCalc.Ito.Picard

universe u v

variable {Ω : Type u} [MeasurableSpace Ω]
variable {E : Type v} [MeasurableSpace E]

variable {n d : ℕ} {P : MeasureTheory.Measure Ω} [MeasureTheory.IsProbabilityMeasure P]


theorem _root_.Prove2MeSourceProof.h_afc5c99feb5115695a5f6b39 (x y z : ℝ) :
    (‖x + y + z‖₊ : ℝ≥0∞) ^ 2
      ≤ 3 * (‖x‖₊ : ℝ≥0∞) ^ 2 + 3 * (‖y‖₊ : ℝ≥0∞) ^ 2 + 3 * (‖z‖₊ : ℝ≥0∞) ^ 2 := by
  have hreal : (x + y + z) ^ 2 ≤ 3 * x ^ 2 + 3 * y ^ 2 + 3 * z ^ 2 := by
    nlinarith [sq_nonneg (x - y), sq_nonneg (y - z), sq_nonneg (x - z)]
  calc (‖x + y + z‖₊ : ℝ≥0∞) ^ 2 = ENNReal.ofReal ((x + y + z) ^ 2) := LevyStochCalc.Ito.Picard.sq_coe_nnnorm_real _
    _ ≤ ENNReal.ofReal (3 * x ^ 2 + 3 * y ^ 2 + 3 * z ^ 2) := ENNReal.ofReal_le_ofReal hreal
    _ = 3 * (‖x‖₊ : ℝ≥0∞) ^ 2 + 3 * (‖y‖₊ : ℝ≥0∞) ^ 2 + 3 * (‖z‖₊ : ℝ≥0∞) ^ 2 := by
        rw [ENNReal.ofReal_add (by positivity) (by positivity),
          ENNReal.ofReal_add (by positivity) (by positivity),
          ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 3),
          ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 3),
          ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 3), ENNReal.ofReal_ofNat,
          ← LevyStochCalc.Ito.Picard.sq_coe_nnnorm_real, ← LevyStochCalc.Ito.Picard.sq_coe_nnnorm_real, ← LevyStochCalc.Ito.Picard.sq_coe_nnnorm_real]
section Step

variable {ν : MeasureTheory.Measure E} [MeasureTheory.SigmaFinite ν]
variable (W : LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion P d)
variable (N : LevyStochCalc.Poisson.PoissonRandomMeasure P ν)
variable (ℱ : MeasureTheory.Filtration ℝ ‹MeasurableSpace Ω›)
variable (hℱW : ∀ j : Fin d, LevyStochCalc.Brownian.IsBrownianFiltration (W.W j) ℱ)
variable (hℱN : LevyStochCalc.Poisson.IsPoissonFiltration N ℱ)
variable (coeffs : LevyStochCalc.Ito.Setting.JumpDiffusionCoeffs n d E)
variable (X : ℝ → Ω → (Fin n → ℝ)) (x₀ : Fin n → ℝ)
variable (h_σ_meas : ∀ i : Fin n, ∀ j : Fin d,
  Measurable (Function.uncurry (fun ω s => coeffs.σ s (X s ω) i j)))
variable (h_σ_progMeas : ∀ i : Fin n, ∀ j : Fin d,
  Probability.ProgressivelyMeasurable ℱ (fun ω s => coeffs.σ s (X s ω) i j))
variable (h_σ_sq : ∀ i : Fin n, ∀ j : Fin d, ∀ T : ℝ, 0 < T →
  ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
    (‖coeffs.σ s (X s ω) i j‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤)
variable (h_γ_meas : ∀ i : Fin n,
  Measurable (fun p : Ω × ℝ × E => coeffs.γ p.2.1 (X p.2.1 p.1) p.2.2 i))
variable (h_γ_progMeas : ∀ i : Fin n,
  Probability.MarkedProgressivelyMeasurable ℱ (fun ω s e => coeffs.γ s (X s ω) e i))
variable (h_γ_sq : ∀ i : Fin n, ∀ T : ℝ, 0 < T →
  ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T, ∫⁻ e,
    (‖coeffs.γ s (X s ω) e i‖₊ : ℝ≥0∞) ^ 2 ∂ν ∂volume ∂P < ⊤)

end Step

end LevyStochCalc.Ito.Picard


