-- Prove2me | Definitions.Def_LevyStochCalc_Ito_PicardOutputMoments_F001
-- name    : LevyStochCalc_Ito_PicardOutputMoments_F001
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-20T21:19:17.209839+00:00
-- url     : https://prove2.me/theorems/01340a70-a725-42d0-90e4-fffe9fb9a718
-- title:
--   Source declarations: LevyStochCalc.Ito.PicardOutputMoments
-- statement:
--   Source-preserving extracted declarations from LevyStochCalc.Ito.PicardOutputMoments. Existing definitions, lemmas, instances, proofs and elaboration context are retained; generated import closure remains under review.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Ito_PicardIntegrandFrozen_F000
import Definitions.Def_LevyStochCalc_Ito_PicardSpaceBieleckiQuotient_F001
import Definitions.Def_LevyStochCalc_Probability_ProgressiveCadlag_F000
import Definitions.Def_LevyStochCalc_Probability_ProgressiveCadlag_F001
import Definitions.Def_SourceProof_190a5767e8f1b936b4a6a09f

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

/-- `‖a + b‖² ≤ 2‖a‖² + 2‖b‖²` for reals, in `ℝ≥0∞`. -/
theorem sq_nnnorm_add_le (a b : ℝ) :
    (‖a + b‖₊ : ℝ≥0∞) ^ 2 ≤ 2 * (‖a‖₊ : ℝ≥0∞) ^ 2 + 2 * (‖b‖₊ : ℝ≥0∞) ^ 2 := by
  have hreal : (a + b) ^ 2 ≤ 2 * a ^ 2 + 2 * b ^ 2 := by nlinarith [sq_nonneg (a - b)]
  calc (‖a + b‖₊ : ℝ≥0∞) ^ 2 = ENNReal.ofReal ((a + b) ^ 2) := sq_coe_nnnorm_real _
    _ ≤ ENNReal.ofReal (2 * a ^ 2 + 2 * b ^ 2) := ENNReal.ofReal_le_ofReal hreal
    _ = 2 * (‖a‖₊ : ℝ≥0∞) ^ 2 + 2 * (‖b‖₊ : ℝ≥0∞) ^ 2 := by
        rw [ENNReal.ofReal_add (by positivity) (by positivity),
          ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 2),
          ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 2), ENNReal.ofReal_ofNat,
          ← sq_coe_nnnorm_real, ← sq_coe_nnnorm_real]
omit [MeasurableSpace E] in
/-- **Second moment of the drift component**, by Cauchy–Schwarz on `[0, t]`. -/
theorem lintegral_sq_picardStep_drift_le
    (coeffs : LevyStochCalc.Ito.Setting.JumpDiffusionCoeffs n d E)
    (X : ℝ → Ω → (Fin n → ℝ)) (x₀ : Fin n → ℝ) (i : Fin n)
    (h_μ_meas : Measurable (Function.uncurry fun ω s => coeffs.μ s (X s ω) i))
    {t : ℝ} (ht : 0 ≤ t)
    (hfin : ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) t,
      (‖coeffs.μ s (X s ω) i‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤) :
    ∫⁻ ω, (‖picardStep_drift coeffs X x₀ t ω i‖₊ : ℝ≥0∞) ^ 2 ∂P
      ≤ 2 * (‖x₀ i‖₊ : ℝ≥0∞) ^ 2
        + 2 * (ENNReal.ofReal t * ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) t,
            (‖coeffs.μ s (X s ω) i‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P) := by
  have hunfold : ∀ ω : Ω, picardStep_drift coeffs X x₀ t ω i
      = x₀ i + ∫ s in Set.Icc (0 : ℝ) t, coeffs.μ s (X s ω) i := fun _ => rfl
  calc ∫⁻ ω, (‖picardStep_drift coeffs X x₀ t ω i‖₊ : ℝ≥0∞) ^ 2 ∂P
      = ∫⁻ ω, (‖x₀ i + ∫ s in Set.Icc (0 : ℝ) t, coeffs.μ s (X s ω) i‖₊ : ℝ≥0∞) ^ 2 ∂P :=
        lintegral_congr fun ω => by rw [hunfold ω]
    _ ≤ ∫⁻ ω, (2 * (‖x₀ i‖₊ : ℝ≥0∞) ^ 2
          + 2 * (‖∫ s in Set.Icc (0 : ℝ) t, coeffs.μ s (X s ω) i‖₊ : ℝ≥0∞) ^ 2) ∂P :=
        lintegral_mono fun ω => sq_nnnorm_add_le _ _
    _ = 2 * (‖x₀ i‖₊ : ℝ≥0∞) ^ 2
          + 2 * ∫⁻ ω, (‖∫ s in Set.Icc (0 : ℝ) t, coeffs.μ s (X s ω) i‖₊ : ℝ≥0∞) ^ 2 ∂P := by
        rw [MeasureTheory.lintegral_add_left measurable_const, MeasureTheory.lintegral_const,
          measure_univ, mul_one,
          MeasureTheory.lintegral_const_mul' _ _ (by simp : (2 : ℝ≥0∞) ≠ ⊤)]
    _ ≤ 2 * (‖x₀ i‖₊ : ℝ≥0∞) ^ 2
          + 2 * (ENNReal.ofReal t * ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) t,
              (‖coeffs.μ s (X s ω) i‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P) :=
        add_le_add le_rfl
          (mul_le_mul' le_rfl (_root_.Prove2MeSourceProof.h_190a5767e8f1b936b4a6a09f h_μ_meas ht hfin))
omit [MeasurableSpace E] [MeasureTheory.IsProbabilityMeasure P] in
/-- The time-integral of a jointly measurable process is measurable in the sample. -/
theorem measurable_setIntegral_slice {f : Ω → ℝ → ℝ}
    (hf : Measurable (Function.uncurry f)) (t : ℝ) :
    Measurable fun ω => ∫ s in Set.Icc (0 : ℝ) t, f ω s := by
  haveI : MeasureTheory.IsFiniteMeasure (volume.restrict (Set.Icc (0 : ℝ) t)) :=
    ⟨by rw [MeasureTheory.Measure.restrict_apply_univ, Real.volume_Icc]
        exact ENNReal.ofReal_lt_top⟩
  exact (hf.stronglyMeasurable.integral_prod_right'
    (ν := volume.restrict (Set.Icc (0 : ℝ) t))).measurable
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


