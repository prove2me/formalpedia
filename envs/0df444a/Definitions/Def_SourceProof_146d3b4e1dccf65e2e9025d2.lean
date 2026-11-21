-- Prove2me | Definitions.Def_SourceProof_146d3b4e1dccf65e2e9025d2
-- name    : SourceProof_146d3b4e1dccf65e2e9025d2
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-20T21:29:09.203714+00:00
-- url     : https://prove2.me/theorems/595f390c-e307-4926-aa98-ce130f645001
-- title:
--   LevyStochCalc source module: SourceProof_146d3b4e1dccf65e2e9025d2
-- statement:
--   The original source theorem `LevyStochCalc.Ito.Picard.bieleckiNorm_picardStep_lt_top` comes from the `LevyStochCalc.Ito.PicardOutputMoments` module. The staged Lean declaration includes its source proof and dependency references.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Ito_PicardIntegrandFrozen_F000
import Definitions.Def_LevyStochCalc_Ito_PicardSpaceBieleckiQuotient_F001
import Definitions.Def_LevyStochCalc_Probability_ProgressiveCadlag_F000
import Definitions.Def_LevyStochCalc_Probability_ProgressiveCadlag_F001
import Definitions.Def_SourceProof_87edab98500212c85ba68c35

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


theorem _root_.Prove2MeSourceProof.h_146d3b4e1dccf65e2e9025d2
    (h_μ_meas : ∀ i : Fin n,
      Measurable (Function.uncurry fun ω s => coeffs.μ s (X s ω) i))
    {T : ℝ}
    (hμT : ∀ i : Fin n, ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
      (‖coeffs.μ s (X s ω) i‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤)
    (hσT : ∀ i : Fin n, ∀ j : Fin d, ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
      (‖coeffs.σ s (X s ω) i j‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤)
    (hγT : ∀ i : Fin n, ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T, ∫⁻ e,
      (‖coeffs.γ s (X s ω) e i‖₊ : ℝ≥0∞) ^ 2 ∂ν ∂volume ∂P < ⊤) :
    bieleckiNorm (P := P) 0 T
      (fun t ω => picardStep W N ℱ hℱW hℱN coeffs X x₀ h_σ_meas h_σ_progMeas h_σ_sq
        h_γ_meas h_γ_progMeas h_γ_sq t ω) < ⊤ := by
  have hKfin : (∑ i : Fin n,
      (3 * (2 * (‖x₀ i‖₊ : ℝ≥0∞) ^ 2
          + 2 * (ENNReal.ofReal T * ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
              (‖coeffs.μ s (X s ω) i‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P))
        + 3 * ((d : ℝ≥0∞) * ∑ j : Fin d, ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
            (‖coeffs.σ s (X s ω) i j‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P)
        + 3 * ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T, ∫⁻ e,
            (‖coeffs.γ s (X s ω) e i‖₊ : ℝ≥0∞) ^ 2 ∂ν ∂volume ∂P)) < ⊤ := by
    refine ENNReal.sum_lt_top.mpr fun i _ => ?_
    refine ENNReal.add_lt_top.mpr ⟨ENNReal.add_lt_top.mpr ⟨?_, ?_⟩, ?_⟩
    · refine ENNReal.mul_lt_top (by simp) (ENNReal.add_lt_top.mpr ⟨?_, ?_⟩)
      · exact ENNReal.mul_lt_top (by simp) (ENNReal.pow_lt_top ENNReal.coe_lt_top)
      · exact ENNReal.mul_lt_top (by simp)
          (ENNReal.mul_lt_top ENNReal.ofReal_lt_top (hμT i))
    · exact ENNReal.mul_lt_top (by simp) (ENNReal.mul_lt_top (by simp)
        (ENNReal.sum_lt_top.mpr fun j _ => hσT i j))
    · exact ENNReal.mul_lt_top (by simp) (hγT i)
  refine lt_of_le_of_lt (b := _ ^ ((1 : ℝ) / 2)) ?_
    (ENNReal.rpow_lt_top_of_nonneg (by norm_num) hKfin.ne)
  unfold LevyStochCalc.Ito.Picard.bieleckiNorm
  refine iSup₂_le fun t ht => ?_
  rw [neg_zero, zero_mul, Real.exp_zero, ENNReal.ofReal_one, one_mul]
  exact ENNReal.rpow_le_rpow
    (_root_.Prove2MeSourceProof.h_87edab98500212c85ba68c35 W N ℱ hℱW hℱN coeffs X x₀ h_σ_meas h_σ_progMeas h_σ_sq
      h_γ_meas h_γ_progMeas h_γ_sq h_μ_meas ht hμT) (by norm_num)
end Step

end LevyStochCalc.Ito.Picard


