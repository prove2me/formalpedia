-- Prove2me | Definitions.Def_SourceProof_87edab98500212c85ba68c35
-- name    : SourceProof_87edab98500212c85ba68c35
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-20T21:26:18.176824+00:00
-- url     : https://prove2.me/theorems/ca5f28d7-a737-4f35-9118-3e5740701e1b
-- title:
--   LevyStochCalc source module: SourceProof_87edab98500212c85ba68c35
-- statement:
--   The original source theorem `LevyStochCalc.Ito.Picard.lintegral_sq_picardStep_le` comes from the `LevyStochCalc.Ito.PicardOutputMoments` module. The staged Lean declaration includes its source proof and dependency references.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Ito_PicardOutputMoments_F000
import Definitions.Def_LevyStochCalc_Ito_PicardOutputMoments_F002
import Definitions.Def_LevyStochCalc_Ito_PicardOutputMoments_F003
import Definitions.Def_SourceProof_06ce725b2f140e9df5ff737b
import Definitions.Def_SourceProof_afc5c99feb5115695a5f6b39

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


theorem _root_.Prove2MeSourceProof.h_87edab98500212c85ba68c35
    (h_μ_meas : ∀ i : Fin n,
      Measurable (Function.uncurry fun ω s => coeffs.μ s (X s ω) i))
    {T t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) T)
    (hμT : ∀ i : Fin n, ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
      (‖coeffs.μ s (X s ω) i‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤) :
    ∫⁻ ω, ∑ i, (‖picardStep W N ℱ hℱW hℱN coeffs X x₀ h_σ_meas h_σ_progMeas h_σ_sq
        h_γ_meas h_γ_progMeas h_γ_sq t ω i‖₊ : ℝ≥0∞) ^ 2 ∂P
      ≤ ∑ i : Fin n,
          (3 * (2 * (‖x₀ i‖₊ : ℝ≥0∞) ^ 2
              + 2 * (ENNReal.ofReal T * ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
                  (‖coeffs.μ s (X s ω) i‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P))
            + 3 * ((d : ℝ≥0∞) * ∑ j : Fin d, ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
                (‖coeffs.σ s (X s ω) i j‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P)
            + 3 * ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T, ∫⁻ e,
                (‖coeffs.γ s (X s ω) e i‖₊ : ℝ≥0∞) ^ 2 ∂ν ∂volume ∂P) := by
  obtain ⟨ht0, htT⟩ := ht
  have hdr : ∀ i : Fin n, Measurable fun ω =>
      (‖LevyStochCalc.Ito.Picard.picardStep_drift coeffs X x₀ t ω i‖₊ : ℝ≥0∞) ^ 2 := fun i =>
    (((LevyStochCalc.Ito.Picard.measurable_picardStep_drift coeffs X x₀ i (h_μ_meas i)
      t).nnnorm).coe_nnreal_ennreal).pow_const 2
  have hdf : ∀ i : Fin n, Measurable fun ω =>
      (‖LevyStochCalc.Ito.Picard.picardStep_diffusion W ℱ hℱW coeffs X h_σ_meas h_σ_progMeas h_σ_sq t ω i‖₊
        : ℝ≥0∞) ^ 2 := fun i =>
    (((_root_.Prove2MeSourceProof.h_06ce725b2f140e9df5ff737b W ℱ hℱW coeffs X h_σ_meas h_σ_progMeas h_σ_sq i
      t).nnnorm).coe_nnreal_ennreal).pow_const 2
  have hjp : ∀ i : Fin n, Measurable fun ω =>
      (‖LevyStochCalc.Ito.Picard.picardStep_jump N ℱ hℱN coeffs X h_γ_meas h_γ_progMeas h_γ_sq t ω i‖₊
        : ℝ≥0∞) ^ 2 := fun i =>
    (((LevyStochCalc.Ito.Picard.measurable_picardStep_jump N ℱ hℱN coeffs X h_γ_meas h_γ_progMeas h_γ_sq i
      t).nnnorm).coe_nnreal_ennreal).pow_const 2
  -- pointwise three-term split
  have hpt : ∀ ω : Ω, ∑ i, (‖LevyStochCalc.Ito.Picard.picardStep W N ℱ hℱW hℱN coeffs X x₀ h_σ_meas h_σ_progMeas
        h_σ_sq h_γ_meas h_γ_progMeas h_γ_sq t ω i‖₊ : ℝ≥0∞) ^ 2
      ≤ ∑ i : Fin n,
          (3 * (‖LevyStochCalc.Ito.Picard.picardStep_drift coeffs X x₀ t ω i‖₊ : ℝ≥0∞) ^ 2
            + 3 * (‖LevyStochCalc.Ito.Picard.picardStep_diffusion W ℱ hℱW coeffs X h_σ_meas h_σ_progMeas h_σ_sq
                t ω i‖₊ : ℝ≥0∞) ^ 2
            + 3 * (‖LevyStochCalc.Ito.Picard.picardStep_jump N ℱ hℱN coeffs X h_γ_meas h_γ_progMeas h_γ_sq
                t ω i‖₊ : ℝ≥0∞) ^ 2) := by
    intro ω
    refine Finset.sum_le_sum fun i _ => ?_
    exact _root_.Prove2MeSourceProof.h_afc5c99feb5115695a5f6b39 _ _ _
  have hmeas2 : ∀ i : Fin n, Measurable fun ω =>
      3 * (‖LevyStochCalc.Ito.Picard.picardStep_drift coeffs X x₀ t ω i‖₊ : ℝ≥0∞) ^ 2
        + 3 * (‖LevyStochCalc.Ito.Picard.picardStep_diffusion W ℱ hℱW coeffs X h_σ_meas h_σ_progMeas h_σ_sq
            t ω i‖₊ : ℝ≥0∞) ^ 2 :=
    fun i => ((hdr i).const_mul 3).add ((hdf i).const_mul 3)
  have hmeas3 : ∀ i : Fin n, Measurable fun ω =>
      3 * (‖LevyStochCalc.Ito.Picard.picardStep_drift coeffs X x₀ t ω i‖₊ : ℝ≥0∞) ^ 2
        + 3 * (‖LevyStochCalc.Ito.Picard.picardStep_diffusion W ℱ hℱW coeffs X h_σ_meas h_σ_progMeas h_σ_sq
            t ω i‖₊ : ℝ≥0∞) ^ 2
        + 3 * (‖LevyStochCalc.Ito.Picard.picardStep_jump N ℱ hℱN coeffs X h_γ_meas h_γ_progMeas h_γ_sq
            t ω i‖₊ : ℝ≥0∞) ^ 2 :=
    fun i => (hmeas2 i).add ((hjp i).const_mul 3)
  refine (lintegral_mono hpt).trans ?_
  rw [MeasureTheory.lintegral_finsetSum _ (fun i _ => hmeas3 i)]
  refine Finset.sum_le_sum fun i _ => ?_
  rw [MeasureTheory.lintegral_add_left (hmeas2 i),
    MeasureTheory.lintegral_add_left ((hdr i).const_mul 3),
    MeasureTheory.lintegral_const_mul' _ _ (by simp : (3 : ℝ≥0∞) ≠ ⊤),
    MeasureTheory.lintegral_const_mul' _ _ (by simp : (3 : ℝ≥0∞) ≠ ⊤),
    MeasureTheory.lintegral_const_mul' _ _ (by simp : (3 : ℝ≥0∞) ≠ ⊤)]
  have hμt : ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) t,
      (‖coeffs.μ s (X s ω) i‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤ :=
    lt_of_le_of_lt (LevyStochCalc.Ito.Picard.lintegral_lintegral_Icc_mono htT) (hμT i)
  refine add_le_add (add_le_add (mul_le_mul' le_rfl ?_) (mul_le_mul' le_rfl ?_))
    (mul_le_mul' le_rfl ?_)
  · refine (LevyStochCalc.Ito.Picard.lintegral_sq_picardStep_drift_le coeffs X x₀ i (h_μ_meas i) ht0 hμt).trans ?_
    exact add_le_add le_rfl (mul_le_mul' le_rfl
      (mul_le_mul' (ENNReal.ofReal_le_ofReal htT) (LevyStochCalc.Ito.Picard.lintegral_lintegral_Icc_mono htT)))
  · refine (LevyStochCalc.Ito.Picard.lintegral_sq_picardStep_diffusion_le W ℱ hℱW coeffs X h_σ_meas h_σ_progMeas
      h_σ_sq i ht0).trans ?_
    exact mul_le_mul' le_rfl
      (Finset.sum_le_sum fun j _ => LevyStochCalc.Ito.Picard.lintegral_lintegral_Icc_mono htT)
  · refine le_of_eq_of_le (LevyStochCalc.Ito.Picard.lintegral_sq_picardStep_jump_eq N ℱ hℱN coeffs X h_γ_meas
      h_γ_progMeas h_γ_sq i ht0) ?_
    exact LevyStochCalc.Ito.Picard.lintegral_lintegral_Icc_mono htT
end Step

end LevyStochCalc.Ito.Picard


