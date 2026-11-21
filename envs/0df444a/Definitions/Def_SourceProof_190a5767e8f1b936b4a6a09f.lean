-- Prove2me | Definitions.Def_SourceProof_190a5767e8f1b936b4a6a09f
-- name    : SourceProof_190a5767e8f1b936b4a6a09f
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-20T21:16:13.017214+00:00
-- url     : https://prove2.me/theorems/d2ebda65-9977-4226-b7a9-ee23e7fc775d
-- title:
--   LevyStochCalc source module: SourceProof_190a5767e8f1b936b4a6a09f
-- statement:
--   The original source theorem `LevyStochCalc.Ito.Picard.lintegral_sq_setIntegral_le` comes from the `LevyStochCalc.Ito.PicardOutputMoments` module. The staged Lean declaration includes its source proof and dependency references.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Ito_PicardOutputMoments_F000
import Definitions.Def_SourceProof_afc5f2e9c8f3a3e4d632ea4b

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

omit [MeasurableSpace E] [MeasureTheory.IsProbabilityMeasure P] in

theorem _root_.Prove2MeSourceProof.h_190a5767e8f1b936b4a6a09f {f : Ω → ℝ → ℝ}
    (hf : Measurable (Function.uncurry f)) {t : ℝ} (ht : 0 ≤ t)
    (hfin : ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) t, (‖f ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤) :
    ∫⁻ ω, (‖∫ s in Set.Icc (0 : ℝ) t, f ω s‖₊ : ℝ≥0∞) ^ 2 ∂P
      ≤ ENNReal.ofReal t
        * ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) t, (‖f ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P := by
  haveI : MeasureTheory.IsFiniteMeasure (volume.restrict (Set.Icc (0 : ℝ) t)) :=
    ⟨by rw [MeasureTheory.Measure.restrict_apply_univ, Real.volume_Icc]
        exact ENNReal.ofReal_lt_top⟩
  have hinner_meas : Measurable fun ω : Ω =>
      ∫⁻ s in Set.Icc (0 : ℝ) t, (‖f ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume :=
    (hf.nnnorm.coe_nnreal_ennreal.pow_const 2).lintegral_prod_right'
  have hae : ∀ᵐ ω ∂P, ∫⁻ s in Set.Icc (0 : ℝ) t,
      (‖f ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume < ⊤ :=
    MeasureTheory.ae_lt_top hinner_meas hfin.ne
  have hpt : ∀ᵐ ω ∂P, (‖∫ s in Set.Icc (0 : ℝ) t, f ω s‖₊ : ℝ≥0∞) ^ 2
      ≤ ENNReal.ofReal t * ∫⁻ s in Set.Icc (0 : ℝ) t, (‖f ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume := by
    filter_upwards [hae] with ω hω
    have hslice : Measurable (f ω) := hf.comp (measurable_const.prodMk measurable_id)
    -- `f ω` is `L²` on `[0, t]`
    have hL2 : MeasureTheory.MemLp (f ω) 2 (volume.restrict (Set.Icc (0 : ℝ) t)) :=
      LevyStochCalc.Ito.Picard.memLp_two_of_lintegral_sq_lt_top hslice hω
    have hint : MeasureTheory.Integrable (f ω) (volume.restrict (Set.Icc (0 : ℝ) t)) :=
      hL2.integrable (by norm_num)
    -- Cauchy–Schwarz against the constant `1`
    have hCS := _root_.Prove2MeSourceProof.h_afc5f2e9c8f3a3e4d632ea4b (fun s => ‖f ω s‖) t ht
      (Filter.Eventually.of_forall fun _ => norm_nonneg _) hL2.norm
    have habs : |∫ s in Set.Icc (0 : ℝ) t, f ω s| ≤ ∫ s in Set.Icc (0 : ℝ) t, ‖f ω s‖ :=
      MeasureTheory.abs_integral_le_integral_abs.trans_eq
        (MeasureTheory.integral_congr_ae
          (Filter.Eventually.of_forall fun s => (Real.norm_eq_abs (f ω s)).symm))
    have hsq : ∫ s in Set.Icc (0 : ℝ) t, ‖f ω s‖ ^ 2
        = (∫⁻ s in Set.Icc (0 : ℝ) t, (‖f ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume).toReal := by
      rw [MeasureTheory.integral_eq_lintegral_of_nonneg_ae
        (Filter.Eventually.of_forall fun s => by positivity)
        ((hslice.norm.pow_const 2).aestronglyMeasurable)]
      congr 1
      refine lintegral_congr fun s => ?_
      rw [← LevyStochCalc.Ito.Picard.sq_coe_nnnorm_real ‖f ω s‖, nnnorm_norm]
    have hbound : (∫ s in Set.Icc (0 : ℝ) t, f ω s) ^ 2
        ≤ t * (∫⁻ s in Set.Icc (0 : ℝ) t, (‖f ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume).toReal := by
      have hnn : 0 ≤ ∫ s in Set.Icc (0 : ℝ) t, ‖f ω s‖ :=
        MeasureTheory.integral_nonneg_of_ae
          (Filter.Eventually.of_forall fun s => norm_nonneg (f ω s))
      rw [← hsq]
      refine le_trans ?_ hCS
      nlinarith [habs, abs_nonneg (∫ s in Set.Icc (0 : ℝ) t, f ω s),
        sq_abs (∫ s in Set.Icc (0 : ℝ) t, f ω s), hnn]
    calc (‖∫ s in Set.Icc (0 : ℝ) t, f ω s‖₊ : ℝ≥0∞) ^ 2
        = ENNReal.ofReal ((∫ s in Set.Icc (0 : ℝ) t, f ω s) ^ 2) := LevyStochCalc.Ito.Picard.sq_coe_nnnorm_real _
      _ ≤ ENNReal.ofReal
            (t * (∫⁻ s in Set.Icc (0 : ℝ) t, (‖f ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume).toReal) :=
          ENNReal.ofReal_le_ofReal hbound
      _ = ENNReal.ofReal t * ∫⁻ s in Set.Icc (0 : ℝ) t, (‖f ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume := by
          rw [ENNReal.ofReal_mul ht, ENNReal.ofReal_toReal hω.ne]
  refine (lintegral_mono_ae hpt).trans ?_
  rw [MeasureTheory.lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
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


