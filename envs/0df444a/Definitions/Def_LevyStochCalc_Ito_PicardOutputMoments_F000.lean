-- Prove2me | Definitions.Def_LevyStochCalc_Ito_PicardOutputMoments_F000
-- name    : LevyStochCalc_Ito_PicardOutputMoments_F000
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-20T20:40:27.973567+00:00
-- url     : https://prove2.me/theorems/11f0a121-d5a1-496c-af1f-ee873019831a
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
import Definitions.Def_SourceProof_a11eee7d83378555a816acd3

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

/-- Cauchy–Schwarz for a finite sum of reals, transported to `ℝ≥0∞`. -/
theorem sq_nnnorm_sum_le {ι : Type*} (s : Finset ι) (f : ι → ℝ) :
    (‖∑ j ∈ s, f j‖₊ : ℝ≥0∞) ^ 2 ≤ (s.card : ℝ≥0∞) * ∑ j ∈ s, (‖f j‖₊ : ℝ≥0∞) ^ 2 := by
  have h1 : (∑ j ∈ s, f j) ^ 2 ≤ (s.card : ℝ) * ∑ j ∈ s, (f j) ^ 2 :=
    sq_sum_le_card_mul_sum_sq
  calc (‖∑ j ∈ s, f j‖₊ : ℝ≥0∞) ^ 2
      = ENNReal.ofReal ((∑ j ∈ s, f j) ^ 2) := sq_coe_nnnorm_real _
    _ ≤ ENNReal.ofReal ((s.card : ℝ) * ∑ j ∈ s, (f j) ^ 2) := ENNReal.ofReal_le_ofReal h1
    _ = (s.card : ℝ≥0∞) * ∑ j ∈ s, (‖f j‖₊ : ℝ≥0∞) ^ 2 := by
        rw [ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_natCast,
          ENNReal.ofReal_sum_of_nonneg (fun _ _ => sq_nonneg _)]
        exact congrArg _ (Finset.sum_congr rfl fun j _ => (sq_coe_nnnorm_real (f j)).symm)
variable {n d : ℕ} {P : MeasureTheory.Measure Ω} [MeasureTheory.IsProbabilityMeasure P]

omit [MeasurableSpace E] in
/-- The Itô isometry at every nonnegative horizon, including `0`. -/
theorem itoIsometry_of_nonneg
    (W : LevyStochCalc.Brownian.BrownianMotion P)
    (ℱ : MeasureTheory.Filtration ℝ ‹MeasurableSpace Ω›)
    (hℱ : LevyStochCalc.Brownian.IsBrownianFiltration W ℱ)
    (H : Ω → ℝ → ℝ)
    (h_meas : Measurable (Function.uncurry H))
    (h_progMeas : Probability.ProgressivelyMeasurable ℱ H)
    (h_sq : ∀ T : ℝ, 0 < T →
      ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T, (‖H ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤)
    {T : ℝ} (hT : 0 ≤ T) :
    ∫⁻ ω, (‖LevyStochCalc.Brownian.Ito.stochasticIntegral W ℱ hℱ H h_meas h_progMeas h_sq T ω‖₊
      : ℝ≥0∞) ^ 2 ∂P
      = ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T, (‖H ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P :=
  _root_.Prove2MeSourceProof.h_a11eee7d83378555a816acd3 W ℱ hℱ H h_meas h_progMeas
    h_sq hT
/-- The Itô–Lévy isometry at every nonnegative horizon, including `0`. -/
theorem compensatedIsometry_of_nonneg {ν : MeasureTheory.Measure E}
    [MeasureTheory.SigmaFinite ν]
    (N : LevyStochCalc.Poisson.PoissonRandomMeasure P ν)
    (ℱ : MeasureTheory.Filtration ℝ ‹MeasurableSpace Ω›)
    (hℱ : LevyStochCalc.Poisson.IsPoissonFiltration N ℱ)
    (φ : Ω → ℝ → E → ℝ)
    (h_meas : Measurable fun p : Ω × ℝ × E => φ p.1 p.2.1 p.2.2)
    (h_progMeas : Probability.MarkedProgressivelyMeasurable ℱ φ)
    (h_sq : ∀ T : ℝ, 0 < T →
      ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T, ∫⁻ e,
        (‖φ ω s e‖₊ : ℝ≥0∞) ^ 2 ∂ν ∂volume ∂P < ⊤)
    {T : ℝ} (hT : 0 ≤ T) :
    ∫⁻ ω, (‖LevyStochCalc.Poisson.Compensated.stochasticIntegral N ℱ hℱ φ h_meas h_progMeas
      h_sq T ω‖₊ : ℝ≥0∞) ^ 2 ∂P
      = ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T, ∫⁻ e,
          (‖φ ω s e‖₊ : ℝ≥0∞) ^ 2 ∂ν ∂volume ∂P := by
  rw [← LevyStochCalc.Poisson.Compensated.process_lintegral_sq' N ℱ hℱ φ h_meas h_progMeas
    h_sq hT]
  refine lintegral_congr_ae ?_
  filter_upwards [LevyStochCalc.Poisson.Compensated.stochasticIntegral_ae_eq_process N ℱ hℱ φ
    h_meas h_progMeas h_sq T] with ω hω
  rw [hω]
omit [MeasurableSpace E] in
/-- **Second moment of the diffusion component**, by the Itô isometry applied to each of the
`d` component integrals. -/
theorem lintegral_sq_picardStep_diffusion_le
    (W : LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion P d)
    (ℱ : MeasureTheory.Filtration ℝ ‹MeasurableSpace Ω›)
    (hℱW : ∀ j : Fin d, LevyStochCalc.Brownian.IsBrownianFiltration (W.W j) ℱ)
    (coeffs : LevyStochCalc.Ito.Setting.JumpDiffusionCoeffs n d E)
    (X : ℝ → Ω → (Fin n → ℝ))
    (h_meas : ∀ i : Fin n, ∀ j : Fin d,
      Measurable (Function.uncurry (fun ω s => coeffs.σ s (X s ω) i j)))
    (h_progMeas : ∀ i : Fin n, ∀ j : Fin d,
        Probability.ProgressivelyMeasurable ℱ (fun ω s => coeffs.σ s (X s ω) i j))
    (h_sq : ∀ i : Fin n, ∀ j : Fin d, ∀ T : ℝ, 0 < T →
      ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
        (‖coeffs.σ s (X s ω) i j‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤)
    (i : Fin n) {t : ℝ} (ht : 0 ≤ t) :
    ∫⁻ ω, (‖picardStep_diffusion W ℱ hℱW coeffs X h_meas h_progMeas h_sq t ω i‖₊ : ℝ≥0∞) ^ 2 ∂P
      ≤ (d : ℝ≥0∞) * ∑ j : Fin d, ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) t,
          (‖coeffs.σ s (X s ω) i j‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P := by
  set M : Fin d → Ω → ℝ := fun j ω =>
    LevyStochCalc.Brownian.Ito.stochasticIntegral (W.W j) ℱ (hℱW j)
      (fun ω' s => coeffs.σ s (X s ω') i j)
      (h_meas i j) (h_progMeas i j) (h_sq i j) t ω with hM
  have hM_meas : ∀ j : Fin d, Measurable (M j) := by
    intro j
    obtain ⟨Filt, hMart⟩ := LevyStochCalc.Brownian.Ito.martingale_stochasticIntegral
      (W.W j) ℱ (hℱW j) (fun ω' s => coeffs.σ s (X s ω') i j)
      (h_meas i j) (h_progMeas i j) (h_sq i j)
    exact (hMart.stronglyMeasurable t).measurable.mono (Filt.le t) le_rfl
  have hunfold : ∀ ω : Ω,
      picardStep_diffusion W ℱ hℱW coeffs X h_meas h_progMeas h_sq t ω i
        = ∑ j : Fin d, M j ω := by
    intro ω
    simp only [picardStep_diffusion,
      LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion.stochasticIntegral, M]
  calc ∫⁻ ω, (‖picardStep_diffusion W ℱ hℱW coeffs X h_meas h_progMeas h_sq t ω i‖₊
        : ℝ≥0∞) ^ 2 ∂P
      = ∫⁻ ω, (‖∑ j : Fin d, M j ω‖₊ : ℝ≥0∞) ^ 2 ∂P :=
        lintegral_congr fun ω => by rw [hunfold ω]
    _ ≤ ∫⁻ ω, (d : ℝ≥0∞) * ∑ j : Fin d, (‖M j ω‖₊ : ℝ≥0∞) ^ 2 ∂P := by
        refine lintegral_mono fun ω => ?_
        simpa using sq_nnnorm_sum_le (Finset.univ : Finset (Fin d)) (fun j => M j ω)
    _ = (d : ℝ≥0∞) * ∑ j : Fin d, ∫⁻ ω, (‖M j ω‖₊ : ℝ≥0∞) ^ 2 ∂P := by
        rw [MeasureTheory.lintegral_const_mul' _ _ (by simp : (d : ℝ≥0∞) ≠ ⊤),
          MeasureTheory.lintegral_finsetSum]
        exact fun j _ => ((hM_meas j).nnnorm.coe_nnreal_ennreal).pow_const 2
    _ = (d : ℝ≥0∞) * ∑ j : Fin d, ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) t,
          (‖coeffs.σ s (X s ω) i j‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P := by
        refine congrArg _ (Finset.sum_congr rfl fun j _ => ?_)
        exact itoIsometry_of_nonneg (W.W j) ℱ (hℱW j)
          (fun ω' s => coeffs.σ s (X s ω') i j)
          (h_meas i j) (h_progMeas i j) (h_sq i j) ht
/-- **Second moment of the jump component**, by the Itô–Lévy isometry. -/
theorem lintegral_sq_picardStep_jump_eq {ν : MeasureTheory.Measure E}
    [MeasureTheory.SigmaFinite ν]
    (N : LevyStochCalc.Poisson.PoissonRandomMeasure P ν)
    (ℱ : MeasureTheory.Filtration ℝ ‹MeasurableSpace Ω›)
    (hℱN : LevyStochCalc.Poisson.IsPoissonFiltration N ℱ)
    (coeffs : LevyStochCalc.Ito.Setting.JumpDiffusionCoeffs n d E)
    (X : ℝ → Ω → (Fin n → ℝ))
    (h_meas : ∀ i : Fin n,
      Measurable (fun p : Ω × ℝ × E => coeffs.γ p.2.1 (X p.2.1 p.1) p.2.2 i))
    (h_progMeas : ∀ i : Fin n,
        Probability.MarkedProgressivelyMeasurable ℱ (fun ω s e => coeffs.γ s (X s ω) e i))
    (h_sq : ∀ i : Fin n, ∀ T : ℝ, 0 < T →
      ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T, ∫⁻ e,
        (‖coeffs.γ s (X s ω) e i‖₊ : ℝ≥0∞) ^ 2 ∂ν ∂volume ∂P < ⊤)
    (i : Fin n) {t : ℝ} (ht : 0 ≤ t) :
    ∫⁻ ω, (‖picardStep_jump N ℱ hℱN coeffs X h_meas h_progMeas h_sq t ω i‖₊ : ℝ≥0∞) ^ 2 ∂P
      = ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) t, ∫⁻ e,
          (‖coeffs.γ s (X s ω) e i‖₊ : ℝ≥0∞) ^ 2 ∂ν ∂volume ∂P :=
  compensatedIsometry_of_nonneg N ℱ hℱN
    (fun ω s e => coeffs.γ s (X s ω) e i) (h_meas i) (h_progMeas i) (h_sq i) ht
/-- The extended norm of a square. -/
theorem enorm_sq_eq (x : ℝ) : ‖x ^ 2‖ₑ = (‖x‖₊ : ℝ≥0∞) ^ 2 := by
  rw [← ENNReal.coe_pow, ← nnnorm_pow]
  rfl
omit [MeasurableSpace E] [MeasureTheory.IsProbabilityMeasure P] in
/-- A function with finite energy on a bounded window is `L²` there. -/
theorem memLp_two_of_lintegral_sq_lt_top {f : ℝ → ℝ} (hf : Measurable f) {b : ℝ}
    (hfin : ∫⁻ s in Set.Icc (0 : ℝ) b, (‖f s‖₊ : ℝ≥0∞) ^ 2 ∂volume < ⊤) :
    MeasureTheory.MemLp f 2 (volume.restrict (Set.Icc (0 : ℝ) b)) := by
  refine (MeasureTheory.memLp_two_iff_integrable_sq hf.aestronglyMeasurable).mpr ?_
  refine ⟨(hf.pow_const 2).aestronglyMeasurable, ?_⟩
  rw [MeasureTheory.hasFiniteIntegral_iff_enorm]
  exact lt_of_le_of_lt (le_of_eq (lintegral_congr fun s => enorm_sq_eq (f s))) hfin
omit [MeasurableSpace E] [MeasureTheory.IsProbabilityMeasure P] in
/-- A function with finite energy on a bounded window is integrable there. -/
theorem integrableOn_of_lintegral_sq_lt_top {f : ℝ → ℝ} (hf : Measurable f) {b : ℝ}
    (hfin : ∫⁻ s in Set.Icc (0 : ℝ) b, (‖f s‖₊ : ℝ≥0∞) ^ 2 ∂volume < ⊤) :
    MeasureTheory.IntegrableOn f (Set.Icc (0 : ℝ) b) volume := by
  haveI : MeasureTheory.IsFiniteMeasure (volume.restrict (Set.Icc (0 : ℝ) b)) :=
    ⟨by rw [MeasureTheory.Measure.restrict_apply_univ, Real.volume_Icc]
        exact ENNReal.ofReal_lt_top⟩
  exact (memLp_two_of_lintegral_sq_lt_top hf hfin).integrable (by norm_num)
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


