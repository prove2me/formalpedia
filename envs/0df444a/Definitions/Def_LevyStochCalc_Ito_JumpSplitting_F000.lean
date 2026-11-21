-- Prove2me | Definitions.Def_LevyStochCalc_Ito_JumpSplitting_F000
-- name    : LevyStochCalc_Ito_JumpSplitting_F000
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-20T19:33:32.622918+00:00
-- url     : https://prove2.me/theorems/8ca03912-4278-4f78-af90-ef3c54372c73
-- title:
--   Source declarations: LevyStochCalc.Ito.JumpSplitting
-- statement:
--   Source-preserving extracted declarations from LevyStochCalc.Ito.JumpSplitting. Existing definitions, lemmas, instances, proofs and elaboration context are retained; generated import closure remains under review.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Brownian_VectorItoProcess_F003
import Definitions.Def_LevyStochCalc_Ito_Setting_F000
import Definitions.Def_LevyStochCalc_Poisson_PathwiseIdentity_F001

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# Finite-activity splitting of a jump diffusion

A jump diffusion whose jump coefficient is carried by a mark set of finite intensity is the sum
of a vector Itô process and a pathwise jump sum. The compensated Poisson integral of such a
coefficient is the pathwise integral against the random measure minus the integral against the
reference intensity, and the latter is an absolutely continuous drift, so it can be absorbed into
the drift of the Itô part.

## Main definitions

* `LevyStochCalc.Ito.JumpSplitting.jumpSum` — the pathwise sum of the jumps carried by a mark set
  over a time window.
* `LevyStochCalc.Ito.JumpSplitting.continuousDrift` — the drift of a jump diffusion with the jump
  compensator subtracted.

## Main statements

* `LevyStochCalc.Ito.JumpSplitting.eq_vectorItoProcess_add_jumpSum` — at every nonnegative time a
  jump diffusion is almost surely the sum of the vector Itô process with diffusion `σ` and drift
  `continuousDrift`, and the pathwise jump sum.

## References

* Applebaum, *Lévy Processes and Stochastic Calculus*, 2009, §6.2.
* Ikeda–Watanabe, *SDEs and Diffusion Processes*, 1989, §IV.
-/

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

namespace LevyStochCalc.Ito.JumpSplitting

universe u v

section ENNRealAux

/-- The square of a sum in `ℝ≥0∞` is at most four times the sum of the squares. -/
theorem sq_add_le_four_mul (a b : ℝ≥0∞) : (a + b) ^ 2 ≤ 4 * (a ^ 2 + b ^ 2) := by
  rcases le_total a b with h | h
  · calc (a + b) ^ 2 ≤ (b + b) ^ 2 := by gcongr
      _ = 4 * b ^ 2 := by ring
      _ ≤ 4 * (a ^ 2 + b ^ 2) := mul_le_mul' le_rfl le_add_self
  · calc (a + b) ^ 2 ≤ (a + a) ^ 2 := by gcongr
      _ = 4 * a ^ 2 := by ring
      _ ≤ 4 * (a ^ 2 + b ^ 2) := mul_le_mul' le_rfl le_self_add
/-- A bound by a product of square roots squares to a bound by the product. -/
theorem sq_le_of_le_mul_rpow {x a b : ℝ≥0∞} (h : x ≤ a ^ (2 : ℝ)⁻¹ * b ^ (2 : ℝ)⁻¹) :
    x ^ 2 ≤ a * b := by
  refine le_trans (pow_le_pow_left' h 2) (le_of_eq ?_)
  rw [← ENNReal.mul_rpow_of_nonneg _ _ (by norm_num : (0 : ℝ) ≤ (2 : ℝ)⁻¹),
    ← ENNReal.rpow_natCast ((a * b) ^ (2 : ℝ)⁻¹) 2, ← ENNReal.rpow_mul]
  norm_num
end ENNRealAux

section Comparison

variable {α : Type*} [MeasurableSpace α] {μ : Measure α}

/-- Over a finite measure the mean size is at most the root mean square times the square root of
the total mass. -/
theorem lintegral_enorm_le_rms [IsFiniteMeasure μ] (f : α → ℝ) (hf : AEStronglyMeasurable f μ) :
    ∫⁻ a, ‖f a‖ₑ ∂μ ≤ (∫⁻ a, ‖f a‖ₑ ^ 2 ∂μ) ^ (2 : ℝ)⁻¹ * μ Set.univ ^ (2 : ℝ)⁻¹ := by
  have hcmp := eLpNorm_le_eLpNorm_mul_rpow_measure_univ (μ := μ) (f := f)
    (p := 1) (q := 2) (by norm_num) hf
  have h2 : eLpNorm f 2 μ = (∫⁻ a, ‖f a‖ₑ ^ 2 ∂μ) ^ (2 : ℝ)⁻¹ := by
    rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (by norm_num) (by norm_num)]
    norm_num
  rw [eLpNorm_one_eq_lintegral_enorm, h2] at hcmp
  refine hcmp.trans (le_of_eq ?_)
  norm_num
/-- A square-integrable function on a bounded time window is integrable there. -/
theorem integrableOn_Icc_of_lintegral_sq_lt_top {T : ℝ} {f : ℝ → ℝ}
    (hf : AEStronglyMeasurable f (volume.restrict (Set.Icc (0 : ℝ) T)))
    (h : ∫⁻ s in Set.Icc (0 : ℝ) T, (‖f s‖₊ : ℝ≥0∞) ^ 2 ∂volume < ⊤) :
    IntegrableOn f (Set.Icc (0 : ℝ) T) volume := by
  haveI : IsFiniteMeasure (volume.restrict (Set.Icc (0 : ℝ) T)) :=
    ⟨by rw [Measure.restrict_apply_univ]; exact isCompact_Icc.measure_lt_top⟩
  refine ⟨hf, lt_of_le_of_lt (lintegral_enorm_le_rms f hf) ?_⟩
  refine ENNReal.mul_lt_top (ENNReal.rpow_lt_top_of_nonneg (by norm_num) h.ne) ?_
  exact ENNReal.rpow_lt_top_of_nonneg (by norm_num) (measure_ne_top _ _)
end Comparison

section Setup

variable {Ω : Type u} [MeasurableSpace Ω] {E : Type v} [MeasurableSpace E]
  {P : Measure Ω} [IsProbabilityMeasure P] {ν : Measure E} [SigmaFinite ν]
  {n d : ℕ}
  {W : LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion P d}
  {N : LevyStochCalc.Poisson.PoissonRandomMeasure P ν}
  {coeffs : Setting.JumpDiffusionCoeffs n d E} {x₀ : Fin n → ℝ}

/-- The reference intensity restricted to a time window times a mark set is the product of
Lebesgue measure on the window with the mark measure restricted to the mark set. -/
theorem restrict_referenceIntensity_window (A : Set E) (T : ℝ) :
    (LevyStochCalc.Poisson.referenceIntensity ν).restrict (Set.Ioc (0 : ℝ) T ×ˢ A)
      = (volume.restrict (Set.Ioc (0 : ℝ) T)).prod (ν.restrict A) := by
  have hsub : Set.Ioc (0 : ℝ) T ∩ Set.Ici (0 : ℝ) = Set.Ioc (0 : ℝ) T := by
    ext x
    simp only [Set.mem_inter_iff, Set.mem_Ioc, Set.mem_Ici, and_iff_left_iff_imp]
    exact fun h => h.1.le
  rw [LevyStochCalc.Poisson.referenceIntensity, ← Measure.prod_restrict,
    Measure.restrict_restrict measurableSet_Ioc, hsub]
/-- On a window of finite intensity the integral against the reference intensity is the iterated
integral over times and marks, whose inner integral is integrable in time. -/
theorem integral_window_eq_and_integrableOn (g : ℝ → E → ℝ) {A : Set E} {T : ℝ}
    (hg : IntegrableOn (fun q : ℝ × E => g q.1 q.2) (Set.Ioc (0 : ℝ) T ×ˢ A)
      (LevyStochCalc.Poisson.referenceIntensity ν)) :
    (∫ q in Set.Ioc (0 : ℝ) T ×ˢ A, g q.1 q.2
          ∂(LevyStochCalc.Poisson.referenceIntensity ν)
        = ∫ s in Set.Icc (0 : ℝ) T, (∫ e in A, g s e ∂ν) ∂volume)
      ∧ IntegrableOn (fun s => ∫ e in A, g s e ∂ν) (Set.Icc (0 : ℝ) T) volume := by
  have hg' : Integrable (fun q : ℝ × E => g q.1 q.2)
      ((volume.restrict (Set.Ioc (0 : ℝ) T)).prod (ν.restrict A)) := by
    rw [← restrict_referenceIntensity_window (ν := ν) A T]
    exact hg
  refine ⟨?_, ?_⟩
  · rw [show (LevyStochCalc.Poisson.referenceIntensity ν).restrict (Set.Ioc (0 : ℝ) T ×ˢ A)
        = (volume.restrict (Set.Ioc (0 : ℝ) T)).prod (ν.restrict A) from
      restrict_referenceIntensity_window A T,
      integral_prod (fun q : ℝ × E => g q.1 q.2) hg', integral_Icc_eq_integral_Ioc]
  · exact IntegrableOn.congr_set_ae hg'.integral_prod_left (MeasureTheory.Ioc_ae_eq_Icc).symm
/-- The pathwise sum of the jumps carried by the mark set `A` over the window `(0, t]`. -/
noncomputable def jumpSum (X : Setting.JumpDiffusion W N coeffs x₀) (A : Set E) (t : ℝ) (ω : Ω)
    (i : Fin n) : ℝ :=
  ∫ q in Set.Ioc (0 : ℝ) t ×ˢ A, coeffs.γ q.1 (X.X q.1 ω) q.2 i ∂(N.N ω)
/-- The drift of a jump diffusion with the compensator of the jumps carried by `A` subtracted. -/
noncomputable def continuousDrift (X : Setting.JumpDiffusion W N coeffs x₀) (A : Set E)
    (i : Fin n) (ω : Ω) (s : ℝ) : ℝ :=
  coeffs.μ s (X.X s ω) i - ∫ e in A, coeffs.γ s (X.X s ω) e i ∂ν
/-- The jump sum over the degenerate window vanishes. -/
theorem jumpSum_zero (X : Setting.JumpDiffusion W N coeffs x₀) (A : Set E) (ω : Ω) (i : Fin n) :
    jumpSum X A 0 ω i = 0 := by
  simp [jumpSum]
section Regularity

variable (X : Setting.JumpDiffusion W N coeffs x₀) (A : Set E) (i : Fin n)

/-- The compensator of the jumps carried by `A`, as a function of the sample point and time. -/
theorem stronglyMeasurable_markIntegral
    (hγm : Measurable fun p : Ω × ℝ × E => coeffs.γ p.2.1 (X.X p.2.1 p.1) p.2.2 i) :
    StronglyMeasurable fun p : Ω × ℝ => ∫ e in A, coeffs.γ p.2 (X.X p.2 p.1) e i ∂ν :=
  (hγm.comp MeasurableEquiv.prodAssoc.measurable).stronglyMeasurable.integral_prod_right'
    (ν := ν.restrict A)
/-- The drift with the compensator subtracted is jointly measurable. -/
theorem measurable_continuousDrift
    (hμm : Measurable (Function.uncurry fun ω s => coeffs.μ s (X.X s ω) i))
    (hγm : Measurable fun p : Ω × ℝ × E => coeffs.γ p.2.1 (X.X p.2.1 p.1) p.2.2 i) :
    Measurable (Function.uncurry (continuousDrift X A i)) :=
  hμm.sub (stronglyMeasurable_markIntegral X A i hγm).measurable
end Regularity

section Splitting

variable (X : Setting.JumpDiffusion W N coeffs x₀) (ℱ : Filtration ℝ ‹MeasurableSpace Ω›)
  (hℱW : ∀ j : Fin d, LevyStochCalc.Brownian.IsBrownianFiltration (W.W j) ℱ)
  (hσm : ∀ (i : Fin n) (j : Fin d),
    Measurable (Function.uncurry fun ω s => coeffs.σ s (X.X s ω) i j))
  (hσp : ∀ (i : Fin n) (j : Fin d),
    Probability.ProgressivelyMeasurable ℱ fun ω s => coeffs.σ s (X.X s ω) i j)
  (hσq : ∀ (i : Fin n) (j : Fin d) (T : ℝ), 0 < T →
    ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
      (‖coeffs.σ s (X.X s ω) i j‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤)

variable (hℱN : LevyStochCalc.Poisson.IsPoissonFiltration N ℱ)
  (hγm : ∀ i : Fin n,
    Measurable fun p : Ω × ℝ × E => coeffs.γ p.2.1 (X.X p.2.1 p.1) p.2.2 i)
  (hγp : ∀ i : Fin n,
    Probability.MarkedProgressivelyMeasurable ℱ fun ω s e => coeffs.γ s (X.X s ω) e i)
  (hγq : ∀ (i : Fin n) (T : ℝ), 0 < T →
    ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T, ∫⁻ e,
      (‖coeffs.γ s (X.X s ω) e i‖₊ : ℝ≥0∞) ^ 2 ∂ν ∂volume ∂P < ⊤)

end Splitting

end Setup

end LevyStochCalc.Ito.JumpSplitting


