-- Prove2me | Definitions.Def_LevyStochCalc_Ito_JumpSplitting_F001
-- name    : LevyStochCalc_Ito_JumpSplitting_F001
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-20T19:37:52.715175+00:00
-- url     : https://prove2.me/theorems/fc456501-84aa-4c83-99fe-36ac34401e39
-- title:
--   Source declarations: LevyStochCalc.Ito.JumpSplitting
-- statement:
--   Source-preserving extracted declarations from LevyStochCalc.Ito.JumpSplitting. Existing definitions, lemmas, instances, proofs and elaboration context are retained; generated import closure remains under review.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Ito_JumpSplitting_F000
import Definitions.Def_SourceProof_36f7727cdf4c604558c9da84

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

end ENNRealAux

section Comparison

variable {α : Type*} [MeasurableSpace α] {μ : Measure α}

end Comparison

section Setup

variable {Ω : Type u} [MeasurableSpace Ω] {E : Type v} [MeasurableSpace E]
  {P : Measure Ω} [IsProbabilityMeasure P] {ν : Measure E} [SigmaFinite ν]
  {n d : ℕ}
  {W : LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion P d}
  {N : LevyStochCalc.Poisson.PoissonRandomMeasure P ν}
  {coeffs : Setting.JumpDiffusionCoeffs n d E} {x₀ : Fin n → ℝ}

section Regularity

variable (X : Setting.JumpDiffusion W N coeffs x₀) (A : Set E) (i : Fin n)

/-- The drift with the compensator subtracted is progressively measurable. -/
theorem progressivelyMeasurable_continuousDrift (ℱ : Filtration ℝ ‹MeasurableSpace Ω›)
    (hμp : Probability.ProgressivelyMeasurable ℱ fun ω s => coeffs.μ s (X.X s ω) i)
    (hγp : Probability.MarkedProgressivelyMeasurable ℱ
      fun ω s e => coeffs.γ s (X.X s ω) e i) :
    Probability.ProgressivelyMeasurable ℱ (continuousDrift X A i) :=
  hμp.sub (_root_.Prove2MeSourceProof.h_36f7727cdf4c604558c9da84 A ℱ hγp)
/-- The energy of the compensator over a window is at most the mark set's intensity times the
energy of the jump coefficient. -/
theorem lintegral_sq_markIntegral_le (hAν : ν A ≠ ⊤)
    (hγm : Measurable fun p : Ω × ℝ × E => coeffs.γ p.2.1 (X.X p.2.1 p.1) p.2.2 i) (T : ℝ) :
    (∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
        (‖∫ e in A, coeffs.γ s (X.X s ω) e i ∂ν‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P)
      ≤ (∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T, ∫⁻ e,
          (‖coeffs.γ s (X.X s ω) e i‖₊ : ℝ≥0∞) ^ 2 ∂ν ∂volume ∂P) * ν A := by
  haveI hfin : IsFiniteMeasure (ν.restrict A) :=
    ⟨by rw [Measure.restrict_apply_univ]; exact lt_top_iff_ne_top.mpr hAν⟩
  have hslice : ∀ (ω : Ω) (s : ℝ), Measurable fun e => coeffs.γ s (X.X s ω) e i := by
    intro ω s
    exact hγm.comp (measurable_const.prodMk (measurable_const.prodMk measurable_id))
  have hpt : ∀ (ω : Ω) (s : ℝ),
      (‖∫ e in A, coeffs.γ s (X.X s ω) e i ∂ν‖₊ : ℝ≥0∞) ^ 2
        ≤ (∫⁻ e, (‖coeffs.γ s (X.X s ω) e i‖₊ : ℝ≥0∞) ^ 2 ∂ν) * ν A := by
    intro ω s
    have h1 : ‖∫ e in A, coeffs.γ s (X.X s ω) e i ∂ν‖ₑ
        ≤ (∫⁻ e in A, ‖coeffs.γ s (X.X s ω) e i‖ₑ ^ 2 ∂ν) ^ (2 : ℝ)⁻¹
          * (ν.restrict A) Set.univ ^ (2 : ℝ)⁻¹ :=
      le_trans (enorm_integral_le_lintegral_enorm _)
        (lintegral_enorm_le_rms _ (hslice ω s).stronglyMeasurable.aestronglyMeasurable)
    refine le_trans (sq_le_of_le_mul_rpow h1) ?_
    rw [Measure.restrict_apply_univ]
    exact mul_le_mul' (lintegral_mono' Measure.restrict_le_self le_rfl) le_rfl
  calc (∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
        (‖∫ e in A, coeffs.γ s (X.X s ω) e i ∂ν‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P)
      ≤ ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
          (∫⁻ e, (‖coeffs.γ s (X.X s ω) e i‖₊ : ℝ≥0∞) ^ 2 ∂ν) * ν A ∂volume ∂P :=
        lintegral_mono fun ω => lintegral_mono fun s => hpt ω s
    _ = ∫⁻ ω, (∫⁻ s in Set.Icc (0 : ℝ) T, ∫⁻ e,
          (‖coeffs.γ s (X.X s ω) e i‖₊ : ℝ≥0∞) ^ 2 ∂ν ∂volume) * ν A ∂P :=
        lintegral_congr fun ω => lintegral_mul_const' _ _ hAν
    _ = (∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T, ∫⁻ e,
          (‖coeffs.γ s (X.X s ω) e i‖₊ : ℝ≥0∞) ^ 2 ∂ν ∂volume ∂P) * ν A :=
        lintegral_mul_const' _ _ hAν
/-- The drift with the compensator subtracted has finite energy over every bounded window. -/
theorem lintegral_sq_continuousDrift_lt_top (hAν : ν A ≠ ⊤)
    (hμm : Measurable (Function.uncurry fun ω s => coeffs.μ s (X.X s ω) i))
    (hμq : ∀ T : ℝ, 0 < T → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
      (‖coeffs.μ s (X.X s ω) i‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤)
    (hγm : Measurable fun p : Ω × ℝ × E => coeffs.γ p.2.1 (X.X p.2.1 p.1) p.2.2 i)
    (hγq : ∀ T : ℝ, 0 < T → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T, ∫⁻ e,
      (‖coeffs.γ s (X.X s ω) e i‖₊ : ℝ≥0∞) ^ 2 ∂ν ∂volume ∂P < ⊤)
    (T : ℝ) (hT : 0 < T) :
    ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
      (‖continuousDrift X A i ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤ := by
  set M : Ω × ℝ → ℝ≥0∞ := fun p => (‖coeffs.μ p.2 (X.X p.2 p.1) i‖₊ : ℝ≥0∞) ^ 2 with hMdef
  set C : Ω × ℝ → ℝ≥0∞ :=
    fun p => (‖∫ e in A, coeffs.γ p.2 (X.X p.2 p.1) e i ∂ν‖₊ : ℝ≥0∞) ^ 2 with hCdef
  have hMmeas : Measurable M :=
    (ENNReal.continuous_coe.measurable.comp hμm.nnnorm).pow_const 2
  have hCmeas : Measurable C :=
    (ENNReal.continuous_coe.measurable.comp
      (stronglyMeasurable_markIntegral X A i hγm).measurable.nnnorm).pow_const 2
  have hbound : ∀ (ω : Ω) (s : ℝ), (‖continuousDrift X A i ω s‖₊ : ℝ≥0∞) ^ 2
      ≤ 4 * (M (ω, s) + C (ω, s)) := by
    intro ω s
    exact le_trans (pow_le_pow_left' enorm_sub_le 2) (sq_add_le_four_mul _ _)
  have hinner : ∀ ω : Ω, ∫⁻ s in Set.Icc (0 : ℝ) T, (M (ω, s) + C (ω, s)) ∂volume
      = (∫⁻ s in Set.Icc (0 : ℝ) T, M (ω, s) ∂volume)
        + ∫⁻ s in Set.Icc (0 : ℝ) T, C (ω, s) ∂volume :=
    fun ω => lintegral_add_left (hMmeas.comp measurable_prodMk_left) _
  have houter : ∫⁻ ω, ((∫⁻ s in Set.Icc (0 : ℝ) T, M (ω, s) ∂volume)
        + ∫⁻ s in Set.Icc (0 : ℝ) T, C (ω, s) ∂volume) ∂P
      = (∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T, M (ω, s) ∂volume ∂P)
        + ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T, C (ω, s) ∂volume ∂P :=
    lintegral_add_left (hMmeas.lintegral_prod_right'
      (ν := volume.restrict (Set.Icc (0 : ℝ) T))) _
  have hCfin : ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T, C (ω, s) ∂volume ∂P < ⊤ := by
    refine lt_of_le_of_lt (lintegral_sq_markIntegral_le X A i hAν hγm T) ?_
    exact ENNReal.mul_lt_top (hγq T hT) (lt_top_iff_ne_top.mpr hAν)
  calc ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
        (‖continuousDrift X A i ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P
      ≤ ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T, 4 * (M (ω, s) + C (ω, s)) ∂volume ∂P :=
        lintegral_mono fun ω => lintegral_mono fun s => hbound ω s
    _ = 4 * ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T, (M (ω, s) + C (ω, s)) ∂volume ∂P := by
        rw [← lintegral_const_mul' _ _ (by norm_num : (4 : ℝ≥0∞) ≠ ⊤)]
        exact lintegral_congr fun ω =>
          lintegral_const_mul' (4 : ℝ≥0∞) _ (by norm_num)
    _ = 4 * ((∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T, M (ω, s) ∂volume ∂P)
          + ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T, C (ω, s) ∂volume ∂P) := by
        rw [lintegral_congr hinner, houter]
    _ < ⊤ := ENNReal.mul_lt_top (by norm_num) (ENNReal.add_lt_top.mpr ⟨hμq T hT, hCfin⟩)
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

/-- The multidimensional Brownian integral of a row of the diffusion coefficient is the
martingale part of the corresponding coordinate of a vector Itô process. -/
theorem multidimIntegral_eq_vectorItoMartingale (i : Fin n) (t : ℝ) (ω : Ω) :
    LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion.stochasticIntegral W ℱ hℱW
        (fun s ω => coeffs.σ s (X.X s ω) i) (fun j => hσm i j) (fun j => hσp i j)
        (fun j => hσq i j) t ω
      = LevyStochCalc.Brownian.Ito.vectorItoMartingale W ℱ hℱW
          (fun i j ω s => coeffs.σ s (X.X s ω) i j) hσm hσp hσq i t ω := rfl
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


