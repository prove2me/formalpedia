-- Prove2me | Definitions.Def_SourceProof_5c5d38cdf193b77dbdd4c35d
-- name    : SourceProof_5c5d38cdf193b77dbdd4c35d
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-21T12:39:57.478188+00:00
-- url     : https://prove2.me/theorems/f4420dff-8dde-431f-a9f3-998adb411b58
-- title:
--   LevyStochCalc source module: SourceProof_5c5d38cdf193b77dbdd4c35d
-- statement:
--   The original source theorem `LevyStochCalc.Ito.JumpFormula.tendsto_setIntegral_of_dominated_ae` comes from the `LevyStochCalc.Ito.ItoLevyBoundedDerivsStepsLimits` module. The staged Lean declaration includes its source proof and dependency references.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Ito_ItoLevyBoundedDerivsStepsIntegrands_F000
import Definitions.Def_LevyStochCalc_Ito_ItoLevyBoundedDerivsStepsIntegrands_F001

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# Limit steps of the Itô–Lévy formula at bounded derivatives

Along a family of paths converging to the solution of a jump diffusion at almost every time of a
window, the four term families of the Itô–Lévy formula converge to their counterparts along the
solution: the Brownian integrals of the mixed diffusion integrands and the compensated integrals
of the cut mixed jump increments converge in `L²`, and the mixed drift and compensator-drift
integrals converge almost surely. The compensator-drift step rests on a form of dominated
convergence for a mark integral over a shrinking family of cuts in which the domination and the
pointwise convergence are asked at almost every time of the window only.
-/

open MeasureTheory ProbabilityTheory Filter Topology
open scoped NNReal ENNReal
open LevyStochCalc.Ito.Setting LevyStochCalc.Poisson.Compensated LevyStochCalc.Probability

namespace LevyStochCalc.Ito.JumpFormula

universe u v

section DominatedAe

variable {E : Type v} [MeasurableSpace E] {ν : Measure E} [SigmaFinite ν]


theorem _root_.Prove2MeSourceProof.h_5c5d38cdf193b77dbdd4c35d
    {T : ℝ} {A : ℕ → Set E} {fs : ℕ → ℝ → E → ℝ} {f g : ℝ → E → ℝ}
    (hA : ∀ m, MeasurableSet (A m))
    (hev : ∀ᵐ e ∂ν, ∀ᶠ m in atTop, e ∉ A m)
    (hmeas : ∀ m, AEStronglyMeasurable (fun p : ℝ × E => fs m p.1 p.2)
      ((volume.restrict (Set.Icc (0 : ℝ) T)).prod ν))
    (hg : Integrable (fun p : ℝ × E => g p.1 p.2)
      ((volume.restrict (Set.Icc (0 : ℝ) T)).prod ν))
    (hdom : ∀ m, ∀ᵐ s ∂(volume.restrict (Set.Icc (0 : ℝ) T)), ∀ e, |fs m s e| ≤ g s e)
    (hconv : ∀ᵐ s ∂(volume.restrict (Set.Icc (0 : ℝ) T)), ∀ e,
      Tendsto (fun m => fs m s e) atTop (𝓝 (f s e))) :
    Tendsto (fun m => ∫ s in Set.Icc (0 : ℝ) T, ∫ e in (A m)ᶜ, fs m s e ∂ν) atTop
      (𝓝 (∫ s in Set.Icc (0 : ℝ) T, ∫ e, f s e ∂ν)) := by
  classical
  have hwin : ∀ᵐ p ∂((volume.restrict (Set.Icc (0 : ℝ) T)).prod ν),
      (∀ m, ∀ e, |fs m p.1 e| ≤ g p.1 e) ∧
        ∀ e, Tendsto (fun m => fs m p.1 e) atTop (𝓝 (f p.1 e)) :=
    Measure.quasiMeasurePreserving_fst.ae ((MeasureTheory.ae_all_iff.mpr hdom).and hconv)
  have hevp : ∀ᵐ p ∂((volume.restrict (Set.Icc (0 : ℝ) T)).prod ν),
      ∀ᶠ m in atTop, p.2 ∉ A m :=
    Measure.quasiMeasurePreserving_snd.ae hev
  have hSm : ∀ m, MeasurableSet {p : ℝ × E | p.2 ∈ (A m)ᶜ} := fun m =>
    measurable_snd (hA m).compl
  set F : ℕ → ℝ × E → ℝ :=
    fun m => {p : ℝ × E | p.2 ∈ (A m)ᶜ}.indicator (fun q => fs m q.1 q.2) with hF
  have hFmeas : ∀ m, AEStronglyMeasurable (F m)
      ((volume.restrict (Set.Icc (0 : ℝ) T)).prod ν) :=
    fun m => (hmeas m).indicator (hSm m)
  have hbound : ∀ m, ∀ᵐ p ∂((volume.restrict (Set.Icc (0 : ℝ) T)).prod ν),
      ‖F m p‖ ≤ g p.1 p.2 := by
    intro m
    filter_upwards [hwin] with p hp
    have hle : |fs m p.1 p.2| ≤ g p.1 p.2 := hp.1 m p.2
    by_cases hpS : p ∈ {q : ℝ × E | q.2 ∈ (A m)ᶜ}
    · rw [hF]
      simp only [Set.indicator_of_mem hpS, Real.norm_eq_abs]
      exact hle
    · rw [hF]
      simp only [Set.indicator_of_notMem hpS, norm_zero]
      exact le_trans (abs_nonneg _) hle
  have hlim : ∀ᵐ p ∂((volume.restrict (Set.Icc (0 : ℝ) T)).prod ν),
      Tendsto (fun m => F m p) atTop (𝓝 (f p.1 p.2)) := by
    filter_upwards [hwin, hevp] with p hp hpe
    refine Tendsto.congr' ?_ (hp.2 p.2)
    filter_upwards [hpe] with m hm
    have hpS : p ∈ {q : ℝ × E | q.2 ∈ (A m)ᶜ} := hm
    rw [hF]
    simp only [Set.indicator_of_mem hpS]
  have hDCT := tendsto_integral_of_dominated_convergence
    (μ := (volume.restrict (Set.Icc (0 : ℝ) T)).prod ν) (F := F)
    (f := fun p : ℝ × E => f p.1 p.2) (fun p : ℝ × E => g p.1 p.2)
    hFmeas hg hbound hlim
  have hLHS : ∀ m, ∫ p, F m p ∂((volume.restrict (Set.Icc (0 : ℝ) T)).prod ν)
      = ∫ s in Set.Icc (0 : ℝ) T, ∫ e in (A m)ᶜ, fs m s e ∂ν := by
    intro m
    have hint : Integrable (F m) ((volume.restrict (Set.Icc (0 : ℝ) T)).prod ν) :=
      hg.mono' (hFmeas m) (hbound m)
    rw [integral_prod _ hint]
    refine integral_congr_ae (Eventually.of_forall fun s => ?_)
    change ∫ e, F m (s, e) ∂ν = ∫ e in (A m)ᶜ, fs m s e ∂ν
    have hfun : (fun e => F m (s, e)) = ((A m)ᶜ).indicator (fun e => fs m s e) := by
      funext e
      by_cases he : e ∈ (A m)ᶜ
      · rw [hF]
        simp only [Set.indicator_of_mem he, Set.indicator_of_mem (show (s, e) ∈
          {q : ℝ × E | q.2 ∈ (A m)ᶜ} from he)]
      · rw [hF]
        simp only [Set.indicator_of_notMem he, Set.indicator_of_notMem (show (s, e) ∉
          {q : ℝ × E | q.2 ∈ (A m)ᶜ} from he)]
    rw [hfun, integral_indicator (hA m).compl]
  have hmlim : AEStronglyMeasurable (fun p : ℝ × E => f p.1 p.2)
      ((volume.restrict (Set.Icc (0 : ℝ) T)).prod ν) :=
    aestronglyMeasurable_of_tendsto_ae atTop hFmeas hlim
  have hblim : ∀ᵐ p ∂((volume.restrict (Set.Icc (0 : ℝ) T)).prod ν),
      ‖f p.1 p.2‖ ≤ g p.1 p.2 := by
    filter_upwards [MeasureTheory.ae_all_iff.mpr hbound, hlim] with p hb hl
    exact le_of_tendsto hl.norm (Eventually.of_forall hb)
  have hRHS : ∫ p, f p.1 p.2 ∂((volume.restrict (Set.Icc (0 : ℝ) T)).prod ν)
      = ∫ s in Set.Icc (0 : ℝ) T, ∫ e, f s e ∂ν :=
    integral_prod _ (hg.mono' hmlim hblim)
  simp_rw [hLHS] at hDCT
  rwa [hRHS] at hDCT
end DominatedAe

section Mixed

open LevyStochCalc.Ito.BigJump LevyStochCalc.Brownian.Multidim LevyStochCalc.Brownian.Ito

variable {Ω : Type u} [MeasurableSpace Ω] {E : Type v} [MeasurableSpace E]
  {P : Measure Ω} [IsProbabilityMeasure P] {ν : Measure E} [SigmaFinite ν] {n d : ℕ}
  {W : MultidimBrownianMotion P d} {N : LevyStochCalc.Poisson.PoissonRandomMeasure P ν}
  {coeffs : JumpDiffusionCoeffs n d E} {x₀ : Fin n → ℝ} {X : JumpDiffusion W N coeffs x₀}
  {u : ℝ → (Fin n → ℝ) → ℝ}

end Mixed

end LevyStochCalc.Ito.JumpFormula


