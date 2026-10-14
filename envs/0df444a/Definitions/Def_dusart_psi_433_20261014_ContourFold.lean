-- Prove2me | Definitions.Def_dusart_psi_433_20261014_ContourFold
-- name    : dusart_psi_433_20261014_ContourFold
-- status  : Definition
-- author  : @abcdefg
-- created : 2026-10-14T09:20:28.009498+00:00
-- url     : https://prove2.me/theorems/05ba12c9-45e2-41a1-9204-0fe11260edd6
-- title:
--   Dusart smoothing: Contour Fold
-- statement:
--   This module gives the complete contour fold component of Gaussian resampling for Chebyshev’s psi function. It is part of the direct formal proof of the parameter-dependent explicit prime-number-theorem error estimate. Its supporting analytic and numerical results are included with their proofs.
--
--   Formalization Note: The imported components are complete proof modules; no open theorem is assumed.
-- source:
--   Pierre Dusart, Estimates of Some Functions Over Primes without R.H., https://www.unilim.fr/pages_perso/pierre.dusart/Documents/HDR_Dusart.pdf, Theorem 45 and Lemmas 47–55, printed pp. 38–46; supporting analytic and numerical formalization.

import Definitions.Def_dusart_psi_433_20261014_ContourSymmetry
/- Copyright (c) 2026 Anthropic, PBC. Released under Apache 2.0.
Adapted from accepted contour-folding proofs on Prove2Me. -/
noncomputable section
namespace DusartSmoothing.RvM
open Complex Set MeasureTheory intervalIntegral
open DusartSmoothing.Contour

lemma path_point_facts {s : ℂ} (hre : 0 < s.re) (him : 1 ≤ s.im)
    (hgood : GoodHeight s.im) : s ≠ 1 ∧ riemannZeta s ≠ 0 := by
  have hs1 : s ≠ 1 := by
    intro hh; rw [hh] at him; simp at him; linarith
  refine ⟨hs1, fun hz => ?_⟩
  rcases lt_or_ge s.re 1 with hlt | hge
  · exact hgood s ⟨hz, hre, hlt⟩ rfl
  · exact riemannZeta_ne_zero_of_one_le_re hge hz

/-- Λ'/Λ is continuous at every point of height T whenever T ≥ 1 is a good height. -/
lemma continuousAt_logDeriv_completedZeta {s : ℂ} (him : 1 ≤ s.im) (hgood : GoodHeight s.im) :
    ContinuousAt (logDeriv completedRiemannZeta) s := by
  have hs0 : s ≠ 0 := by intro hh; rw [hh] at him; simp at him; linarith
  have hs1 : s ≠ 1 := by intro hh; rw [hh] at him; simp at him; linarith
  have hΛ := analyticAt_completedRiemannZeta hs0 hs1
  have hne : completedRiemannZeta s ≠ 0 := fun h =>
    hgood s (completedRiemannZeta_eq_zero_iff.mp h) rfl
  exact hΛ.deriv.continuousAt.div hΛ.continuousAt hne






theorem horizontal_fold {T : ℝ} (hT : 1 ≤ T) (hgood : GoodHeight T) :
    ∫ σ in (-1 : ℝ)..2, logDeriv completedRiemannZeta (σ + T * I)
      = 2 * I * ((∫ σ in (1 / 2 : ℝ)..2, logDeriv completedRiemannZeta (σ + T * I)).im : ℂ) := by
  set F := logDeriv completedRiemannZeta with hF
  have hcont : Continuous fun σ : ℝ => F (σ + T * I) := by
    refine continuous_iff_continuousAt.mpr fun σ => ?_
    have h := continuousAt_logDeriv_completedZeta (s := σ + T * I) (by simpa using hT)
      (by simpa using hgood)
    exact ContinuousAt.comp (f := fun σ : ℝ => (σ : ℂ) + T * I) h (by fun_prop)
  have hsplit := intervalIntegral.integral_add_adjacent_intervals
    (hcont.intervalIntegrable (μ := volume) (-1) (1 / 2))
    (hcont.intervalIntegrable (μ := volume) (1 / 2) 2)
  rw [← hsplit]
  set A := ∫ σ in (1 / 2 : ℝ)..2, F (σ + T * I) with hA
  -- the left piece is −conj A
  have hleft : ∫ σ in (-1 : ℝ)..(1 / 2), F (σ + T * I) = -starRingEnd ℂ A := by
    have hsub := intervalIntegral.integral_comp_sub_left (f := fun x : ℝ => F (x + T * I))
      (a := (1 / 2 : ℝ)) (b := 2) (1 : ℝ)
    norm_num at hsub
    -- hsub : ∫ x in 1/2..2, F (↑(1 - x) + T I) = ∫ x in -1..1/2, F (x + T I)   (up to cast shape)
    rw [← hsub, hA, ← intervalIntegral_conj, ← intervalIntegral.integral_neg]
    apply intervalIntegral.integral_congr
    intro x hx
    rw [uIcc_of_le (by norm_num)] at hx
    have hxpos : 0 < x := by linarith [hx.1]
    obtain ⟨hs1, hζ⟩ := path_point_facts (s := x + T * I) (by simpa using hxpos)
      (by simpa using hT) (by simpa using hgood)
    have key := logDeriv_completedZeta_one_sub_conj (s := x + T * I) (by simpa using hxpos) hs1 hζ
    have e : (1 : ℂ) - starRingEnd ℂ (x + T * I) = 1 - (x : ℂ) + T * I := by
      simp [Complex.ext_iff]
    simp only [hF] at key ⊢
    rw [← e, key]
  rw [hleft, neg_add_eq_sub, Complex.sub_conj]
  push_cast
  ring

theorem vertical_fold {T₁ T₂ : ℝ} (h1 : 1 ≤ T₁) (h12 : T₁ ≤ T₂) :
    ∫ t in T₁..T₂, logDeriv completedRiemannZeta (-1 + t * I)
      = -starRingEnd ℂ (∫ t in T₁..T₂, logDeriv completedRiemannZeta (2 + t * I)) := by
  rw [← intervalIntegral_conj, ← intervalIntegral.integral_neg]
  apply intervalIntegral.integral_congr
  intro t ht
  rw [uIcc_of_le h12] at ht
  have ht1 : 1 ≤ t := le_trans h1 ht.1
  have hs1 : (2 : ℂ) + t * I ≠ 1 := by
    intro hh; have := congrArg Complex.re hh; simp at this
  have hζ : riemannZeta (2 + t * I) ≠ 0 := riemannZeta_ne_zero_of_one_le_re (by simp)
  have key := logDeriv_completedZeta_one_sub_conj (s := 2 + t * I) (by simp) hs1 hζ
  have e : (1 : ℂ) - starRingEnd ℂ (2 + t * I) = -1 + t * I := by
    simp [Complex.ext_iff]; norm_num
  show logDeriv completedRiemannZeta (-1 + t * I)
    = -starRingEnd ℂ (logDeriv completedRiemannZeta (2 + t * I))
  rw [← e, key]

theorem rectangleIntegral_logDeriv_completedZeta_eq_halfContour {T₁ T₂ : ℝ} (h1 : 1 ≤ T₁)
    (h12 : T₁ < T₂) (hg1 : GoodHeight T₁) (hg2 : GoodHeight T₂) :
    RectangleIntegral (logDeriv completedRiemannZeta) (-1 + T₁ * I) (2 + T₂ * I)
      = 2 * I * ((halfContour (logDeriv completedRiemannZeta) T₁ T₂).im : ℂ) := by
  have hre1 : (-1 + T₁ * I).re = -1 := by simp
  have him1 : (-1 + T₁ * I).im = T₁ := by simp
  have hre2 : (2 + T₂ * I : ℂ).re = 2 := by simp
  have him2 : (2 + T₂ * I : ℂ).im = T₂ := by simp
  simp only [RectangleIntegral, HIntegral, VIntegral, hre1, him1, hre2, him2, smul_eq_mul,
    Complex.ofReal_neg, Complex.ofReal_one, Complex.ofReal_ofNat]
  rw [horizontal_fold h1 hg1, horizontal_fold (by linarith) hg2, vertical_fold h1 h12.le]
  simp only [halfContour, Complex.add_im, Complex.sub_im, Complex.mul_I_im]
  generalize (∫ σ in (1 / 2 : ℝ)..2, logDeriv completedRiemannZeta (σ + T₁ * I)) = A₁
  generalize (∫ σ in (1 / 2 : ℝ)..2, logDeriv completedRiemannZeta (σ + T₂ * I)) = A₂
  generalize (∫ t in T₁..T₂, logDeriv completedRiemannZeta (2 + t * I)) = B
  have e1 : 2 * I * (A₁.im : ℂ) - 2 * I * (A₂.im : ℂ) + I * B - I * -starRingEnd ℂ B
      = 2 * I * (A₁.im : ℂ) - 2 * I * (A₂.im : ℂ) + I * (B + starRingEnd ℂ B) := by ring
  rw [e1, Complex.add_conj]
  push_cast
  ring

end DusartSmoothing.RvM


