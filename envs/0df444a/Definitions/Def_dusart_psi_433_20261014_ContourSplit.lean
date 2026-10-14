-- Prove2me | Definitions.Def_dusart_psi_433_20261014_ContourSplit
-- name    : dusart_psi_433_20261014_ContourSplit
-- status  : Definition
-- author  : @abcdefg
-- created : 2026-10-14T09:21:21.823148+00:00
-- url     : https://prove2.me/theorems/2ee2c964-ce5b-4e4f-9665-7b6da453c926
-- title:
--   Dusart smoothing: Contour Split
-- statement:
--   This module gives the complete contour split component of Gaussian resampling for Chebyshev’s psi function. It is part of the direct formal proof of the parameter-dependent explicit prime-number-theorem error estimate. Its supporting analytic and numerical results are included with their proofs.
--
--   Formalization Note: The imported components are complete proof modules; no open theorem is assumed.
-- source:
--   Pierre Dusart, Estimates of Some Functions Over Primes without R.H., https://www.unilim.fr/pages_perso/pierre.dusart/Documents/HDR_Dusart.pdf, Theorem 45 and Lemmas 47–55, printed pp. 38–46; supporting analytic and numerical formalization.

import Definitions.Def_dusart_psi_433_20261014_ContourFold
/- Copyright (c) 2026 Anthropic, PBC. Released under Apache 2.0.
Adapted from the accepted half-contour decomposition on Prove2Me. -/
noncomputable section
namespace DusartSmoothing.RvM
open Complex Set MeasureTheory

lemma contour_point_facts {s : ℂ} (hre1 : 1/2 ≤ s.re) (_hre2 : s.re ≤ 2)
    (him : 1 ≤ s.im) (hgood : ∀ ρ, IsNontrivialZero ρ → ρ.im ≠ s.im) :
    s ≠ 0 ∧ s ≠ 1 ∧ riemannZeta s ≠ 0 ∧ 0 < s.re := by
  have hs0 : s ≠ 0 := by
    intro hh
    rw [hh] at him
    simp only [Complex.zero_im] at him
    linarith
  have hs1 : s ≠ 1 := by
    intro hh
    rw [hh] at him
    simp only [Complex.one_im] at him
    linarith
  refine ⟨hs0, hs1, ?_, by linarith⟩
  intro hz
  rcases lt_or_ge s.re 1 with hlt | hge
  · exact hgood s ⟨hz, by linarith, hlt⟩ rfl
  · exact riemannZeta_ne_zero_of_one_le_re hge hz

/-- logDeriv ζ is continuous at good points. -/
lemma continuousAt_logDeriv_zeta {s : ℂ} (hs1 : s ≠ 1) (hζ : riemannZeta s ≠ 0) :
    ContinuousAt (logDeriv riemannZeta) s := by
  have ha := analyticAt_riemannZeta hs1
  exact (ha.deriv.continuousAt).div ha.continuousAt hζ

lemma continuousAt_logDeriv_Gammaℝ {s : ℂ} (hre : 0 < s.re) :
    ContinuousAt (logDeriv Complex.Gammaℝ) s := by
  have ha := analyticAt_Gammaℝ hre
  exact (ha.deriv.continuousAt).div ha.continuousAt (Gammaℝ_ne_zero_of_re_pos hre)





theorem halfContour_completedZeta_split {T₁ T₂ : ℝ} (h1 : 1 ≤ T₁) (h12 : T₁ < T₂)
    (hg1 : GoodHeight T₁) (hg2 : GoodHeight T₂) :
    halfContour (logDeriv completedRiemannZeta) T₁ T₂ =
      halfContour (logDeriv riemannZeta) T₁ T₂ + halfContour (logDeriv Complex.Gammaℝ) T₁ T₂ := by
  have hmem : ∀ σ : ℝ, σ ∈ Set.uIcc (1/2:ℝ) 2 → 1/2 ≤ σ ∧ σ ≤ 2 := by
    intro σ hσ
    rw [Set.uIcc_of_le (by norm_num : (1/2:ℝ) ≤ 2)] at hσ
    exact ⟨hσ.1, hσ.2⟩
  -- facts at horizontal-segment points
  have hseg : ∀ (T : ℝ), 1 ≤ T → GoodHeight T → ∀ σ ∈ Set.uIcc (1/2:ℝ) 2,
      ((σ:ℂ) + T*I ≠ 0 ∧ (σ:ℂ) + T*I ≠ 1 ∧ riemannZeta ((σ:ℂ) + T*I) ≠ 0
        ∧ 0 < ((σ:ℂ) + T*I).re) := by
    intro T hT hg σ hσ
    obtain ⟨ha, hb'⟩ := hmem σ hσ
    have hre : ((σ:ℂ) + T*I).re = σ := by simp
    have him : ((σ:ℂ) + T*I).im = T := by simp
    refine contour_point_facts ?_ ?_ ?_ ?_
    · rw [hre]; exact ha
    · rw [hre]; exact hb'
    · rw [him]; exact hT
    · rw [him]; exact fun ρ hρ => hg ρ hρ
  -- facts at vertical-segment points (σ = 2)
  have hvert : ∀ t : ℝ, t ∈ Set.uIcc T₁ T₂ →
      ((2:ℂ) + t*I ≠ 0 ∧ (2:ℂ) + t*I ≠ 1 ∧ riemannZeta ((2:ℂ) + t*I) ≠ 0
        ∧ 0 < ((2:ℂ) + t*I).re) := by
    intro t _
    have hre : ((2:ℂ) + t*I).re = 2 := by simp
    refine ⟨?_, ?_, riemannZeta_ne_zero_of_one_le_re (by rw [hre]; norm_num), by rw [hre]; norm_num⟩
    · intro hh
      have := congrArg Complex.re hh
      rw [hre] at this
      simp at this
    · intro hh
      have := congrArg Complex.re hh
      rw [hre] at this
      simp at this
  -- pointwise splitting along the three segments
  have keyb : Set.EqOn (fun σ : ℝ => logDeriv completedRiemannZeta ((σ:ℂ) + T₁*I))
      (fun σ : ℝ => logDeriv riemannZeta ((σ:ℂ) + T₁*I)
        + logDeriv Complex.Gammaℝ ((σ:ℂ) + T₁*I)) (Set.uIcc (1/2:ℝ) 2) := by
    intro σ hσ
    obtain ⟨hs0, hs1, hζ, hre⟩ := hseg T₁ h1 hg1 σ hσ
    simp only
    rw [logDeriv_completedZeta _ hs1 hζ hre]
    ring
  have keyt : Set.EqOn (fun σ : ℝ => logDeriv completedRiemannZeta ((σ:ℂ) + T₂*I))
      (fun σ : ℝ => logDeriv riemannZeta ((σ:ℂ) + T₂*I)
        + logDeriv Complex.Gammaℝ ((σ:ℂ) + T₂*I)) (Set.uIcc (1/2:ℝ) 2) := by
    intro σ hσ
    obtain ⟨hs0, hs1, hζ, hre⟩ := hseg T₂ (by linarith) hg2 σ hσ
    simp only
    rw [logDeriv_completedZeta _ hs1 hζ hre]
    ring
  have keyr : Set.EqOn (fun t : ℝ => logDeriv completedRiemannZeta ((2:ℂ) + t*I))
      (fun t : ℝ => logDeriv riemannZeta ((2:ℂ) + t*I)
        + logDeriv Complex.Gammaℝ ((2:ℂ) + t*I)) (Set.uIcc T₁ T₂) := by
    intro t ht
    obtain ⟨hs0, hs1, hζ, hre⟩ := hvert t ht
    simp only
    rw [logDeriv_completedZeta _ hs1 hζ hre]
    ring
  -- integrability of the ζ and Γℝ pieces on each segment
  have hintb : ∀ (T : ℝ), 1 ≤ T → GoodHeight T →
      IntervalIntegrable (fun σ : ℝ => logDeriv riemannZeta ((σ:ℂ) + T*I))
        MeasureTheory.volume (1/2) 2 := by
    intro T hT hg
    apply ContinuousOn.intervalIntegrable
    intro σ hσ
    obtain ⟨_, hs1, hζ, _⟩ := hseg T hT hg σ hσ
    have hparam : ContinuousAt (fun σ : ℝ => (σ:ℂ) + T*I) σ := by fun_prop
    exact ContinuousAt.continuousWithinAt
      (ContinuousAt.comp (g := logDeriv riemannZeta) (f := fun σ : ℝ => (σ:ℂ) + T*I)
        (continuousAt_logDeriv_zeta hs1 hζ) hparam)
  have hintbΓ : ∀ (T : ℝ), 1 ≤ T → GoodHeight T →
      IntervalIntegrable (fun σ : ℝ => logDeriv Complex.Gammaℝ ((σ:ℂ) + T*I))
        MeasureTheory.volume (1/2) 2 := by
    intro T hT hg
    apply ContinuousOn.intervalIntegrable
    intro σ hσ
    obtain ⟨_, _, _, hre⟩ := hseg T hT hg σ hσ
    have hparam : ContinuousAt (fun σ : ℝ => (σ:ℂ) + T*I) σ := by fun_prop
    exact ContinuousAt.continuousWithinAt
      (ContinuousAt.comp (g := logDeriv Complex.Gammaℝ) (f := fun σ : ℝ => (σ:ℂ) + T*I)
        (continuousAt_logDeriv_Gammaℝ hre) hparam)
  have hintr : IntervalIntegrable (fun t : ℝ => logDeriv riemannZeta ((2:ℂ) + t*I))
      MeasureTheory.volume T₁ T₂ := by
    apply ContinuousOn.intervalIntegrable
    intro t ht
    obtain ⟨_, hs1, hζ, _⟩ := hvert t ht
    have hparam : ContinuousAt (fun t : ℝ => (2:ℂ) + t*I) t := by fun_prop
    exact ContinuousAt.continuousWithinAt
      (ContinuousAt.comp (g := logDeriv riemannZeta) (f := fun t : ℝ => (2:ℂ) + t*I)
        (continuousAt_logDeriv_zeta hs1 hζ) hparam)
  have hintrΓ : IntervalIntegrable (fun t : ℝ => logDeriv Complex.Gammaℝ ((2:ℂ) + t*I))
      MeasureTheory.volume T₁ T₂ := by
    apply ContinuousOn.intervalIntegrable
    intro t ht
    obtain ⟨_, _, _, hre⟩ := hvert t ht
    have hparam : ContinuousAt (fun t : ℝ => (2:ℂ) + t*I) t := by fun_prop
    exact ContinuousAt.continuousWithinAt
      (ContinuousAt.comp (g := logDeriv Complex.Gammaℝ) (f := fun t : ℝ => (2:ℂ) + t*I)
        (continuousAt_logDeriv_Gammaℝ hre) hparam)
  -- assemble
  unfold halfContour
  rw [intervalIntegral.integral_congr keyb, intervalIntegral.integral_congr keyt,
    intervalIntegral.integral_congr keyr,
    intervalIntegral.integral_add (hintb T₁ h1 hg1) (hintbΓ T₁ h1 hg1),
    intervalIntegral.integral_add (hintb T₂ (by linarith) hg2) (hintbΓ T₂ (by linarith) hg2),
    intervalIntegral.integral_add hintr hintrΓ]
  ring

end DusartSmoothing.RvM


