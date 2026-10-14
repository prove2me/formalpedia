-- Prove2me | Definitions.Def_dusart_psi_433_20261014_GoodHeights
-- name    : dusart_psi_433_20261014_GoodHeights
-- status  : Definition
-- author  : @abcdefg
-- created : 2026-10-14T09:50:32.912974+00:00
-- url     : https://prove2.me/theorems/0a5b5020-d7b0-40e0-a8a1-ca18a6ca9108
-- title:
--   Dusart smoothing: Good Heights
-- statement:
--   This module gives the complete good heights component of Gaussian resampling for Chebyshev’s psi function. It is part of the direct formal proof of the parameter-dependent explicit prime-number-theorem error estimate. Its supporting analytic and numerical results are included with their proofs.
--
--   Formalization Note: The imported components are complete proof modules; no open theorem is assumed.
-- source:
--   Pierre Dusart, Estimates of Some Functions Over Primes without R.H., https://www.unilim.fr/pages_perso/pierre.dusart/Documents/HDR_Dusart.pdf, Theorem 45 and Lemmas 47–55, printed pp. 38–46; supporting analytic and numerical formalization.

import Definitions.Def_dusart_psi_433_20261014_GoodHeightsRight
import Definitions.Def_dusart_psi_433_20261014_ZetaReflection
noncomputable section
namespace DusartSmoothing
open Complex Real Set Metric Filter Topology

lemma good_heights_full_strip : ∃ C : ℝ, 0 < C ∧ ∀ j : ℕ, 7 ≤ j →
    ∃ R : ℝ, (j : ℝ) ≤ R ∧ R ≤ (j : ℝ) + 1 ∧ RvM.GoodHeight R ∧
      ∀ s : ℂ, (s.im = R ∨ s.im = -R) → -(1 / 2 : ℝ) ≤ s.re → s.re ≤ 2 →
        riemannZeta s ≠ 0 ∧ ‖logDeriv riemannZeta s‖ ≤
          C * ((j : ℝ) + 3)^2 * Real.log ((j : ℝ) + 4) := by
  obtain ⟨C, hC, hright⟩ := good_heights_right
  refine ⟨C + 1, by positivity, fun j hj => ?_⟩
  have hjR : (7 : ℝ) ≤ j := by exact_mod_cast hj
  obtain ⟨R, hR1, hR2, hgood, hb⟩ := hright j hj
  have hRp : 0 < R := by linarith
  let Q : ℝ := ((j : ℝ) + 3)^2 * Real.log ((j : ℝ) + 4)
  have hlog : 1 ≤ Real.log ((j : ℝ) + 4) := by
    rw [Real.le_log_iff_exp_le (by linarith)]
    linarith [Real.exp_one_lt_d9]
  have hQ : R + 10 ≤ Q := by
    have hm := mul_le_mul_of_nonneg_left hlog (sq_nonneg ((j : ℝ) + 3))
    dsimp [Q]
    nlinarith
  have hn : ∀ σ ∈ Set.Icc (-(1 / 2) : ℝ) 2,
      ‖logDeriv riemannZeta (σ + R * I)‖ ≤ (C + 1) * Q := by
    intro σ hσ
    by_cases hσh : 1 / 2 ≤ σ
    · have h := hb σ ⟨hσh, hσ.2⟩
      have h' : ‖logDeriv riemannZeta (σ + R * I)‖ ≤ C * Q := by
        simpa only [Q, mul_assoc] using h
      nlinarith
    · let s : ℂ := σ + R * I
      have hsr : 1 / 2 ≤ 1 - σ ∧ 1 - σ ≤ 2 := by constructor <;> linarith [hσ.1]
      have hconj : 1 - s = starRingEnd ℂ ((1 - σ : ℝ) + R * I) := by
        dsimp [s]; simp only [map_add, map_mul, Complex.conj_ofReal, Complex.conj_I]; push_cast; ring
      have hr : ‖logDeriv riemannZeta (1 - s)‖ ≤ C * Q := by
        rw [hconj, RvM.norm_logDeriv_zeta_conj]
        simpa only [Q, mul_assoc] using hb (1 - σ) hsr
      have hz := zeta_nonzero_of_goodHeight hgood (s := s) (by simpa [s] using hσ.1) (by simp [s])
      have hzr := zeta_nonzero_of_goodHeight (RvM.goodHeight_neg hgood) (s := 1 - s)
        (by norm_num [s]; linarith [hσ.2]) (by simp [s])
      have hsi : s.im ≠ 0 := by simpa [s] using hRp.ne'
      have hG := RvM.norm_logDeriv_GammaR_strip (s := s)
        (by simpa [s] using hσ.1) (by simpa [s] using hσ.2) (by simp [s, abs_of_pos hRp]; linarith)
      have hGr := RvM.norm_logDeriv_GammaR_strip (s := 1 - s)
        (by norm_num [s]; linarith [hσ.2]) (by norm_num [s]; linarith [hσ.1])
        (by simp [s, abs_of_pos hRp]; linarith)
      have hei : s.im = R := by simp [s]
      rw [hei, abs_of_pos hRp] at hG
      rw [Complex.sub_im, Complex.one_im, zero_sub, abs_neg, hei, abs_of_pos hRp] at hGr
      change ‖logDeriv riemannZeta s‖ ≤ _
      rw [RvM.logDeriv_zeta_reflection hsi hz hzr]
      have ht := (norm_sub_le
        (-logDeriv riemannZeta (1 - s) - logDeriv Gammaℝ s) (logDeriv Gammaℝ (1 - s))).trans
        (add_le_add (norm_sub_le _ _) le_rfl)
      rw [norm_neg] at ht
      nlinarith
  refine ⟨R, hR1, hR2, hgood, ?_⟩
  intro s him hlo hhi
  rcases him with him | him
  · refine ⟨zeta_nonzero_of_goodHeight hgood hlo him, ?_⟩
    have he : s = (s.re : ℂ) + R * I := by
      apply Complex.ext <;> simp [him]
    rw [he]
    have h := hn s.re ⟨hlo, hhi⟩
    simpa [Q, mul_assoc] using h
  · refine ⟨zeta_nonzero_of_goodHeight (RvM.goodHeight_neg hgood) hlo him, ?_⟩
    have he : s = starRingEnd ℂ ((s.re : ℂ) + R * I) := by
      apply Complex.ext <;> simp [him]
    rw [he, RvM.norm_logDeriv_zeta_conj]
    have h := hn s.re ⟨hlo, hhi⟩
    simpa [Q, mul_assoc] using h

end DusartSmoothing


