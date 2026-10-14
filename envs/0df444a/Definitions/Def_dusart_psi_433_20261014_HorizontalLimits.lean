-- Prove2me | Definitions.Def_dusart_psi_433_20261014_HorizontalLimits
-- name    : dusart_psi_433_20261014_HorizontalLimits
-- status  : Definition
-- author  : @abcdefg
-- created : 2026-10-14T09:55:43.847613+00:00
-- url     : https://prove2.me/theorems/9ce52bce-8c6b-4951-a06b-5a80c8843c8e
-- title:
--   Dusart smoothing: Horizontal Limits
-- statement:
--   This module gives the complete horizontal limits component of Gaussian resampling for Chebyshev’s psi function. It is part of the direct formal proof of the parameter-dependent explicit prime-number-theorem error estimate. Its supporting analytic and numerical results are included with their proofs.
--
--   Formalization Note: The imported components are complete proof modules; no open theorem is assumed.
-- source:
--   Pierre Dusart, Estimates of Some Functions Over Primes without R.H., https://www.unilim.fr/pages_perso/pierre.dusart/Documents/HDR_Dusart.pdf, Theorem 45 and Lemmas 47–55, printed pp. 38–46; supporting analytic and numerical formalization.

import Definitions.Def_dusart_psi_433_20261014_HorizontalBounds
noncomputable section
namespace DusartSmoothing
open Complex Real Set Filter Topology MeasureTheory

lemma exists_perron_good_heights (x : ℝ) (hx : 1 ≤ x) :
    ∃ R : ℕ → ℝ, Tendsto R atTop atTop ∧ (∀ j, 4 < R j ∧ RvM.GoodHeight (R j)) ∧
      Tendsto (fun j => ∫ σ in (-(1 / 2) : ℝ)..2,
        perronIntegrand x (σ + (-R j) * I)) atTop (𝓝 0) ∧
      Tendsto (fun j => ∫ σ in (-(1 / 2) : ℝ)..2,
        perronIntegrand x (σ + R j * I)) atTop (𝓝 0) := by
  classical
  obtain ⟨C, hC, hh⟩ := good_heights_full_strip
  choose R hR1 hR2 hgood hbound using fun j : ℕ => hh (j + 7) (by omega)
  simp only [Nat.cast_add, Nat.cast_ofNat] at hR1 hR2 hbound
  have hRt : Tendsto R atTop atTop := tendsto_atTop_mono hR1
    (tendsto_atTop_add_const_right atTop 7 tendsto_natCast_atTop_atTop)
  have hRp : ∀ j, 0 < R j := by
    intro j
    have hn : (0 : ℝ) ≤ j := Nat.cast_nonneg j
    linarith [hR1 j]
  have hmax : Tendsto (fun j : ℕ =>
      20 * C * x^4 * Real.log ((j : ℝ) + 11) / ((j : ℝ) + 11)) atTop (𝓝 0) := by
    simpa only [mul_div_assoc, mul_zero] using log_div_height_tendsto.const_mul (20 * C * x^4)
  have hlim : ∀ ε ∈ ({(-1 : ℝ), 1} : Set ℝ),
      Tendsto (fun j => ∫ σ in (-(1 / 2) : ℝ)..2,
        perronIntegrand x (σ + (ε * R j : ℝ) * I)) atTop (𝓝 0) := by
    intro ε hε
    have hεabs : |ε| = 1 := by rcases hε with h | h <;> simp_all
    apply tendsto_zero_iff_norm_tendsto_zero.mpr
    apply squeeze_zero (fun j => norm_nonneg _) (fun j => ?_) hmax
    have hb : ∀ σ ∈ Set.Icc (-(1 / 2) : ℝ) 2,
        ‖logDeriv riemannZeta (σ + (ε * R j : ℝ) * I)‖ ≤
          C * ((j : ℝ) + 7 + 3)^2 * Real.log ((j : ℝ) + 7 + 4) := by
      intro σ hσ
      apply (hbound j (σ + (ε * R j : ℝ) * I) ?_ (by simpa using hσ.1) (by simpa using hσ.2)).2
      rcases hε with h | h <;> simp_all
    have he : |ε * R j| = R j := by rw [abs_mul, hεabs, abs_of_pos (hRp j), one_mul]
    have h := norm_perron_horizontal_integral x hx C ((j : ℝ) + 7) (R j) hC
      (by have hn := Nat.cast_nonneg (α := ℝ) j; linarith) (hR1 j) (ε * R j) he hb
    simpa only [show (j : ℝ) + 7 + 4 = (j : ℝ) + 11 by ring] using h
  refine ⟨R, hRt, ?_, ?_, ?_⟩
  · intro j
    refine ⟨?_, hgood j⟩
    have hn : (0 : ℝ) ≤ j := Nat.cast_nonneg j
    linarith [hR1 j]
  · simpa only [neg_one_mul, Complex.ofReal_neg] using hlim (-1) (by simp)
  · simpa only [one_mul] using hlim 1 (by simp)

end DusartSmoothing


