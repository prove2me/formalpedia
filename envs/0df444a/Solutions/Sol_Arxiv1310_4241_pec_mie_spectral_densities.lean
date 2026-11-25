-- Prove2me | solution 1 for Arxiv1310_4241.pec_mie_spectral_densities
-- status  : ACCEPTED   (prove)
-- author  : @fl-39
-- created : 2026-11-25T19:20:32.318727+00:00
-- url     : https://prove2.me/submissions/0af44f43-bc2d-4f8a-b7fe-fab9f6ff3c23

import Mathlib
import Definitions.Def_Arxiv1310_4241_Basic

open MeasureTheory Filter Topology Arxiv1310_4241

theorem solution (ω : ℝ) (ε μ k : ℂ) (hkdef : k = wavenumber ω ε μ)
    (hk : IsCausalWavenumber k) (ξ η : ℝ) (hξη : (ξ, η) ≠ (0, 0))
    (hβ : sommerfeldRoot k ξ η ≠ 0) (Ex Ey σ τ : ℂ) :
    (ghat k ξ η 0 * (-(Complex.I * ξ * sommerfeldRoot k ξ η * σ) - ω * μ * η * τ) = -Ex ∧
      ghat k ξ η 0 * (-(Complex.I * η * sommerfeldRoot k ξ η * σ) + ω * μ * ξ * τ) = -Ey) ↔
    (σ = -(8 * Real.pi ^ 2 * Complex.I / ((ξ : ℂ) ^ 2 + (η : ℂ) ^ 2)) * (ξ * Ex + η * Ey) ∧
      τ = 8 * Real.pi ^ 2 * sommerfeldRoot k ξ η / (ω * μ * ((ξ : ℂ) ^ 2 + (η : ℂ) ^ 2)) *
        (η * Ex - ξ * Ey)) := by
  have hk0 : k ≠ 0 := by
    intro h
    have := hk.1
    rw [h] at this
    simp at this
  have hω : (ω : ℂ) ≠ 0 := by
    intro h
    apply hk0
    rw [hkdef, wavenumber, h, zero_mul]
  have hμ : μ ≠ 0 := by
    intro h
    apply hk0
    rw [hkdef, wavenumber, h, mul_zero, Complex.zero_cpow (by norm_num), mul_zero]
  have hπ : (Real.pi : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
  have hρ2_real : (0 : ℝ) < ξ ^ 2 + η ^ 2 := by
    by_contra h
    push Not at h
    have hξ : ξ = 0 := by nlinarith [sq_nonneg ξ, sq_nonneg η]
    have hη : η = 0 := by nlinarith [sq_nonneg ξ, sq_nonneg η]
    exact hξη (Prod.ext hξ hη)
  have hρ2 : (ξ : ℂ) ^ 2 + (η : ℂ) ^ 2 ≠ 0 := by
    have : ((ξ ^ 2 + η ^ 2 : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hρ2_real.ne'
    simpa using this
  have hghat : ghat k ξ η 0 = 1 / (8 * (Real.pi : ℂ) ^ 2 * sommerfeldRoot k ξ η) := by
    simp [ghat]
  rw [hghat]
  set β := sommerfeldRoot k ξ η
  have hden : (8 * (Real.pi : ℂ) ^ 2 * β) ≠ 0 :=
    mul_ne_zero (mul_ne_zero (by norm_num) (pow_ne_zero 2 hπ)) hβ
  constructor
  · rintro ⟨h1, h2⟩
    have h1' : -(Complex.I * ξ * β * σ) - ω * μ * η * τ = -(8 * (Real.pi : ℂ) ^ 2 * β * Ex) := by
      calc -(Complex.I * ξ * β * σ) - ω * μ * η * τ
          = (8 * (Real.pi : ℂ) ^ 2 * β) * (1 / (8 * (Real.pi : ℂ) ^ 2 * β) *
              (-(Complex.I * ξ * β * σ) - ω * μ * η * τ)) := by field_simp [hden]
        _ = (8 * (Real.pi : ℂ) ^ 2 * β) * (-Ex) := by rw [h1]
        _ = -(8 * (Real.pi : ℂ) ^ 2 * β * Ex) := by ring
    have h2' : -(Complex.I * η * β * σ) + ω * μ * ξ * τ = -(8 * (Real.pi : ℂ) ^ 2 * β * Ey) := by
      calc -(Complex.I * η * β * σ) + ω * μ * ξ * τ
          = (8 * (Real.pi : ℂ) ^ 2 * β) * (1 / (8 * (Real.pi : ℂ) ^ 2 * β) *
              (-(Complex.I * η * β * σ) + ω * μ * ξ * τ)) := by field_simp [hden]
        _ = (8 * (Real.pi : ℂ) ^ 2 * β) * (-Ey) := by rw [h2]
        _ = -(8 * (Real.pi : ℂ) ^ 2 * β * Ey) := by ring
    constructor
    · have hcomb : -Complex.I * β * ((ξ : ℂ) ^ 2 + (η : ℂ) ^ 2) * σ =
          -(8 * (Real.pi : ℂ) ^ 2 * β * (ξ * Ex + η * Ey)) := by
        linear_combination (ξ : ℂ) * h1' + (η : ℂ) * h2'
      have hσmul : ((ξ : ℂ) ^ 2 + (η : ℂ) ^ 2) * σ =
          -(8 * (Real.pi : ℂ) ^ 2 * Complex.I) * (ξ * Ex + η * Ey) := by
        apply mul_left_cancel₀ hβ
        calc β * (((ξ : ℂ) ^ 2 + (η : ℂ) ^ 2) * σ)
            = Complex.I * (-Complex.I * β * ((ξ : ℂ) ^ 2 + (η : ℂ) ^ 2) * σ) := by
                ring_nf; simp [Complex.I_sq]
          _ = Complex.I * -(8 * (Real.pi : ℂ) ^ 2 * β * (ξ * Ex + η * Ey)) := by rw [hcomb]
          _ = β * (-(8 * (Real.pi : ℂ) ^ 2 * Complex.I) * (ξ * Ex + η * Ey)) := by ring
      field_simp [hρ2]
      linear_combination hσmul
    · have hcomb : (ω : ℂ) * μ * ((ξ : ℂ) ^ 2 + (η : ℂ) ^ 2) * τ =
          8 * (Real.pi : ℂ) ^ 2 * β * (η * Ex - ξ * Ey) := by
        linear_combination -(η : ℂ) * h1' + (ξ : ℂ) * h2'
      field_simp [hω, hμ, hρ2]
      linear_combination hcomb
  · rintro ⟨rfl, rfl⟩
    constructor
    · field_simp [hπ, hβ, hω, hμ, hρ2]
      ring_nf; simp [Complex.I_sq]
    · field_simp [hπ, hβ, hω, hμ, hρ2]
      ring_nf; simp [Complex.I_sq]
