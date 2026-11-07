-- Prove2me | solution 1 for AaronsonAmbainis.Bridge.sqrt_form_iff
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T23:12:22.545894+00:00
-- url     : https://prove2.me/submissions/af4687a5-df9c-45a7-a02d-673b5e92e493

import Definitions.Def_AaronsonAmbainis_Bridge_Poly
import Definitions.Def_AaronsonAmbainis_Bridge_Affine
import Definitions.Def_AaronsonAmbainis_Bridge_PrintedAA

set_option autoImplicit true
open AaronsonAmbainis AaronsonAmbainis.Bridge
open Finset MvPolynomial
namespace AaronsonAmbainis.Bridge
theorem _root_.solution {c₁ c₂ k m ε D I : ℝ} (hc₁ : 0 ≤ c₁) (hc₂ : 0 < c₂) (hm : 0 < m)
    (hkm : 15 * c₁ ^ 2 * m = k * c₂ ^ 2) (hε : 0 ≤ ε) (hD : 0 < D) (hI : 0 ≤ I) :
    c₁ * Real.sqrt 15 / (c₂ * Real.pi ^ 4) * (ε ^ 2 * Real.sqrt ε) / D ^ 6 ≤ I
      ↔ k * ε ^ 5 ≤ m * Real.pi ^ 8 * D ^ 12 * I ^ 2 := by
  have hpi : 0 < Real.pi := Real.pi_pos
  have hden : 0 < c₂ * Real.pi ^ 4 * D ^ 6 := by positivity
  have hL : 0 ≤ c₁ * Real.sqrt 15 * (ε ^ 2 * Real.sqrt ε) := by positivity
  have e : c₁ * Real.sqrt 15 / (c₂ * Real.pi ^ 4) * (ε ^ 2 * Real.sqrt ε) / D ^ 6
      = c₁ * Real.sqrt 15 * (ε ^ 2 * Real.sqrt ε) / (c₂ * Real.pi ^ 4 * D ^ 6) := by
    field_simp
  have e1 : (c₁ * Real.sqrt 15 * (ε ^ 2 * Real.sqrt ε)) ^ 2 = 15 * c₁ ^ 2 * ε ^ 5 := by
    rw [mul_pow, mul_pow, mul_pow, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 15), Real.sq_sqrt hε]
    ring
  have e2 : (I * (c₂ * Real.pi ^ 4 * D ^ 6)) ^ 2
      = c₂ ^ 2 * (Real.pi ^ 8 * D ^ 12 * I ^ 2) := by ring
  have e3 : m * (15 * c₁ ^ 2 * ε ^ 5) = c₂ ^ 2 * (k * ε ^ 5) := by
    linear_combination ε ^ 5 * hkm
  have e4 : m * (c₂ ^ 2 * (Real.pi ^ 8 * D ^ 12 * I ^ 2))
      = c₂ ^ 2 * (m * Real.pi ^ 8 * D ^ 12 * I ^ 2) := by ring
  rw [e, div_le_iff₀ hden]
  constructor
  · intro h
    have h2 := pow_le_pow_left₀ hL h 2
    rw [e1, e2] at h2
    have h3 := mul_le_mul_of_nonneg_left h2 hm.le
    rw [e3, e4] at h3
    exact le_of_mul_le_mul_left h3 (pow_pos hc₂ 2)
  · intro h
    apply le_of_pow_le_pow_left₀ two_ne_zero (mul_nonneg hI hden.le)
    rw [e1, e2]
    have h3 := mul_le_mul_of_nonneg_left h (sq_nonneg c₂)
    rw [← e3, ← e4] at h3
    exact le_of_mul_le_mul_left h3 hm
end AaronsonAmbainis.Bridge
