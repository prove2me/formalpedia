-- Prove2me | solution 1 for Arxiv2608_05214.surface_decomposition_angle
-- status  : ACCEPTED   (prove)
-- author  : @garyholm
-- created : 2026-11-26T00:00:02.813751+00:00
-- url     : https://prove2.me/submissions/58cc0670-3f19-4c9d-a0db-7cd0e5195bb5

import Mathlib
import Definitions.Def_Arxiv2608_05214_Basic

set_option autoImplicit false

open MeasureTheory

open Arxiv2608_05214 in
theorem solution (c₀ ρ₀ omega k₁ k₂ : ℝ) (hc₀ : 0 < c₀) (hρ₀ : 0 < ρ₀)
    (homega : omega ≠ 0) (hprop : k₁ ^ 2 + k₂ ^ 2 < omega ^ 2 / c₀ ^ 2) :
    let k := verticalWavenumber omega c₀ k₁ k₂
    let cosθ := k / ((omega : ℂ) / c₀)
    (0 < omega → cosθ = ((Real.sqrt (1 - c₀ ^ 2 * (k₁ ^ 2 + k₂ ^ 2) / omega ^ 2) : ℝ) : ℂ)) ∧
    (omega * ρ₀ : ℂ) / k = ρ₀ * c₀ / cosθ ∧
    (∀ P V : ℂ, downgoingP omega ρ₀ k P V = P / 2 + ρ₀ * c₀ / (2 * cosθ) * V ∧
      upgoingP omega ρ₀ k P V = P / 2 - ρ₀ * c₀ / (2 * cosθ) * V) ∧
    (0 < omega → k₁ = 0 → k₂ = 0 → (omega * ρ₀ : ℂ) / k = ρ₀ * c₀) := by
  intro k cosθ
  set x : ℝ := omega ^ 2 / c₀ ^ 2 - (k₁ ^ 2 + k₂ ^ 2) with hx
  have hx0 : 0 < x := by rw [hx]; linarith
  have hk : k = ((Real.sqrt x : ℝ) : ℂ) := by
    show verticalWavenumber omega c₀ k₁ k₂ = _
    unfold verticalWavenumber
    rw [Real.sqrt_eq_rpow, Complex.ofReal_cpow hx0.le]
    rw [hx]; push_cast; rfl
  have hs : 0 < Real.sqrt x := Real.sqrt_pos.2 hx0
  have hk0 : k ≠ 0 := by rw [hk]; exact_mod_cast hs.ne'
  have hc0 : (c₀ : ℂ) ≠ 0 := by exact_mod_cast hc₀.ne'
  have hw0 : (omega : ℂ) ≠ 0 := by exact_mod_cast homega
  have hcos : cosθ = k * c₀ / omega := by
    show k / ((omega : ℂ) / c₀) = _
    field_simp
  have key : (omega * ρ₀ : ℂ) / k = ρ₀ * c₀ / cosθ := by
    rw [hcos]; field_simp
  refine ⟨fun hw => ?_, key, fun P V => ⟨?_, ?_⟩, fun hw h1 h2 => ?_⟩
  · rw [hcos, hk]
    have e : Real.sqrt x * c₀ / omega = Real.sqrt (1 - c₀ ^ 2 * (k₁ ^ 2 + k₂ ^ 2) / omega ^ 2) := by
      have : 1 - c₀ ^ 2 * (k₁ ^ 2 + k₂ ^ 2) / omega ^ 2 = x * (c₀ / omega) ^ 2 := by
        rw [hx]; field_simp
      rw [this, Real.sqrt_mul hx0.le, Real.sqrt_sq (by positivity)]
      ring
    rw [← e]; push_cast; ring
  · unfold downgoingP
    rw [show ρ₀ * c₀ / (2 * cosθ) = (omega * ρ₀ : ℂ) / k / 2 by rw [key]; ring]
    ring
  · unfold upgoingP
    rw [show ρ₀ * c₀ / (2 * cosθ) = (omega * ρ₀ : ℂ) / k / 2 by rw [key]; ring]
    ring
  · have e : Real.sqrt x = omega / c₀ := by
      rw [hx, h1, h2]
      simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, add_zero, sub_zero]
      rw [show omega ^ 2 / c₀ ^ 2 = (omega / c₀) ^ 2 by ring, Real.sqrt_sq (by positivity)]
    rw [hk, e]
    push_cast
    field_simp
