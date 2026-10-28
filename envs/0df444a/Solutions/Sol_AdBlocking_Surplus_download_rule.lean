-- Prove2me | solution 1 for AdBlocking.Surplus.download_rule
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-26T01:28:22.717017+00:00
-- url     : https://prove2.me/submissions/cd73e8a8-d075-46c6-9fdd-17a072c1d8a5

import Mathlib
import Definitions.Def_AdBlocking_Surplus_Model

open AdBlocking.Surplus in
theorem solution :
    ∀ r q V θ γ κ : ℝ, 0 < r → 0 < q → 0 ≤ V → V < q / (1 + r) →
      (downloads q (q / (1 + r)) V θ γ κ ↔
        (1 + r) * κ / (q - V * (1 + r)) < γ ∧ κ / q + γ * V / q < θ) := by
  intro r q V θ γ κ hr hq hV hVq
  have h1r : 0 < 1 + r := by linarith
  have hD : 0 < q - V * (1 + r) := by
    rw [lt_div_iff₀ h1r] at hVq; linarith
  have hA : q / (1 + r) * (1 + r) = q := by field_simp
  have e2 : κ / q + γ * V / q = (κ + γ * V) / q := by ring
  rw [e2, div_lt_iff₀ hD, div_lt_iff₀ hq]
  unfold downloads
  rw [max_lt_iff]
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨?_, by linarith⟩
    have : κ < γ * (q / (1 + r) - V) := by linarith
    have h3 := mul_lt_mul_of_pos_right this h1r
    have : γ * (q / (1 + r) - V) * (1 + r) = γ * (q - V * (1 + r)) := by
      rw [mul_assoc, sub_mul, hA]
    nlinarith
  · rintro ⟨h1, h2⟩
    refine ⟨?_, by linarith⟩
    have : γ * (q / (1 + r) - V) * (1 + r) = γ * (q - V * (1 + r)) := by
      rw [mul_assoc, sub_mul, hA]
    have h4 : κ * (1 + r) < γ * (q / (1 + r) - V) * (1 + r) := by linarith
    have h5 := lt_of_mul_lt_mul_right h4 h1r.le
    linarith
