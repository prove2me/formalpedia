-- Prove2me | solution 1 for AffinePolicies.SqrtBound.mu_pos
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-05T22:46:51.283076+00:00
-- url     : https://prove2.me/submissions/35a256d4-42cf-4ec5-9a3f-d53c05d034a3

import Mathlib
import Definitions.Def_AffinePolicies_SqrtBound_Setting

open Matrix

open AffinePolicies.SqrtBound in
theorem solution {m : ℕ} (U : Set (Fin m → ℝ)) (hUnn : ∀ b ∈ U, 0 ≤ b)
    (hUfull : (interior U).Nonempty)
    (μ : Fin m → ℝ) (hμ : ∀ j, IsGreatest ((fun b : Fin m → ℝ => b j) '' U) (μ j)) :
    ∀ j, 0 < μ j := by
  intro j
  obtain ⟨x, hx⟩ := hUfull
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp isOpen_interior x hx
  set y : Fin m → ℝ := x + (ε / 2) • Pi.single j (1 : ℝ) with hy
  have hyU : y ∈ U := by
    apply interior_subset
    apply hball
    rw [Metric.mem_ball, dist_eq_norm, hy, add_sub_cancel_left, norm_smul,
      Pi.norm_single, norm_one, mul_one, Real.norm_eq_abs, abs_of_pos (by positivity)]
    linarith
  have hxU : x ∈ U := interior_subset hx
  have h1 : y j ≤ μ j := (hμ j).2 ⟨y, hyU, rfl⟩
  have h2 : 0 ≤ x j := hUnn x hxU j
  have h3 : y j = x j + ε / 2 := by simp [hy]
  linarith
