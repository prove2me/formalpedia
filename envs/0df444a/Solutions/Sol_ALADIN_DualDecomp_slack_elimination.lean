-- Prove2me | solution 1 for ALADIN.DualDecomp.slack_elimination
-- status  : ACCEPTED   (prove)
-- author  : @arexychen
-- created : 2026-10-13T02:57:07.808873+00:00
-- url     : https://prove2.me/submissions/77abe36a-f591-402c-a255-42d9926f8be0

import Mathlib

open Matrix

theorem solution {m : ℕ} (μ : ℝ) (hμ : 0 < μ) (lam lamQP : Fin m → ℝ) :
    (∀ s : Fin m → ℝ,
      -(1 / (2 * μ)) * ((lamQP - lam) ⬝ᵥ (lamQP - lam)) ≤
        μ / 2 * (s ⬝ᵥ s) - (lamQP - lam) ⬝ᵥ s) ∧
    (∀ s : Fin m → ℝ,
      μ / 2 * (s ⬝ᵥ s) - (lamQP - lam) ⬝ᵥ s =
          -(1 / (2 * μ)) * ((lamQP - lam) ⬝ᵥ (lamQP - lam)) ↔
        s = μ⁻¹ • (lamQP - lam)) := by
  let a := lamQP - lam
  have ident (s : Fin m → ℝ) :
      μ / 2 * (s ⬝ᵥ s) - a ⬝ᵥ s + (1 / (2 * μ)) * (a ⬝ᵥ a) =
        μ / 2 * ((s - μ⁻¹ • a) ⬝ᵥ (s - μ⁻¹ • a)) := by
    simp only [sub_dotProduct, dotProduct_sub, smul_dotProduct, dotProduct_smul,
      smul_eq_mul, dotProduct_comm s a]
    field_simp
    <;> ring
  have nonneg (s : Fin m → ℝ) : 0 ≤ (s - μ⁻¹ • a) ⬝ᵥ (s - μ⁻¹ • a) := by
    exact Finset.sum_nonneg fun i _ => mul_self_nonneg _
  constructor
  · intro s
    have := mul_nonneg (show 0 ≤ μ / 2 by positivity) (nonneg s)
    change -(1 / (2 * μ)) * (a ⬝ᵥ a) ≤ _
    linarith [ident s]
  · intro s
    change μ / 2 * (s ⬝ᵥ s) - a ⬝ᵥ s = -(1 / (2 * μ)) * (a ⬝ᵥ a) ↔ _
    rw [← sub_eq_zero (a := s) (b := μ⁻¹ • a), ← dotProduct_self_eq_zero]
    constructor
    · intro h
      have hz : μ / 2 * ((s - μ⁻¹ • a) ⬝ᵥ (s - μ⁻¹ • a)) = 0 := by
        linarith [ident s]
      exact (mul_eq_zero.mp hz).resolve_left (by positivity)
    · intro h
      have hi := ident s
      rw [h, mul_zero] at hi
      linarith
