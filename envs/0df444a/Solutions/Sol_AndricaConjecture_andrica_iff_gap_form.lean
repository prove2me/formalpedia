-- Prove2me | solution 1 for AndricaConjecture.andrica_iff_gap_form
-- status  : ACCEPTED   (prove)
-- author  : @jakevej
-- created : 2026-11-27T03:17:36.73272+00:00
-- url     : https://prove2.me/submissions/b6fd19fe-d36f-43e6-b81d-9bab5263421b

import Mathlib

open Real in
theorem solution (n : Nat) :
    Real.sqrt (Nat.nth Nat.Prime (n + 1) : Real) -
        Real.sqrt (Nat.nth Nat.Prime n : Real) < 1 ↔
      (Nat.nth Nat.Prime (n + 1) - Nat.nth Nat.Prime n : Real) <
        2 * Real.sqrt (Nat.nth Nat.Prime n : Real) + 1 := by
  have ha0 : (0 : Real) ≤ (Nat.nth Nat.Prime n : Real) := Nat.cast_nonneg _
  have hb0 : (0 : Real) ≤ (Nat.nth Nat.Prime (n + 1) : Real) := Nat.cast_nonneg _
  have hsq : (Real.sqrt (Nat.nth Nat.Prime n : Real) + 1) ^ 2
      = (Nat.nth Nat.Prime n : Real) + 2 * Real.sqrt (Nat.nth Nat.Prime n : Real) + 1 := by
    rw [add_sq, Real.sq_sqrt ha0]
    ring
  constructor
  · intro h
    have h1 : Real.sqrt (Nat.nth Nat.Prime (n + 1) : Real)
        < Real.sqrt (Nat.nth Nat.Prime n : Real) + 1 := by
      have hs := Real.sqrt_nonneg (Nat.nth Nat.Prime n : Real)
      linarith
    have h2 : (Real.sqrt (Nat.nth Nat.Prime (n + 1) : Real)) ^ 2
        < (Real.sqrt (Nat.nth Nat.Prime n : Real) + 1) ^ 2 :=
      (sq_lt_sq₀ (Real.sqrt_nonneg _) (by positivity)).mpr h1
    rw [Real.sq_sqrt hb0, hsq] at h2
    linarith
  · intro h
    have h2 : (Real.sqrt (Nat.nth Nat.Prime (n + 1) : Real)) ^ 2
        < (Real.sqrt (Nat.nth Nat.Prime n : Real) + 1) ^ 2 := by
      rw [Real.sq_sqrt hb0, hsq]
      linarith
    have h1 : Real.sqrt (Nat.nth Nat.Prime (n + 1) : Real)
        < Real.sqrt (Nat.nth Nat.Prime n : Real) + 1 :=
      (sq_lt_sq₀ (Real.sqrt_nonneg _) (by positivity)).mp h2
    have hs := Real.sqrt_nonneg (Nat.nth Nat.Prime n : Real)
    linarith
