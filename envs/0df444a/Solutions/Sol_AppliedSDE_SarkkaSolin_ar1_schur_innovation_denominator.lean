-- Prove2me | solution 1 for AppliedSDE.SarkkaSolin.ar1_schur_innovation_denominator
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-14T09:37:20.079006+00:00
-- url     : https://prove2.me/submissions/fb023d15-38c9-4b29-9064-187688bacfcf

import Mathlib
import Theorems.Thm_AppliedSDE_SarkkaSolin_ar1_schur_predicted_variance
set_option autoImplicit false
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true
open Matrix
open scoped Matrix

/-- Schur complement of an appended noisy AR(1) observation is the strictly
positive scalar Kalman innovation variance. -/
theorem solution
    (n : ℕ) (A : Matrix (Fin n) (Fin n) ℝ)
    (k : Fin n → ℝ) (a V r P : ℝ)
    (ha : 0 < a) (ha1 : a < 1) (hV : 0 < V)
    (hr : 0 < r) (hP : 0 ≤ P)
    (hPident : P = V - (k ⬝ᵥ A.mulVec k)) :
    ((V + r) - ((a • k) ⬝ᵥ A.mulVec (a • k)) =
      (a ^ 2 * P + V * (1 - a ^ 2)) + r) ∧
    0 < (V + r) - ((a • k) ⬝ᵥ A.mulVec (a • k)) := by
  have ha2 : a ^ 2 < 1 := by nlinarith
  have hnoise : 0 < V * (1 - a ^ 2) := by
    apply mul_pos hV
    linarith
  have hq : 0 ≤ a ^ 2 * P :=
    mul_nonneg (sq_nonneg _) hP
  have hp :
      0 < (a ^ 2 * P + V * (1 - a ^ 2)) + r := by
    linarith
  have hpred :=
    AppliedSDE.SarkkaSolin.ar1_schur_predicted_variance
      n A k a V P hPident
  constructor
  · linarith
  · linarith
