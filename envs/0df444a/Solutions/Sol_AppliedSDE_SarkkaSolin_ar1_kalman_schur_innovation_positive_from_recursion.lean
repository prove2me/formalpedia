-- Prove2me | solution 1 for AppliedSDE.SarkkaSolin.ar1_kalman_schur_innovation_positive_from_recursion
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-14T16:52:41.355411+00:00
-- url     : https://prove2.me/submissions/dbe0c820-0062-46b2-9505-29cb4aefad51

import Mathlib
import Theorems.Thm_AppliedSDE_SarkkaSolin_ar1_kalman_finite_recursion_variance_nonnegative
import Theorems.Thm_AppliedSDE_SarkkaSolin_ar1_schur_innovation_denominator
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open Matrix
open scoped Matrix
set_option autoImplicit false
theorem solution
    (n : ℕ) (a V r : ℝ)
    (ha : 0 < a) (ha1 : a < 1) (hV : 0 < V) (hr : 0 < r)
    (P : Fin (n + 1) -> ℝ)
    (hP0 : P 0 = V * r / (V + r))
    (hstep : ∀ j : Fin n,
      P j.succ =
        (a ^ 2 * P j.castSucc + V * (1 - a ^ 2)) * r /
          (a ^ 2 * P j.castSucc + V * (1 - a ^ 2) + r))
    (A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ)
    (k : Fin (n + 1) -> ℝ)
    (hPident : P (Fin.last n) = V - (k ⬝ᵥ A.mulVec k)) :
    0 < (V + r) - ((a • k) ⬝ᵥ A.mulVec (a • k)) := by
  have hnonneg :=
    AppliedSDE.SarkkaSolin.ar1_kalman_finite_recursion_variance_nonnegative
      n a V r ha ha1 hV hr P hP0 hstep (Fin.last n)
  exact (AppliedSDE.SarkkaSolin.ar1_schur_innovation_denominator
    (n + 1) A k a V r (P (Fin.last n))
    ha ha1 hV hr hnonneg hPident).2
