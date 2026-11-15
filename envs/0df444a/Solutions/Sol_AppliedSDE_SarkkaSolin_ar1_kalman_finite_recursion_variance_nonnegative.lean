-- Prove2me | solution 1 for AppliedSDE.SarkkaSolin.ar1_kalman_finite_recursion_variance_nonnegative
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-14T16:50:19.786047+00:00
-- url     : https://prove2.me/submissions/98539376-8bcc-4c60-bb27-ba8cf936f86c

import Mathlib
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

set_option autoImplicit false
theorem solution
    (n : ℕ) (a V r : ℝ)
    (ha : 0 < a) (ha1 : a < 1) (hV : 0 < V) (hr : 0 < r)
    (P : Fin (n + 1) -> ℝ)
    (hP0 : P 0 = V * r / (V + r))
    (hstep : ∀ j : Fin n,
      P j.succ =
        (a ^ 2 * P j.castSucc + V * (1 - a ^ 2)) * r /
          (a ^ 2 * P j.castSucc + V * (1 - a ^ 2) + r)) :
    ∀ j : Fin (n + 1), 0 ≤ P j := by
  have ha2 : 0 <= 1 - a ^ 2 := by
    nlinarith [mul_nonneg (sub_nonneg.mpr ha1.le)
      (add_nonneg ha.le (zero_le_one : (0 : ℝ) <= 1))]
  intro j
  induction j using Fin.induction with
  | zero =>
      rw [hP0]
      positivity
  | succ i hi =>
      rw [hstep i]
      have hp : 0 <= a ^ 2 * P i.castSucc + V * (1 - a ^ 2) :=
        add_nonneg (mul_nonneg (sq_nonneg a) hi)
          (mul_nonneg hV.le ha2)
      exact div_nonneg (mul_nonneg hp hr.le) (add_nonneg hp hr.le)
