-- Prove2me | solution 1 for AppliedSDE.SarkkaSolin.ar1_batch_kalman_core
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-14T10:14:12.224208+00:00
-- url     : https://prove2.me/submissions/cae74063-1930-4597-80ee-93e0288dd839

import Mathlib
import Theorems.Thm_AppliedSDE_SarkkaSolin_ar1_batch_mean_variance_joint_induction
set_option autoImplicit false
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true
open Matrix
open scoped Matrix

/-- The arbitrary-size GP/Kalman mean equality follows from the joint
mean-and-posterior-variance Schur-complement induction invariant. -/
theorem solution
    (n : ℕ) (a V r : ℝ)
    (ha : 0 < a) (ha1 : a < 1) (hV : 0 < V) (hr : 0 < r)
    (y m P : Fin (n + 1) → ℝ) :
    let K : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ :=
      Matrix.of fun i j => V * a ^ Nat.dist i.val j.val
    (P 0 = V * r / (V + r)) →
    (m 0 = V / (V + r) * y 0) →
    (∀ j : Fin n,
      let predicted : ℝ := a ^ 2 * P j.castSucc + V * (1 - a ^ 2)
      P j.succ = predicted * r / (predicted + r) ∧
      m j.succ = a * m j.castSucc +
        predicted / (predicted + r) *
          (y j.succ - a * m j.castSucc)) →
    m (Fin.last n) =
      (K.mulVec ((K + r • (1 : Matrix (Fin (n + 1))
        (Fin (n + 1)) ℝ))⁻¹ |>.mulVec y)) (Fin.last n) := by
  intro K hp hm hstep
  have h :=
    AppliedSDE.SarkkaSolin.ar1_batch_mean_variance_joint_induction
      n a V r ha ha1 hV hr y m P hp hm hstep
  exact h.1
