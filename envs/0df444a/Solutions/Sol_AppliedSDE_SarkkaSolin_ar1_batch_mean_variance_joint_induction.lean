-- Prove2me | solution 1 for AppliedSDE.SarkkaSolin.ar1_batch_mean_variance_joint_induction
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-14T11:26:01.82686+00:00
-- url     : https://prove2.me/submissions/dc177865-ab57-4ab3-8737-db00ed296ba2

import Mathlib
import Theorems.Thm_AppliedSDE_SarkkaSolin_ar1_batch_final_mean_from_kalman
import Theorems.Thm_AppliedSDE_SarkkaSolin_ar1_batch_final_variance_from_kalman
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open Matrix
open scoped Matrix
set_option autoImplicit false
theorem solution
    (n : ℕ) (a V r : ℝ)
    (ha : 0 < a) (ha1 : a < 1) (hV : 0 < V) (hr : 0 < r)
    (y m P : Fin (n + 1) → ℝ) :
    let K : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ :=
      Matrix.of fun i j => V * a ^ Nat.dist i.val j.val
    let C : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ :=
      K + r • (1 : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ)
    let k : Fin (n + 1) → ℝ := fun j => K (Fin.last n) j
    (P 0 = V * r / (V + r)) →
    (m 0 = V / (V + r) * y 0) →
    (∀ j : Fin n,
      let predicted : ℝ := a ^ 2 * P j.castSucc + V * (1 - a ^ 2)
      P j.succ = predicted * r / (predicted + r) ∧
      m j.succ = a * m j.castSucc +
        predicted / (predicted + r) *
          (y j.succ - a * m j.castSucc)) →
    (m (Fin.last n) =
      (K.mulVec (C⁻¹ |>.mulVec y)) (Fin.last n)) ∧
    (P (Fin.last n) = V - (k ⬝ᵥ (C⁻¹ |>.mulVec k))) := by
  intro K C k hP0 hm0 hRec
  constructor
  · exact AppliedSDE.SarkkaSolin.ar1_batch_final_mean_from_kalman
      n a V r ha ha1 hV hr y m P hP0 hm0 hRec
  · exact AppliedSDE.SarkkaSolin.ar1_batch_final_variance_from_kalman
      n a V r ha ha1 hV hr y m P hP0 hm0 hRec
