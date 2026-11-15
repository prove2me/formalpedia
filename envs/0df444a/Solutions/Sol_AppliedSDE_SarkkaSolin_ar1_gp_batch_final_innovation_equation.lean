-- Prove2me | solution 1 for AppliedSDE.SarkkaSolin.ar1_gp_batch_final_innovation_equation
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-14T08:12:53.98331+00:00
-- url     : https://prove2.me/submissions/0e9a32da-ce62-436f-b74b-70e8317a7c13

import Mathlib
import Theorems.Thm_AppliedSDE_SarkkaSolin_ar1_general_noisy_covariance_posdef
import Theorems.Thm_AppliedSDE_SarkkaSolin_ar1_batch_posterior_innovation
set_option autoImplicit false
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true
open Matrix

theorem solution
    (n : ℕ) (a V r : ℝ)
    (ha : 0 < a) (ha1 : a < 1) (hV : 0 < V) (hr : 0 < r)
    (y : Fin (n + 2) → ℝ) :
    let K : Matrix (Fin (n + 2)) (Fin (n + 2)) ℝ :=
      Matrix.of fun i j => V * a ^ Nat.dist i.val j.val
    let z := (K + r • (1 : Matrix (Fin (n + 2)) (Fin (n + 2)) ℝ))⁻¹ |>.mulVec y
    let m := K.mulVec z
    (r + V * (1 - a ^ 2)) * m (Fin.last (n + 1)) =
      a * r * m ((Fin.last n).castSucc) +
        V * (1 - a ^ 2) * y (Fin.last (n + 1)) := by
  have hM :
      (Matrix.of (fun i j : Fin (n + 2) =>
          V * a ^ Nat.dist i.val j.val) +
        r • (1 : Matrix (Fin (n + 2)) (Fin (n + 2)) ℝ)).PosDef := by
    simpa only [Nat.add_assoc] using
      (AppliedSDE.SarkkaSolin.ar1_general_noisy_covariance_posdef
        (n + 1) a V r ha ha1 hV hr)
  exact AppliedSDE.SarkkaSolin.ar1_batch_posterior_innovation
    n a V r y hM
