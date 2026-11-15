-- Prove2me | solution 1 for AppliedSDE.SarkkaSolin.ar1_general_noisy_covariance_posdef
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-14T08:08:39.729231+00:00
-- url     : https://prove2.me/submissions/91ba36ea-6cb8-4c86-95e8-4c35692d62ba

import Mathlib
import Definitions.Def_AppliedSDE_SarkkaSolin_OUKalmanInterfaces
import Theorems.Thm_AppliedSDE_SarkkaSolin_ar1_noisy_covariance_posdef
set_option autoImplicit false
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true
open Matrix

theorem solution
    (n : ℕ) (a V r : ℝ)
    (ha : 0 < a) (ha1 : a < 1) (hV : 0 < V) (hr : 0 < r) :
    ((Matrix.of (fun i j : Fin (n + 1) => V * a ^ Nat.dist i.val j.val)) +
        r • (1 : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ)).PosDef := by
  let rate : ℝ := -Real.log a
  let q : ℝ := 2 * rate * V
  have hrate : 0 < rate := by
    dsimp [rate]
    exact neg_pos.mpr (Real.log_neg ha ha1)
  have hq : 0 < q := by
    dsimp [q]
    positivity
  have hrate2 : 2 * rate ≠ 0 :=
    ne_of_gt (mul_pos (by norm_num) hrate)
  have hratio : q / (2 * rate) = V := by
    dsimp [q]
    apply (div_eq_iff hrate2).mpr
    ring
  have hfac : AppliedSDE.SarkkaSolin.ouStepFactor rate 1 = a := by
    change Real.exp (-rate * 1) = a
    dsimp [rate]
    simpa using Real.exp_log ha
  have hpos :=
    AppliedSDE.SarkkaSolin.ar1_noisy_covariance_posdef
      n rate q 1 r hrate hq (by norm_num) hr
  simpa only [hratio, hfac] using hpos
