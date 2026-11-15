-- Prove2me | solution 2 for AppliedSDE.SarkkaSolin.stationary_ou_gp_batch_equals_kalman
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-14T09:06:10.405194+00:00
-- url     : https://prove2.me/submissions/caebfe74-4fed-4444-886a-7a42929e90de

import Mathlib
import Definitions.Def_AppliedSDE_SarkkaSolin_OUKalmanInterfaces
import Theorems.Thm_AppliedSDE_SarkkaSolin_stationary_ou_covariance_grid_equals_ar_power
import Theorems.Thm_AppliedSDE_SarkkaSolin_ar1_batch_kalman_core
set_option autoImplicit false
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true
open Matrix
open scoped BigOperators Matrix

theorem solution
    (n : ℕ) (rate q Δ r : ℝ)
    (hrate : 0 < rate) (hq : 0 < q) (hΔ : 0 < Δ) (hr : 0 < r)
    (y : Fin (n + 1) → ℝ) (m P : Fin (n + 1) → ℝ) :
    let V : ℝ := q / (2 * rate)
    let a : ℝ := AppliedSDE.SarkkaSolin.ouStepFactor rate Δ
    let K : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ :=
      fun i j => AppliedSDE.SarkkaSolin.stationaryOUCovariance
        rate q ((i.val : ℝ) * Δ) ((j.val : ℝ) * Δ)
    (P 0 = V * r / (V + r)) →
    (m 0 = V / (V + r) * y 0) →
    (∀ k : Fin n,
      let predicted : ℝ :=
        AppliedSDE.SarkkaSolin.ouPredictedVariance rate q Δ (P k.castSucc)
      P k.succ = AppliedSDE.SarkkaSolin.scalarUpdatedVariance predicted r ∧
      m k.succ = a * m k.castSucc +
        AppliedSDE.SarkkaSolin.scalarKalmanGain predicted r *
          (y k.succ - a * m k.castSucc)) →
    m (Fin.last n) =
      AppliedSDE.SarkkaSolin.gpBatchPosteriorMean K r y
        (Fin.last n) := by
  intro V a K hp hm hs
  have hV : 0 < V := by
    dsimp [V]
    exact div_pos hq (mul_pos (by norm_num) hrate)
  have ha : 0 < a := by
    dsimp [a, AppliedSDE.SarkkaSolin.ouStepFactor]
    exact Real.exp_pos _
  have hneg : -rate * Δ < 0 := by
    nlinarith [mul_pos hrate hΔ]
  have ha1 : a < 1 := by
    dsimp [a, AppliedSDE.SarkkaSolin.ouStepFactor]
    exact Real.exp_lt_one_iff.mpr hneg
  have hs' : ∀ k : Fin n,
      let predicted : ℝ := a ^ 2 * P k.castSucc + V * (1 - a ^ 2)
      P k.succ = predicted * r / (predicted + r) ∧
      m k.succ = a * m k.castSucc +
        predicted / (predicted + r) *
          (y k.succ - a * m k.castSucc) := by
    intro k
    simpa [a, V, AppliedSDE.SarkkaSolin.ouPredictedVariance,
      AppliedSDE.SarkkaSolin.scalarUpdatedVariance,
      AppliedSDE.SarkkaSolin.scalarKalmanGain] using hs k
  have hcore :=
    AppliedSDE.SarkkaSolin.ar1_batch_kalman_core
      n a V r ha ha1 hV hr y m P hp hm hs'
  have hK :
      (fun i j : Fin (n + 1) =>
        AppliedSDE.SarkkaSolin.stationaryOUCovariance
          rate q ((i.val : ℝ) * Δ) ((j.val : ℝ) * Δ)) =
      (fun i j : Fin (n + 1) =>
        V * a ^ Nat.dist i.val j.val) := by
    funext i j
    simpa [V, a] using
      (AppliedSDE.SarkkaSolin.stationary_ou_covariance_grid_equals_ar_power
        rate q Δ hrate hΔ i.val j.val)
  change K = (fun i j : Fin (n + 1) =>
    V * a ^ Nat.dist i.val j.val) at hK
  change m (Fin.last n) =
    AppliedSDE.SarkkaSolin.gpBatchPosteriorMean K r y (Fin.last n)
  rw [hK]
  simpa [AppliedSDE.SarkkaSolin.gpBatchPosteriorMean] using hcore
