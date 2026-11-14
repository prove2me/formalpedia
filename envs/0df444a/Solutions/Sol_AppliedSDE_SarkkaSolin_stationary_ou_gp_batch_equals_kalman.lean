-- Prove2me | solution 1 for AppliedSDE.SarkkaSolin.stationary_ou_gp_batch_equals_kalman
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-13T22:46:20.149063+00:00
-- url     : https://prove2.me/submissions/04c3ff4f-f80e-42c2-8d10-7ce0b8e68b9f
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_AppliedSDE_SarkkaSolin_OUKalmanInterfaces
import Theorems.Thm_AppliedSDE_SarkkaSolin_stationary_ou_covariance_grid_equals_ar_power
import Theorems.Thm_AppliedSDE_SarkkaSolin_ar1_batch_kalman_core
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

set_option autoImplicit false
open scoped BigOperators

theorem solution
    (n : ℕ) (rate q Δ r : ℝ)
    (hrate : 0 < rate) (hq : 0 < q) (hΔ : 0 < Δ) (hr : 0 < r)
    (y : Fin (n + 1) → ℝ) (m P : Fin (n + 1) → ℝ) :
    let V : ℝ := q / (2 * rate)
    let a : ℝ := AppliedSDE.SarkkaSolin.ouStepFactor rate Δ
    let K : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ :=
      fun i j => AppliedSDE.SarkkaSolin.stationaryOUCovariance rate q ((i.val : ℝ) * Δ) ((j.val : ℝ) * Δ)
    (P 0 = V * r / (V + r)) →
    (m 0 = V / (V + r) * y 0) →
    (∀ k : Fin n,
      let predicted : ℝ := AppliedSDE.SarkkaSolin.ouPredictedVariance rate q Δ (P k.castSucc)
      P k.succ = AppliedSDE.SarkkaSolin.scalarUpdatedVariance predicted r ∧
      m k.succ = a * m k.castSucc +
        AppliedSDE.SarkkaSolin.scalarKalmanGain predicted r * (y k.succ - a * m k.castSucc)) →
    m (Fin.last n) =
      AppliedSDE.SarkkaSolin.gpBatchPosteriorMean K r y
        (Fin.last n) := by
  dsimp only
  intro hP0 hm0 hrec
  let V : ℝ := q / (2 * rate)
  let a : ℝ := AppliedSDE.SarkkaSolin.ouStepFactor rate Δ
  let K : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ :=
    fun i j => AppliedSDE.SarkkaSolin.stationaryOUCovariance rate q
      ((i.val : ℝ) * Δ) ((j.val : ℝ) * Δ)
  have ha : 0 < a := by
    dsimp [a, AppliedSDE.SarkkaSolin.ouStepFactor]
    exact Real.exp_pos _
  have ha1 : a < 1 := by
    dsimp [a, AppliedSDE.SarkkaSolin.ouStepFactor]
    apply Real.exp_lt_one_iff.mpr
    have hrd : 0 < rate * Δ := mul_pos hrate hΔ
    linarith
  have hV : 0 < V := by
    dsimp [V]
    exact div_pos hq (by positivity)
  have hrec' : ∀ k : Fin n,
      let predicted : ℝ := a ^ 2 * P k.castSucc + V * (1 - a ^ 2)
      P k.succ = predicted * r / (predicted + r) ∧
      m k.succ = a * m k.castSucc +
        predicted / (predicted + r) *
          (y k.succ - a * m k.castSucc) := by
    intro k
    have hk := hrec k
    change
      (P k.succ =
        (a ^ 2 * P k.castSucc + V * (1 - a ^ 2)) * r /
          ((a ^ 2 * P k.castSucc + V * (1 - a ^ 2)) + r)) ∧
      (m k.succ = a * m k.castSucc +
        ((a ^ 2 * P k.castSucc + V * (1 - a ^ 2)) /
          ((a ^ 2 * P k.castSucc + V * (1 - a ^ 2)) + r)) *
          (y k.succ - a * m k.castSucc)) at hk
    exact hk
  have hK :
      K = ((fun i j : Fin (n + 1) =>
        V * a ^ Nat.dist i.val j.val) :
        Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ) := by
    ext i j
    simpa only [K, V, a] using
      (AppliedSDE.SarkkaSolin.stationary_ou_covariance_grid_equals_ar_power
        rate q Δ hrate hΔ i.val j.val)
  have hcore :=
    AppliedSDE.SarkkaSolin.ar1_batch_kalman_core
      n a V r ha ha1 hV hr y m P hP0 hm0 hrec'
  change m (Fin.last n) =
    AppliedSDE.SarkkaSolin.gpBatchPosteriorMean K r y (Fin.last n)
  rw [hK]
  simpa only [AppliedSDE.SarkkaSolin.gpBatchPosteriorMean] using hcore
