-- Prove2me | solution 1 for AppliedSDE.SarkkaSolin.ar1_noisy_covariance_posdef
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-13T22:57:07.607242+00:00
-- url     : https://prove2.me/submissions/4d5bb79e-5131-4364-ba60-9d7eefb17514

import Mathlib
import Definitions.Def_AppliedSDE_SarkkaSolin_OUKalmanInterfaces
import Theorems.Thm_AppliedSDE_SarkkaSolin_noisy_ou_covariance_positive_definite
import Theorems.Thm_AppliedSDE_SarkkaSolin_stationary_ou_covariance_grid_equals_ar_power
set_option autoImplicit false
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true
open Matrix
open scoped BigOperators

theorem solution
    (n : ℕ) (rate q Δ r : ℝ)
    (hrate : 0 < rate) (hq : 0 < q) (hΔ : 0 < Δ) (hr : 0 < r) :
    ((Matrix.of fun i j : Fin (n + 1) =>
        q / (2 * rate) *
          (AppliedSDE.SarkkaSolin.ouStepFactor rate Δ) ^ Nat.dist i.val j.val) +
      r • (1 : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ)).PosDef := by
  let V : ℝ := q / (2 * rate)
  let a : ℝ := AppliedSDE.SarkkaSolin.ouStepFactor rate Δ
  let K : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ :=
    Matrix.of fun i j => V * a ^ Nat.dist i.val j.val
  have hV : 0 ≤ V := (div_pos hq (by positivity)).le
  have hK (i j : Fin (n + 1)) :
      K i j = V * Real.exp
        (-rate * |((i.val : ℝ) * Δ) - ((j.val : ℝ) * Δ)|) := by
    calc
      K i j = q / (2 * rate) *
          (AppliedSDE.SarkkaSolin.ouStepFactor rate Δ) ^
            Nat.dist i.val j.val := rfl
      _ = AppliedSDE.SarkkaSolin.stationaryOUCovariance rate q
            ((i.val : ℝ) * Δ) ((j.val : ℝ) * Δ) :=
          (AppliedSDE.SarkkaSolin.stationary_ou_covariance_grid_equals_ar_power
            rate q Δ hrate hΔ i.val j.val).symm
      _ = V * Real.exp
            (-rate * |((i.val : ℝ) * Δ) - ((j.val : ℝ) * Δ)|) := rfl
  have hsym : (K + r • (1 : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ)).IsHermitian := by
    apply Matrix.IsHermitian.ext
    intro i j
    simp [K, Matrix.add_apply, Matrix.smul_apply, Matrix.one_apply,
      Nat.dist_comm, eq_comm]
  have hentry (i j : Fin (n + 1)) :
      (K + r • (1 : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ)) i j =
        V * Real.exp
          (-rate * |((i.val : ℝ) * Δ) - ((j.val : ℝ) * Δ)|) +
          (if i = j then r else 0) := by
    simp only [Matrix.add_apply, Matrix.smul_apply, Matrix.one_apply, hK]
    by_cases hij : i = j
    · subst j
      simp
    · simp [hij]
  change (K + r • (1 : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ)).PosDef
  apply Matrix.PosDef.of_dotProduct_mulVec_pos hsym
  intro x hx
  have hquad :=
    AppliedSDE.SarkkaSolin.noisy_ou_covariance_positive_definite
      (n + 1) rate V r hrate hV hr
      (fun i : Fin (n + 1) => (i.val : ℝ) * Δ) x hx
  simpa [dotProduct, Matrix.mulVec, Finset.mul_sum, hentry,
    mul_assoc, mul_comm, mul_left_comm] using hquad
