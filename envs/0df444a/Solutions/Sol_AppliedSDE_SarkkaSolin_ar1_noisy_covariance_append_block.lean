-- Prove2me | solution 1 for AppliedSDE.SarkkaSolin.ar1_noisy_covariance_append_block
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-14T09:17:37.840184+00:00
-- url     : https://prove2.me/submissions/90d6f4f0-6bf4-47f0-96e6-00bf9279c51e

import Mathlib
set_option autoImplicit false
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true
open Matrix

theorem solution
    (n : ℕ) (a V r : ℝ) :
    let Cnew : Matrix (Fin (n + 2)) (Fin (n + 2)) ℝ :=
      (Matrix.of (fun i j => V * a ^ Nat.dist i.val j.val)) +
        r • (1 : Matrix (Fin (n + 2)) (Fin (n + 2)) ℝ)
    let Cold : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ :=
      (Matrix.of (fun i j => V * a ^ Nat.dist i.val j.val)) +
        r • (1 : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ)
    Cnew.submatrix Fin.castSucc Fin.castSucc = Cold ∧
      (∀ i : Fin (n + 1),
        Cnew (Fin.castSucc i) (Fin.last (n + 1)) =
          V * a ^ (n + 1 - i.val)) ∧
      Cnew (Fin.last (n + 1)) (Fin.last (n + 1)) = V + r := by
  classical
  constructor
  · ext i j
    simp only [Matrix.submatrix_apply, Matrix.add_apply, Matrix.smul_apply,
      Matrix.one_apply, Fin.val_castSucc]
    simp [Fin.castSucc_inj]
  constructor
  · intro i
    have hne : (Fin.castSucc i : Fin (n + 2)) ≠ Fin.last (n + 1) :=
      Fin.castSucc_ne_last _
    simp only [Matrix.add_apply, Matrix.smul_apply, Matrix.one_apply,
      if_neg hne, smul_eq_mul, mul_zero, add_zero]
    change V * a ^ Nat.dist i.val (n + 1) =
      V * a ^ (n + 1 - i.val)
    rw [Nat.dist_comm i.val (n + 1), Nat.dist_eq_sub_of_le_right (Nat.le_of_lt i.isLt)]
  · simp [Matrix.add_apply, Matrix.smul_apply, Matrix.one_apply,
      Nat.dist_self]
