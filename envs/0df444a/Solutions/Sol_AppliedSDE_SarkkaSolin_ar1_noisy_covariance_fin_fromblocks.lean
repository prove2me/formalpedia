-- Prove2me | solution 1 for AppliedSDE.SarkkaSolin.ar1_noisy_covariance_fin_fromblocks
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-14T09:26:23.082996+00:00
-- url     : https://prove2.me/submissions/f4cd635d-0fdc-4c73-8239-0a2038d119e4

import Mathlib
set_option autoImplicit false
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true
open Matrix
open scoped Matrix

theorem solution
    (n : ℕ) (a V r : ℝ) :
    let e : (Fin (n + 1) ⊕ Fin 1) ≃ Fin (n + 2) := finSumFinEquiv
    let Cnew : Matrix (Fin (n + 2)) (Fin (n + 2)) ℝ :=
      (Matrix.of (fun i j => V * a ^ Nat.dist i.val j.val)) +
        r • (1 : Matrix (Fin (n + 2)) (Fin (n + 2)) ℝ)
    let Cold : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ :=
      (Matrix.of (fun i j => V * a ^ Nat.dist i.val j.val)) +
        r • (1 : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ)
    let B : Matrix (Fin (n + 1)) (Fin 1) ℝ :=
      fun i _ => V * a ^ (n + 1 - i.val)
    let D : Matrix (Fin 1) (Fin 1) ℝ := fun _ _ => V + r
    Cnew.submatrix e e = Matrix.fromBlocks Cold B B.transpose D := by
  classical
  ext i j
  rcases i with i | i <;> rcases j with j | j
  · simp [Matrix.submatrix_apply, Matrix.fromBlocks,
      finSumFinEquiv_apply_left, Matrix.add_apply,
      Matrix.smul_apply, Matrix.one_apply]
  · fin_cases j
    have hne : (Fin.castAdd 1 i : Fin (n + 2)) ≠
        Fin.natAdd (n + 1) (0 : Fin 1) := by
      intro heq
      have hv : i.val = n + 1 := by
        simpa [Fin.val_castAdd, Fin.val_natAdd] using congrArg Fin.val heq
      exact (Nat.ne_of_lt i.isLt) hv
    have hd : Nat.dist i.val (n + 1) = n + 1 - i.val := by
      rw [Nat.dist_comm i.val (n + 1),
        Nat.dist_eq_sub_of_le_right (Nat.le_of_lt i.isLt)]
    simp [Matrix.submatrix_apply, Matrix.fromBlocks,
      finSumFinEquiv_apply_left, finSumFinEquiv_apply_right,
      Matrix.add_apply, Matrix.smul_apply, Matrix.one_apply, hne, hd]
  · fin_cases i
    have hne : (Fin.natAdd (n + 1) (0 : Fin 1) : Fin (n + 2)) ≠
        Fin.castAdd 1 j := by
      intro heq
      have hv : n + 1 = j.val := by
        simpa [Fin.val_castAdd, Fin.val_natAdd] using congrArg Fin.val heq
      exact (Nat.ne_of_gt j.isLt) hv
    have hd : Nat.dist (n + 1) j.val = n + 1 - j.val := by
      rw [Nat.dist_eq_sub_of_le_right (Nat.le_of_lt j.isLt)]
    simp [Matrix.submatrix_apply, Matrix.fromBlocks,
      finSumFinEquiv_apply_left, finSumFinEquiv_apply_right,
      Matrix.add_apply, Matrix.smul_apply, Matrix.one_apply, hne, hd,
      Matrix.transpose_apply]
    rfl
  · fin_cases i
    fin_cases j
    simp [Matrix.submatrix_apply, Matrix.fromBlocks,
      finSumFinEquiv_apply_right, Matrix.add_apply,
      Matrix.smul_apply, Matrix.one_apply]
