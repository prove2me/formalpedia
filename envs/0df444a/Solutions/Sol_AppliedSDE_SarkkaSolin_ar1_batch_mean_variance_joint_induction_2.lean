-- Prove2me | solution 2 for AppliedSDE.SarkkaSolin.ar1_batch_mean_variance_joint_induction
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-14T17:00:55.24119+00:00
-- url     : https://prove2.me/submissions/1b9b6164-8d57-490a-997d-91121dd3e63b

import Mathlib
import Theorems.Thm_AppliedSDE_SarkkaSolin_ar1_batch_kalman_zero_step
import Theorems.Thm_AppliedSDE_SarkkaSolin_ar1_batch_zero_step_variance_matrix
import Theorems.Thm_AppliedSDE_SarkkaSolin_ar1_general_noisy_covariance_posdef
import Theorems.Thm_AppliedSDE_SarkkaSolin_ar1_kalman_schur_innovation_positive_from_recursion
import Theorems.Thm_AppliedSDE_SarkkaSolin_ar1_true_covariance_append_joint_kalman_step
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
  induction n with
  | zero =>
      intro K C k hP0 hm0 hstep
      have hK : K = (fun _ _ => V : Matrix (Fin 1) (Fin 1) ℝ) := by
        ext i j
        fin_cases i
        fin_cases j
        simp [K]
      constructor
      · calc
          m (Fin.last 0) = V / (V + r) * y 0 := by simpa using hm0
          _ = (K.mulVec (C⁻¹.mulVec y)) (Fin.last 0) := by
            simpa [K, C, hK] using
              (AppliedSDE.SarkkaSolin.ar1_batch_kalman_zero_step
                V r hV hr y).symm
      · calc
          P (Fin.last 0) = V * r / (V + r) := by simpa using hP0
          _ = V - (k ⬝ᵥ C⁻¹.mulVec k) := by
            simpa [K, C, k, hK] using
              (AppliedSDE.SarkkaSolin.ar1_batch_zero_step_variance_matrix
                V r hV hr).symm
  | succ n ih =>
      intro K C k hP0 hm0 hstep
      let yold : Fin (n + 1) -> ℝ := fun j => y j.castSucc
      let mold : Fin (n + 1) -> ℝ := fun j => m j.castSucc
      let Pold : Fin (n + 1) -> ℝ := fun j => P j.castSucc
      have hP0old : Pold 0 = V * r / (V + r) := by simpa [Pold] using hP0
      have hm0old : mold 0 = V / (V + r) * yold 0 := by
        simpa [mold, yold] using hm0
      have hstepold : ∀ j : Fin n,
          let pred : ℝ := a ^ 2 * Pold j.castSucc + V * (1 - a ^ 2)
          Pold j.succ = pred * r / (pred + r) ∧
          mold j.succ = a * mold j.castSucc +
            pred / (pred + r) * (yold j.succ - a * mold j.castSucc) := by
        intro j
        simpa [Pold, mold, yold] using (hstep j.castSucc)
      have hold := ih yold mold Pold hP0old hm0old hstepold
      let Kold : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ :=
        Matrix.of fun i j => V * a ^ Nat.dist i.val j.val
      let Cold : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ :=
        Kold + r • (1 : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ)
      let kold : Fin (n + 1) -> ℝ :=
        fun j => V * a ^ Nat.dist n j.val
      have hmean : mold (Fin.last n) =
          kold ⬝ᵥ (Cold⁻¹.mulVec yold) := by
        simpa [Kold, Cold, kold, Matrix.mulVec, dotProduct] using hold.1
      have hvar : Pold (Fin.last n) =
          V - (kold ⬝ᵥ (Cold⁻¹.mulVec kold)) := by
        simpa [Kold, Cold, kold] using hold.2
      have hpos : Cold.PosDef := by
        simpa [Cold, Kold] using
          (AppliedSDE.SarkkaSolin.ar1_general_noisy_covariance_posdef
            n a V r ha ha1 hV hr)
      have hdet : IsUnit Cold.det :=
        (Matrix.isUnit_iff_isUnit_det Cold).mp hpos.isUnit
      have hAM : Cold⁻¹ * Cold = 1 := Matrix.nonsing_inv_mul Cold hdet
      have hS : (V + r) - ((a • kold) ⬝ᵥ
          Cold⁻¹.mulVec (a • kold)) ≠ 0 :=
        ne_of_gt (AppliedSDE.SarkkaSolin.ar1_kalman_schur_innovation_positive_from_recursion
          n a V r ha ha1 hV hr Pold hP0old
            (fun j => (hstepold j).1) Cold⁻¹ kold hvar)
      have hbatch :=
        AppliedSDE.SarkkaSolin.ar1_true_covariance_append_joint_kalman_step
          n a V r ha ha1 hV hr y (Pold (Fin.last n))
          (mold (Fin.last n)) hAM hvar hmean hS
      have hlast := hstep (Fin.last n)
      dsimp at hbatch hlast
      constructor
      · exact hlast.2.trans hbatch.1.symm
      · exact hlast.1.trans hbatch.2.symm
