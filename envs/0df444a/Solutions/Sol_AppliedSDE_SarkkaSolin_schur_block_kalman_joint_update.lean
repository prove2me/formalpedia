-- Prove2me | solution 1 for AppliedSDE.SarkkaSolin.schur_block_kalman_joint_update
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-14T13:53:15.354904+00:00
-- url     : https://prove2.me/submissions/5ff2052b-8876-43a5-9914-bbfd7edc3563

import Mathlib
import Theorems.Thm_AppliedSDE_SarkkaSolin_ar1_schur_predicted_variance
import Theorems.Thm_AppliedSDE_SarkkaSolin_schur_fromBlocks_covariance_posterior_mean
import Theorems.Thm_AppliedSDE_SarkkaSolin_schur_fromBlocks_covariance_posterior_variance
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open Matrix
open scoped Matrix
set_option autoImplicit false
theorem solution
    (n : ℕ) (M A : Matrix (Fin n) (Fin n) ℝ)
    (hAM : A * M = 1)
    (k u : Fin n -> ℝ)
    (a V r Pold mold ynew : ℝ)
    (hP : Pold = V - (k ⬝ᵥ A.mulVec k))
    (hm : mold = k ⬝ᵥ A.mulVec u)
    (zM zV : Fin n ⊕ Fin 1 -> ℝ)
    (hBM :
      (Matrix.fromBlocks M
        (fun i (_ : Fin 1) => (a • k) i )
        (fun (_ : Fin 1) j => (a • k) j )
        (fun (_ _ : Fin 1) => V + r )).mulVec zM =
        Sum.elim u (fun _ : Fin 1 => ynew))
    (hBV :
      (Matrix.fromBlocks M
        (fun i (_ : Fin 1) => (a • k) i )
        (fun (_ : Fin 1) j => (a • k) j )
        (fun (_ _ : Fin 1) => V + r )).mulVec zV =
        Sum.elim (a • k) (fun _ : Fin 1 => V))
    (hS : (V + r) - ((a • k) ⬝ᵥ A.mulVec (a • k)) ≠ 0) :
    let pred : ℝ := a ^ 2 * Pold + V * (1 - a ^ 2)
    (((a • k) ⬝ᵥ (zM ∘ Sum.inl)) +
        V * zM (Sum.inr (0 : Fin 1)) =
      a * mold + pred / (pred + r) * (ynew - a * mold)) ∧
    (V - (((a • k) ⬝ᵥ (zV ∘ Sum.inl)) +
        V * zV (Sum.inr (0 : Fin 1))) =
      pred * r / (pred + r)) := by
  classical
  let b : Fin n -> ℝ := a • k
  let pred : ℝ := a ^ 2 * Pold + V * (1 - a ^ 2)
  have hpred :
      V - ((a • k) ⬝ᵥ A.mulVec (a • k)) = pred := by
    exact AppliedSDE.SarkkaSolin.ar1_schur_predicted_variance
      n A k a V Pold hP
  have hden :
      (V + r) - ((a • k) ⬝ᵥ A.mulVec (a • k)) =
        pred + r := by linarith [hpred]
  have hdenne : pred + r ≠ 0 := by
    rw [← hden]
    exact hS
  have hmean :=
    AppliedSDE.SarkkaSolin.schur_fromBlocks_covariance_posterior_mean
      n M A (a • k) V r
      (Sum.elim u (fun _ : Fin 1 => ynew)) zM hAM hBM hS
  have hvariance :=
    AppliedSDE.SarkkaSolin.schur_fromBlocks_covariance_posterior_variance
      n M A (a • k) V r zV hAM hBV hS
  have hdot :
      ((a • k) ⬝ᵥ A.mulVec u) = a * mold := by
    simpa only [smul_dotProduct, smul_eq_mul, hm]
  have hmeanEq :
      ((a • k) ⬝ᵥ (zM ∘ Sum.inl)) +
        V * zM (Sum.inr (0 : Fin 1)) =
      ynew - r * ((ynew - a * mold) / (pred + r)) := by
    rw [hden] at hmean
    simpa [Function.comp_def, hdot] using hmean
  have hvarianceEq :
      V - (((a • k) ⬝ᵥ (zV ∘ Sum.inl)) +
        V * zV (Sum.inr (0 : Fin 1))) =
        pred * r / (pred + r) := by
    simpa only [hpred, hden] using hvariance
  have hscalar :
      ynew - r * ((ynew - a * mold) / (pred + r)) =
        a * mold + pred / (pred + r) * (ynew - a * mold) := by
    field_simp [hdenne]
    ring
  change
    (((a • k) ⬝ᵥ (zM ∘ Sum.inl)) +
      V * zM (Sum.inr (0 : Fin 1)) =
        a * mold + pred / (pred + r) * (ynew - a * mold)) ∧
    (V - (((a • k) ⬝ᵥ (zV ∘ Sum.inl)) +
      V * zV (Sum.inr (0 : Fin 1))) =
        pred * r / (pred + r))
  exact ⟨hmeanEq.trans hscalar, hvarianceEq⟩
