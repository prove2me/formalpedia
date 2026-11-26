-- Prove2me | solution 1 for Arxiv2205_09234.weighted_l2_form
-- status  : ACCEPTED   (prove)
-- author  : @garyholm
-- created : 2026-11-26T00:02:05.983837+00:00
-- url     : https://prove2.me/submissions/095f1478-85b6-497a-8f59-7af93da3ee44

import Mathlib
import Definitions.Def_Arxiv2205_09234_Basic

set_option autoImplicit false

open Complex

open Arxiv2205_09234 in
theorem solution (N : ℕ) (hN : 0 < N) (dt α : ℝ) (hdt : 0 < dt) (w : Fin N → ℝ)
    (hw : IsFreqWeight N dt α w) (dm dobs : Fin N → ℝ) :
    let rhat : Fin N → ℂ := fun k => dft N dm k - dft N dobs k
    let r : Fin N → ℂ := fun j => ((dm j - dobs j : ℝ) : ℂ)
    ((discreteMetric N 2 w dm dobs ^ 2 : ℝ) : ℂ) = star rhat ⬝ᵥ (weightMat w).mulVec rhat ∧
      star rhat ⬝ᵥ (weightMat w).mulVec rhat =
        r ⬝ᵥ ((dftMat N).conjTranspose * weightMat w * dftMat N).mulVec r := by
  intro rhat r
  have hrhat : rhat = (dftMat N).mulVec r := by
    funext k
    show dft N dm k - dft N dobs k = _
    have hd : ∀ (x : Fin N → ℝ), dft N x k = ∑ j, dftMat N k j * (x j : ℂ) := fun x => rfl
    rw [hd, hd, ← Finset.sum_sub_distrib]
    show _ = ∑ j, dftMat N k j * r j
    congr 1; funext j; simp only [r]; push_cast; ring
  constructor
  · unfold discreteMetric
    have e : ∀ k, ‖rhat k‖ ^ (2:ℝ) = ‖rhat k‖ ^ (2:ℕ) := fun k => by
      exact_mod_cast Real.rpow_natCast _ 2
    simp only [rhat] at e
    simp only [e]
    have hnn : 0 ≤ ∑ k, w k * ‖dft N dm k - dft N dobs k‖ ^ 2 :=
      Finset.sum_nonneg (fun k _ => mul_nonneg (hw.1 k) (sq_nonneg _))
    rw [← Real.sqrt_eq_rpow, Real.sq_sqrt hnn]
    push_cast
    unfold weightMat dotProduct
    congr 1; funext k
    rw [Matrix.mulVec_diagonal]
    simp only [Pi.star_apply, rhat]
    rw [← Complex.conj_mul']
    simp only [RCLike.star_def]
    ring
  · rw [hrhat, Matrix.star_mulVec, ← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec,
      Matrix.mulVec_mulVec]
    have hs : star r = r := by
      funext j; simp [r, Complex.conj_ofReal]
    rw [hs, Matrix.mul_assoc]
