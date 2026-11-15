-- Prove2me | solution 1 for AppliedSDE.SarkkaSolin.ar1_batch_covariance_fromBlocks_system
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-14T09:37:12.510866+00:00
-- url     : https://prove2.me/submissions/e6f43aa6-77b8-4399-b450-52f5271e65b6

import Mathlib
import Theorems.Thm_AppliedSDE_SarkkaSolin_ar1_general_noisy_covariance_posdef
import Theorems.Thm_AppliedSDE_SarkkaSolin_ar1_noisy_covariance_fin_fromblocks
set_option autoImplicit false
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true
open Matrix
open scoped Matrix

/-- The inverse of the entire noisy AR(1) covariance system solves the
corresponding true leading-block and appended-observation equations. -/
theorem solution
    (n : ℕ) (a V r : ℝ)
    (ha : 0 < a) (ha1 : a < 1) (hV : 0 < V) (hr : 0 < r)
    (y : Fin (n + 2) → ℝ) :
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
    let z := Cnew⁻¹ |>.mulVec y
    (Matrix.fromBlocks Cold B B.transpose D).mulVec (z ∘ e) =
      y ∘ e := by
  intro e Cnew Cold B D z
  have hpos : Cnew.PosDef := by
    simpa [Cnew, Nat.add_assoc] using
      (AppliedSDE.SarkkaSolin.ar1_general_noisy_covariance_posdef
        (n + 1) a V r ha ha1 hV hr)
  have hunit : IsUnit Cnew := hpos.isUnit
  have hdet : IsUnit Cnew.det :=
    (Matrix.isUnit_iff_isUnit_det Cnew).mp hunit
  have hmul : Cnew.mulVec z = y := by
    dsimp [z]
    rw [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv Cnew hdet,
      Matrix.one_mulVec]
  have hblock : Cnew.submatrix e e =
      Matrix.fromBlocks Cold B B.transpose D := by
    simpa [Cnew, Cold, B, D, e] using
      (AppliedSDE.SarkkaSolin.ar1_noisy_covariance_fin_fromblocks n a V r)
  have htransport :
      (Cnew.submatrix e e).mulVec (z ∘ e) =
        (Cnew.mulVec z) ∘ e := by
    rw [Matrix.submatrix_mulVec_equiv]
    simp [Function.comp_def]
  rw [← hblock, htransport, hmul]
