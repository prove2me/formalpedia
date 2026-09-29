-- Prove2me | solution 1 for AutomorphicForm.hasDerivAt_apply_mul_archRealGLAt_inv_mul_archFlowMatrix_mul
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:05.340288+00:00
-- url     : https://prove2.me/submissions/319fcbf7-19de-5299-abe9-f9fd1a9b8cfb

import Definitions.Def_AutomorphicForm_ArchDerivCasimirComplex
import Definitions.Def_NumberField_PrincipalLevel
import Definitions.Def_AutomorphicForm_SmoothAutomorphicFnAt
import Definitions.Def_NumberField_AdelicHaar

import Theorems.Thm_AutomorphicForm_fderiv_apply_mul_archRealLiftAt_eq_of_isArchSmoothAt
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AutomorphicForm_hasDerivAt_apply_mul_archRealGLAt_inv_mul_archFlowMatrix_mul

set_option autoImplicit false

open MeasureTheory NumberField NumberField.AdelicLevel NumberField.AdelicHaar NumberField.InfinitePlace
open AutomorphicForm
open IsDedekindDomain

attribute [local instance] NumberField.AdelicHaar.glBorel

namespace DRProof

variable (K : Type) [Field K] [NumberField K]

theorem archRealLiftAt_coe {w : InfinitePlace K} (hw : w.IsReal) (g : GL (Fin 2) ℝ) :
    archRealLiftAt hw (Matrix.of.symm (g : Matrix (Fin 2) (Fin 2) ℝ)) = archRealGLAt (F := K) hw g := by
  have h : (Matrix.of (Matrix.of.symm (g : Matrix (Fin 2) (Fin 2) ℝ))).det ≠ 0 := by
    rw [Equiv.apply_symm_apply]
    exact ((Matrix.isUnit_iff_isUnit_det _).1 g.isUnit).ne_zero
  rw [archRealLiftAt_of_det_ne_zero hw h]
  congr 1
  ext i j
  rfl

theorem trace_archDirMatrix (d : ArchDir) : (archDirMatrix d) 0 0 + (archDirMatrix d) 1 1 = 0 := by
  cases d <;> simp [archDirMatrix]

theorem trace_conj (A B X : Matrix (Fin 2) (Fin 2) ℝ) (hBA : B * A = 1) :
    (A * X * B) 0 0 + (A * X * B) 1 1 = X 0 0 + X 1 1 := by
  have h1 : Matrix.trace (A * X * B) = Matrix.trace X := by
    rw [Matrix.trace_mul_cycle, hBA, one_mul]
  simpa [Matrix.trace_fin_two] using h1

end DRProof

open DRProof in
theorem solution
    (K : Type) [Field K] [NumberField K] {w : InfinitePlace K} (hw : w.IsReal)
    (G : AdelicGL2 (𝓞 K) K → ℂ) (hG : IsArchSmoothAt hw G) (y : AdelicGL2 (𝓞 K) K)
    (m : GL (Fin 2) ℝ) (d : ArchDir) :
    let Y : Matrix (Fin 2) (Fin 2) ℝ :=
      ((m⁻¹ : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) * archDirMatrix d * (m : Matrix (Fin 2) (Fin 2) ℝ)
    HasDerivAt (fun s : ℝ => G (y * archRealGLAt hw (m⁻¹ * archFlowMatrix d s * m)))
      ((((Y 0 0 - Y 1 1) / 2 : ℝ) : ℂ) * archDerivAt hw ArchDir.H G y +
        ((Y 0 1 : ℝ) : ℂ) * archDerivAt hw ArchDir.E G y +
        ((Y 1 0 : ℝ) : ℂ) * archDerivAt hw ArchDir.Fm G y) 0 := by
  intro Y

  set A : Matrix (Fin 2) (Fin 2) ℝ := ((m⁻¹ : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) with hA
  set B : Matrix (Fin 2) (Fin 2) ℝ := ((m : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) with hB
  have hBA : B * A = 1 := by rw [hA, hB, ← Units.val_mul, mul_inv_cancel, Units.val_one]
  have hAB : A * B = 1 := by rw [hA, hB, ← Units.val_mul, inv_mul_cancel, Units.val_one]
  set e : ℝ → (Fin 2 → Fin 2 → ℝ) := fun s =>
    Matrix.of.symm (A * (archFlowMatrix d s : Matrix (Fin 2) (Fin 2) ℝ) * B) with he
  have hcurve : (fun s : ℝ => G (y * archRealGLAt hw (m⁻¹ * archFlowMatrix d s * m))) =
      (fun e' : Fin 2 → Fin 2 → ℝ => G (y * archRealLiftAt hw e')) ∘ e := by
    funext s
    simp only [Function.comp, he]
    rw [show A * (archFlowMatrix d s : Matrix (Fin 2) (Fin 2) ℝ) * B = ((m⁻¹ * archFlowMatrix d s * m : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ)
      by rw [hA, hB, Units.val_mul, Units.val_mul], archRealLiftAt_coe K hw]

  have hderiv : HasDerivAt e (Matrix.of.symm (A * archDirMatrix d * B)) 0 := by
    rw [hasDerivAt_pi]; intro i; rw [hasDerivAt_pi]; intro j
    simp only [he, Matrix.of_symm_apply, Matrix.mul_apply]
    refine HasDerivAt.fun_sum fun l _ => ?_
    exact (HasDerivAt.fun_sum fun k _ => (hasDerivAt_archFlowMatrix_apply d k l).const_mul (A i k)).mul_const (B l j)

  have he0 : e 0 = Matrix.of.symm (1 : Matrix (Fin 2) (Fin 2) ℝ) := by
    simp only [he, archFlowMatrix_zero, Units.val_one, mul_one, hAB]
  have hdet : (Matrix.of (Matrix.of.symm (1 : Matrix (Fin 2) (Fin 2) ℝ))).det ≠ 0 := by
    rw [Equiv.apply_symm_apply, Matrix.det_one]; exact one_ne_zero

  have hΦ : HasFDerivAt (fun e' : Fin 2 → Fin 2 → ℝ => G (y * archRealLiftAt hw e'))
      (fderiv ℝ (fun e' : Fin 2 → Fin 2 → ℝ => G (y * archRealLiftAt hw e')) (e 0)) (e 0) := by
    rw [he0]
    exact (((hG y).contDiffAt (isOpen_setOf_det_ne_zero.mem_nhds hdet)).differentiableAt (by simp)).hasFDerivAt
  have hchain := hΦ.comp_hasDerivAt (x := (0 : ℝ)) hderiv
  rw [hcurve]
  refine hchain.congr_deriv ?_

  rw [he0, AutomorphicForm.fderiv_apply_mul_archRealLiftAt_eq_of_isArchSmoothAt K hw G hG y _ hdet]
  simp only [Equiv.apply_symm_apply, inv_one, one_mul, archRealLiftAt_of_symm_one, mul_one]
  have htr : (A * archDirMatrix d * B) 0 0 + (A * archDirMatrix d * B) 1 1 = 0 := by
    rw [trace_conj A B _ hBA, trace_archDirMatrix]
  have hY : Y = A * archDirMatrix d * B := rfl
  rw [← hY] at htr ⊢
  rw [htr]
  push_cast
  ring

end S_AutomorphicForm_hasDerivAt_apply_mul_archRealGLAt_inv_mul_archFlowMatrix_mul
end P2MW
export P2MW.S_AutomorphicForm_hasDerivAt_apply_mul_archRealGLAt_inv_mul_archFlowMatrix_mul (solution)
