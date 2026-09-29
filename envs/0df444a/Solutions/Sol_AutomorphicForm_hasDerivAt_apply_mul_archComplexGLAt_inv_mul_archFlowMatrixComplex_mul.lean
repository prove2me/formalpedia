-- Prove2me | solution 1 for AutomorphicForm.hasDerivAt_apply_mul_archComplexGLAt_inv_mul_archFlowMatrixComplex_mul
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:05.340288+00:00
-- url     : https://prove2.me/submissions/4156a401-adc7-50c0-8634-65e11daef8af

import Definitions.Def_AutomorphicForm_ArchDerivCasimirComplex
import Definitions.Def_NumberField_PrincipalLevel
import Definitions.Def_AutomorphicForm_SmoothAutomorphicFnAt
import Definitions.Def_NumberField_AdelicHaar

import Theorems.Thm_AutomorphicForm_fderiv_apply_mul_archComplexLiftAt_eq_of_isArchSmoothAtComplex
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AutomorphicForm_hasDerivAt_apply_mul_archComplexGLAt_inv_mul_archFlowMatrixComplex_mul

set_option autoImplicit false

open MeasureTheory NumberField NumberField.AdelicLevel NumberField.AdelicHaar NumberField.InfinitePlace
open AutomorphicForm
open IsDedekindDomain

attribute [local instance] NumberField.AdelicHaar.glBorel
open scoped ComplexConjugate

namespace DCProof

variable (K : Type) [Field K] [NumberField K]

def XC : ArchDirComplex → Matrix (Fin 2) (Fin 2) ℂ := fun d => match d with
  | .H => !![1, 0; 0, -1] | .E => !![0, 1; 0, 0] | .Fm => !![0, 0; 1, 0]
  | .iH => !![Complex.I, 0; 0, -Complex.I] | .iE => !![0, Complex.I; 0, 0] | .iFm => !![0, 0; Complex.I, 0]

theorem archComplexLiftAt_coe {w : InfinitePlace K} (hw : w.IsComplex) (g : GL (Fin 2) ℂ) :
    archComplexLiftAt hw (Matrix.of.symm (g : Matrix (Fin 2) (Fin 2) ℂ)) = archComplexGLAt (F := K) hw g := by
  have h : (Matrix.of (Matrix.of.symm (g : Matrix (Fin 2) (Fin 2) ℂ))).det ≠ 0 := by
    rw [Equiv.apply_symm_apply]
    exact ((Matrix.isUnit_iff_isUnit_det _).1 g.isUnit).ne_zero
  rw [archComplexLiftAt_of_det_ne_zero hw h]
  congr 1
  ext i j
  rfl

theorem archComplexLiftAt_of_symm_one {w : InfinitePlace K} (hw : w.IsComplex) :
    archComplexLiftAt hw (Matrix.of.symm (1 : Matrix (Fin 2) (Fin 2) ℂ)) = (1 : AdelicGL2 (𝓞 K) K) := by
  rw [show (1 : Matrix (Fin 2) (Fin 2) ℂ) = ((1 : GL (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ) from Units.val_one.symm,
    archComplexLiftAt_coe K hw, map_one]

theorem trace_XC (d : ArchDirComplex) : (XC d) 0 0 + (XC d) 1 1 = 0 := by
  cases d <;> simp [XC]

theorem trace_conj (A B X : Matrix (Fin 2) (Fin 2) ℂ) (hBA : B * A = 1) :
    (A * X * B) 0 0 + (A * X * B) 1 1 = X 0 0 + X 1 1 := by
  have h1 : Matrix.trace (A * X * B) = Matrix.trace X := by
    rw [Matrix.trace_mul_cycle, hBA, one_mul]
  simpa [Matrix.trace_fin_two] using h1

theorem hasDerivAt_archFlowMatrixComplex_apply (d : ArchDirComplex) (i j : Fin 2) :
    HasDerivAt (fun t : ℝ => (archFlowMatrixComplex d t : Matrix (Fin 2) (Fin 2) ℂ) i j) (XC d i j) 0 := by
  have h1 : HasDerivAt (fun t : ℝ => (t : ℂ)) 1 0 := by simpa using (hasDerivAt_id ((0 : ℝ) : ℂ)).comp_ofReal
  have h2 : HasDerivAt (fun t : ℝ => (t : ℂ) * Complex.I) Complex.I 0 := by simpa using h1.mul_const Complex.I
  have h3 : HasDerivAt (fun t : ℝ => Complex.exp (t : ℂ)) 1 0 := by simpa using h1.cexp
  have h4 : HasDerivAt (fun t : ℝ => Complex.exp (-(t : ℂ))) (-1) 0 := by simpa using h1.neg.cexp
  have h5 : HasDerivAt (fun t : ℝ => Complex.exp ((t : ℂ) * Complex.I)) Complex.I 0 := by simpa using h2.cexp
  have h6 : HasDerivAt (fun t : ℝ => Complex.exp (-((t : ℂ) * Complex.I))) (-Complex.I) 0 := by simpa using h2.neg.cexp
  cases d <;> fin_cases i <;> fin_cases j <;>
    simp only [archFlowMatrixComplex, splitTorusGL2Complex, unipotentGL2_coe, lowerUnipotentGL2_coe, XC,
      Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.empty_val', Matrix.cons_val_fin_one] <;>
    first
      | exact hasDerivAt_const _ _
      | exact h1 | exact h2 | exact h3 | exact h4 | exact h5 | exact h6

end DCProof

open DCProof in
theorem solution
    (K : Type) [Field K] [NumberField K] {w : InfinitePlace K} (hw : w.IsComplex)
    (G : AdelicGL2 (𝓞 K) K → ℂ) (hG : IsArchSmoothAtComplex hw G) (y : AdelicGL2 (𝓞 K) K)
    (m : GL (Fin 2) ℂ) (d : ArchDirComplex) :
    let X : Matrix (Fin 2) (Fin 2) ℂ := match d with
      | .H => !![1, 0; 0, -1] | .E => !![0, 1; 0, 0] | .Fm => !![0, 0; 1, 0]
      | .iH => !![Complex.I, 0; 0, -Complex.I] | .iE => !![0, Complex.I; 0, 0] | .iFm => !![0, 0; Complex.I, 0]
    let Y : Matrix (Fin 2) (Fin 2) ℂ := ((m⁻¹ : GL (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ) * X * (m : Matrix (Fin 2) (Fin 2) ℂ)
    HasDerivAt (fun s : ℝ => G (y * archComplexGLAt hw (m⁻¹ * archFlowMatrixComplex d s * m)))
      ((((Y 0 0 - Y 1 1) / 2).re : ℂ) * archDerivAtComplex hw ArchDirComplex.H G y +
        (((Y 0 0 - Y 1 1) / 2).im : ℂ) * archDerivAtComplex hw ArchDirComplex.iH G y +
        ((Y 0 1).re : ℂ) * archDerivAtComplex hw ArchDirComplex.E G y +
        ((Y 0 1).im : ℂ) * archDerivAtComplex hw ArchDirComplex.iE G y +
        ((Y 1 0).re : ℂ) * archDerivAtComplex hw ArchDirComplex.Fm G y +
        ((Y 1 0).im : ℂ) * archDerivAtComplex hw ArchDirComplex.iFm G y) 0 := by
  intro X Y
  have hX : X = XC d := by cases d <;> rfl
  set A : Matrix (Fin 2) (Fin 2) ℂ := ((m⁻¹ : GL (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ) with hA
  set B : Matrix (Fin 2) (Fin 2) ℂ := ((m : GL (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ) with hB
  have hBA : B * A = 1 := by rw [hA, hB, ← Units.val_mul, mul_inv_cancel, Units.val_one]
  have hAB : A * B = 1 := by rw [hA, hB, ← Units.val_mul, inv_mul_cancel, Units.val_one]
  set e : ℝ → (Fin 2 → Fin 2 → ℂ) := fun s =>
    Matrix.of.symm (A * (archFlowMatrixComplex d s : Matrix (Fin 2) (Fin 2) ℂ) * B) with he
  have hcurve : (fun s : ℝ => G (y * archComplexGLAt hw (m⁻¹ * archFlowMatrixComplex d s * m))) =
      (fun e' : Fin 2 → Fin 2 → ℂ => G (y * archComplexLiftAt hw e')) ∘ e := by
    funext s
    simp only [Function.comp, he]
    rw [show A * (archFlowMatrixComplex d s : Matrix (Fin 2) (Fin 2) ℂ) * B =
      ((m⁻¹ * archFlowMatrixComplex d s * m : GL (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ)
      by rw [hA, hB, Units.val_mul, Units.val_mul], archComplexLiftAt_coe K hw]
  have hderiv : HasDerivAt e (Matrix.of.symm (A * XC d * B)) 0 := by
    rw [hasDerivAt_pi]; intro i; rw [hasDerivAt_pi]; intro j
    simp only [he, Matrix.of_symm_apply, Matrix.mul_apply]
    refine HasDerivAt.fun_sum fun l _ => ?_
    exact (HasDerivAt.fun_sum fun k _ => (hasDerivAt_archFlowMatrixComplex_apply d k l).const_mul (A i k)).mul_const (B l j)
  have he0 : e 0 = Matrix.of.symm (1 : Matrix (Fin 2) (Fin 2) ℂ) := by
    simp only [he, archFlowMatrixComplex_zero, Units.val_one, mul_one, hAB]
  have hdet : (Matrix.of (Matrix.of.symm (1 : Matrix (Fin 2) (Fin 2) ℂ))).det ≠ 0 := by
    rw [Equiv.apply_symm_apply, Matrix.det_one]; exact one_ne_zero
  have hΦ : HasFDerivAt (fun e' : Fin 2 → Fin 2 → ℂ => G (y * archComplexLiftAt hw e'))
      (fderiv ℝ (fun e' : Fin 2 → Fin 2 → ℂ => G (y * archComplexLiftAt hw e')) (e 0)) (e 0) := by
    rw [he0]
    exact (((hG y).contDiffAt (isOpen_setOf_det_ne_zero_complex.mem_nhds hdet)).differentiableAt (by simp)).hasFDerivAt
  have hchain := hΦ.comp_hasDerivAt (x := (0 : ℝ)) hderiv
  rw [hcurve]
  refine hchain.congr_deriv ?_
  rw [he0, AutomorphicForm.fderiv_apply_mul_archComplexLiftAt_eq_of_isArchSmoothAtComplex K hw G hG y _ hdet]
  simp only [Equiv.apply_symm_apply, inv_one, one_mul, archComplexLiftAt_of_symm_one, mul_one]
  have htr : (A * XC d * B) 0 0 + (A * XC d * B) 1 1 = 0 := by
    rw [trace_conj A B _ hBA, trace_XC]
  have hY : Y = A * XC d * B := by rw [← hX]
  rw [← hY] at htr ⊢
  rw [htr]
  simp only [zero_div, Complex.zero_re, Complex.zero_im, Complex.ofReal_zero, zero_mul, add_zero]

end S_AutomorphicForm_hasDerivAt_apply_mul_archComplexGLAt_inv_mul_archFlowMatrixComplex_mul
end P2MW
export P2MW.S_AutomorphicForm_hasDerivAt_apply_mul_archComplexGLAt_inv_mul_archFlowMatrixComplex_mul (solution)
