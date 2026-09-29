-- Prove2me | solution 1 for AutomorphicForm.hasCircleWeightAt_archDelAt_archDelBarAt_archDerivAtComplex_of_hasCircleWeightAt_of_isArchSmoothAtComplex
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:05.340288+00:00
-- url     : https://prove2.me/submissions/17027d31-4fa8-5d70-b497-2e8531da617f

import Definitions.Def_AutomorphicForm_CuspidalConstituent
import Definitions.Def_AutomorphicForm_CanonicalTruncationDomain
import Definitions.Def_AutomorphicForm_ArchDerivCasimirComplex
import Definitions.Def_NumberField_PrincipalLevel
import Definitions.Def_NumberField_TateGlobalZeta
import Definitions.Def_NumberField_AdelicHaar
import Definitions.Def_AutomorphicForm_ArchDerivCasimirComplexAPI
import Mathlib
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AutomorphicForm_hasCircleWeightAt_archDelAt_archDelBarAt_archDerivAtComplex_of_hasCircleWeightAt_of_isArchSmoothAtComplex

set_option autoImplicit false

open MeasureTheory NumberField NumberField.AdelicLevel NumberField.AdelicBox NumberField.AdelicHaar
open AutomorphicForm AutomorphicForm.WindowedSiegel AutomorphicForm.SiegelCovering AutomorphicForm.CuspidalConstituent
open IsDedekindDomain NumberField.InfinitePlace NumberField.InfinitePlace.Completion
open scoped ComplexConjugate

attribute [local instance] NumberField.AdelicHaar.glBorel

noncomputable section

namespace K2C

open Matrix Complex

variable {K : Type} [Field K] [NumberField K] {w : InfinitePlace K} (hw : w.IsComplex)

def chartL (φ : AdelicGL2 (𝓞 K) K → ℂ) (g : AdelicGL2 (𝓞 K) K) : (Fin 2 → Fin 2 → ℂ) →L[ℝ] ℂ :=
  fderiv ℝ (fun e : Fin 2 → Fin 2 → ℂ => φ (g * archComplexLiftAt hw e)) (Matrix.of.symm (1 : Matrix (Fin 2) (Fin 2) ℂ))

theorem det_of_symm_one : (Matrix.of (Matrix.of.symm (1 : Matrix (Fin 2) (Fin 2) ℂ))).det ≠ 0 := by
  rw [Equiv.apply_symm_apply, Matrix.det_one]; exact one_ne_zero

theorem archComplexGLAt_eq_lift (u : GL (Fin 2) ℂ) :
    archComplexGLAt hw u = archComplexLiftAt hw (Matrix.of.symm (u : Matrix (Fin 2) (Fin 2) ℂ)) := by
  have h := archComplexLiftAt_mul_archComplexGLAt hw det_of_symm_one u
  rw [archComplexLiftAt_of_symm_one, one_mul, Equiv.apply_symm_apply, one_mul] at h
  exact h

theorem hasDerivAt_conj_flowMatrix (m : GL (Fin 2) ℂ) (d : ArchDirComplex) :
    HasDerivAt (fun t : ℝ => (Matrix.of.symm ((m : Matrix (Fin 2) (Fin 2) ℂ) * (archFlowMatrixComplex d t : Matrix (Fin 2) (Fin 2) ℂ) *
        ((m⁻¹ : GL (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ)) : Fin 2 → Fin 2 → ℂ))
      (Matrix.of.symm ((m : Matrix (Fin 2) (Fin 2) ℂ) * archDirMatrixComplex d * ((m⁻¹ : GL (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ))) 0 := by
  have h1 := hasDerivAt_of_symm_mul_archFlowMatrixComplex ((m : Matrix (Fin 2) (Fin 2) ℂ)) d
  rw [hasDerivAt_pi] at h1
  rw [hasDerivAt_pi]
  intro i
  rw [hasDerivAt_pi]
  intro j
  have h1i := h1 i
  rw [hasDerivAt_pi] at h1i
  simp only [Matrix.of_symm_apply, Matrix.mul_apply, Matrix.of_apply] at h1i ⊢
  exact HasDerivAt.fun_sum fun l _ => (h1i l).mul_const _

theorem hasDerivAt_conj_flow {φ : AdelicGL2 (𝓞 K) K → ℂ} (hφ : IsArchSmoothAtComplex hw φ) (g : AdelicGL2 (𝓞 K) K)
    (m : GL (Fin 2) ℂ) (d : ArchDirComplex) :
    HasDerivAt (fun t : ℝ => φ (g * archComplexGLAt hw m * archFlowAtComplex hw d t * archComplexGLAt hw m⁻¹))
      (chartL hw φ g (Matrix.of.symm ((m : Matrix (Fin 2) (Fin 2) ℂ) * archDirMatrixComplex d *
        ((m⁻¹ : GL (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ)))) 0 := by
  have hopen := isOpen_setOf_det_ne_zero_complex
  have hdiff : DifferentiableAt ℝ (fun e' : Fin 2 → Fin 2 → ℂ => φ (g * archComplexLiftAt hw e'))
      (Matrix.of.symm (1 : Matrix (Fin 2) (Fin 2) ℂ)) :=
    ((hφ g).contDiffAt (hopen.mem_nhds det_of_symm_one)).differentiableAt (by simp)
  have hfun : (fun t : ℝ => φ (g * archComplexGLAt hw m * archFlowAtComplex hw d t * archComplexGLAt hw m⁻¹)) =
      (fun e' : Fin 2 → Fin 2 → ℂ => φ (g * archComplexLiftAt hw e')) ∘
      (fun t : ℝ => (Matrix.of.symm ((m : Matrix (Fin 2) (Fin 2) ℂ) * (archFlowMatrixComplex d t : Matrix (Fin 2) (Fin 2) ℂ) *
        ((m⁻¹ : GL (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ)) : Fin 2 → Fin 2 → ℂ)) := by
    funext t
    simp only [Function.comp_apply]
    rw [mul_assoc g, mul_assoc g, archFlowAtComplex, ← map_mul, ← map_mul, archComplexGLAt_eq_lift]
    rfl
  have h0 : (Matrix.of.symm ((m : Matrix (Fin 2) (Fin 2) ℂ) * (archFlowMatrixComplex d 0 : Matrix (Fin 2) (Fin 2) ℂ) *
      ((m⁻¹ : GL (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ)) : Fin 2 → Fin 2 → ℂ) = Matrix.of.symm (1 : Matrix (Fin 2) (Fin 2) ℂ) := by
    rw [archFlowMatrixComplex_zero, Units.val_one, mul_one, ← Units.val_mul, mul_inv_cancel, Units.val_one]
  rw [hfun]
  refine HasFDerivAt.comp_hasDerivAt (x := (0 : ℝ)) ?_ (hasDerivAt_conj_flowMatrix m d)
  rw [h0]
  exact hdiff.hasFDerivAt

theorem archDerivAtComplex_eq_chartL {φ : AdelicGL2 (𝓞 K) K → ℂ} (hφ : IsArchSmoothAtComplex hw φ) (g : AdelicGL2 (𝓞 K) K)
    (d : ArchDirComplex) :
    archDerivAtComplex hw d φ g = chartL hw φ g (Matrix.of.symm (archDirMatrixComplex d)) := by
  have h := hasDerivAt_conj_flow hw hφ g 1 d
  simp only [map_one, inv_one, mul_one, Units.val_one, one_mul] at h
  exact h.deriv

theorem circle_inv_val (ζ : ℂˣ) : (((circleGL2 ζ)⁻¹ : GL (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ) = !![((ζ⁻¹ : ℂˣ) : ℂ), 0; 0, (ζ : ℂ)] := rfl

theorem conj_dir (ζ : ℂˣ) (X : ArchDirComplex) :
    (circleGL2 ζ : Matrix (Fin 2) (Fin 2) ℂ) * archDirMatrixComplex X * (((circleGL2 ζ)⁻¹ : GL (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ) =
      (match X with
        | .H => (1 : ℂ) | .iH => 1 | .E => (ζ : ℂ) ^ 2 | .iE => (ζ : ℂ) ^ 2
        | .Fm => ((ζ⁻¹ : ℂˣ) : ℂ) ^ 2 | .iFm => ((ζ⁻¹ : ℂˣ) : ℂ) ^ 2) • archDirMatrixComplex X := by
  rw [circle_inv_val]
  have hζ0 : (ζ : ℂ) ≠ 0 := ζ.ne_zero
  cases X <;>
  · ext i j
    fin_cases i <;> fin_cases j <;>
      (simp [circleGL2, archDirMatrixComplex, Matrix.mul_apply, Fin.sum_univ_two, Matrix.smul_apply,
          Units.val_inv_eq_inv_val]; try field_simp; try ring)

theorem of_symm_smul (c : ℂ) (M : Matrix (Fin 2) (Fin 2) ℂ) : Matrix.of.symm (c • M) = c • Matrix.of.symm M := rfl

theorem clm_complex_smul (L : (Fin 2 → Fin 2 → ℂ) →L[ℝ] ℂ) (z : ℂ) (M : Fin 2 → Fin 2 → ℂ) :
    L (z • M) = (z.re : ℂ) * L M + (z.im : ℂ) * L (Complex.I • M) := by
  have h : z • M = (z.re : ℝ) • M + (z.im : ℝ) • (Complex.I • M) := by
    funext i j
    simp only [Pi.smul_apply, Pi.add_apply, smul_eq_mul, Complex.real_smul]
    conv_lhs => rw [← Complex.re_add_im z]
    ring
  rw [h, map_add, map_smul, map_smul, Complex.real_smul, Complex.real_smul]

theorem I_smul_dir_E : (Complex.I • (Matrix.of.symm (archDirMatrixComplex .E)) : Fin 2 → Fin 2 → ℂ) = Matrix.of.symm (archDirMatrixComplex .iE) := by
  funext i j; fin_cases i <;> fin_cases j <;> simp [archDirMatrixComplex]
theorem I_smul_dir_iE : (Complex.I • (Matrix.of.symm (archDirMatrixComplex .iE)) : Fin 2 → Fin 2 → ℂ) = -Matrix.of.symm (archDirMatrixComplex .E) := by
  funext i j; fin_cases i <;> fin_cases j <;> simp [archDirMatrixComplex]
theorem I_smul_dir_Fm : (Complex.I • (Matrix.of.symm (archDirMatrixComplex .Fm)) : Fin 2 → Fin 2 → ℂ) = Matrix.of.symm (archDirMatrixComplex .iFm) := by
  funext i j; fin_cases i <;> fin_cases j <;> simp [archDirMatrixComplex]
theorem I_smul_dir_iFm : (Complex.I • (Matrix.of.symm (archDirMatrixComplex .iFm)) : Fin 2 → Fin 2 → ℂ) = -Matrix.of.symm (archDirMatrixComplex .Fm) := by
  funext i j; fin_cases i <;> fin_cases j <;> simp [archDirMatrixComplex]

theorem deriv_at_circle {ψ : AdelicGL2 (𝓞 K) K → ℂ} (hψ : IsArchSmoothAtComplex hw ψ) {n : ℤ} (hwt : HasCircleWeightAt hw n ψ)
    (ζ : ℂˣ) (hζ : ‖(ζ : ℂ)‖ = 1) (g : AdelicGL2 (𝓞 K) K) (X : ArchDirComplex) :
    archDerivAtComplex hw X ψ (g * archCircleAt hw ζ) =
      (ζ : ℂ) ^ n * chartL hw ψ g (Matrix.of.symm ((circleGL2 ζ : Matrix (Fin 2) (Fin 2) ℂ) * archDirMatrixComplex X *
        (((circleGL2 ζ)⁻¹ : GL (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ))) := by
  show deriv (fun t : ℝ => ψ (g * archCircleAt hw ζ * archFlowAtComplex hw X t)) 0 = _
  have hfun : (fun t : ℝ => ψ (g * archCircleAt hw ζ * archFlowAtComplex hw X t)) =
      fun t : ℝ => (ζ : ℂ) ^ n * ψ (g * archComplexGLAt hw (circleGL2 ζ) * archFlowAtComplex hw X t * archComplexGLAt hw (circleGL2 ζ)⁻¹) := by
    funext t
    rw [← hwt ζ hζ]
    show ψ (g * archComplexGLAt hw (circleGL2 ζ) * archFlowAtComplex hw X t) =
      ψ (g * archComplexGLAt hw (circleGL2 ζ) * archFlowAtComplex hw X t * archComplexGLAt hw (circleGL2 ζ)⁻¹ * archComplexGLAt hw (circleGL2 ζ))
    rw [map_inv, inv_mul_cancel_right]
  rw [hfun]
  exact ((hasDerivAt_conj_flow hw hψ g (circleGL2 ζ) X).const_mul ((ζ : ℂ) ^ n)).deriv

end K2C

open K2C in
theorem solution
    (K : Type) [Field K] [NumberField K]
    (w : InfinitePlace K) (hw : w.IsComplex) (n : ℤ)
    (ψ : AdelicGL2 (𝓞 K) K → ℂ) (hψ : IsArchSmoothAtComplex hw ψ)
    (hwt : HasCircleWeightAt hw n ψ) :
    HasCircleWeightAt hw (n + 2) (archDelAt hw .E ψ) ∧
      HasCircleWeightAt hw (n - 2) (archDelBarAt hw .E ψ) ∧
      HasCircleWeightAt hw (n - 2) (archDelAt hw .Fm ψ) ∧
      HasCircleWeightAt hw (n + 2) (archDelBarAt hw .Fm ψ) ∧
      HasCircleWeightAt hw n (archDerivAtComplex hw .H ψ) ∧
      HasCircleWeightAt hw n (archDerivAtComplex hw .iH ψ) := by
  have hD : ∀ (X : ArchDirComplex) (g : AdelicGL2 (𝓞 K) K),
      archDerivAtComplex hw X ψ g = K2C.chartL hw ψ g (Matrix.of.symm (archDirMatrixComplex X)) :=
    fun X g => K2C.archDerivAtComplex_eq_chartL hw hψ g X
  have hpow : ∀ (ζ : ℂˣ), (ζ : ℂ) ^ (n + 2) = (ζ : ℂ) ^ n * (ζ : ℂ) ^ 2 := fun ζ => by
    rw [zpow_add₀ ζ.ne_zero, zpow_two, pow_two]
  have hpow' : ∀ (ζ : ℂˣ), (ζ : ℂ) ^ (n - 2) = (ζ : ℂ) ^ n * ((ζ⁻¹ : ℂˣ) : ℂ) ^ 2 := fun ζ => by
    rw [zpow_sub₀ ζ.ne_zero, zpow_two, pow_two, Units.val_inv_eq_inv_val, div_eq_mul_inv, mul_inv]

  have hz : ∀ (ζ : ℂˣ), (((ζ : ℂ) ^ 2).re : ℂ) + (((ζ : ℂ) ^ 2).im : ℂ) * Complex.I = (ζ : ℂ) ^ 2 :=
    fun ζ => Complex.re_add_im _
  have hzi : ∀ (ζ : ℂˣ), ((((ζ⁻¹ : ℂˣ) : ℂ) ^ 2).re : ℂ) + ((((ζ⁻¹ : ℂˣ) : ℂ) ^ 2).im : ℂ) * Complex.I = ((ζ⁻¹ : ℂˣ) : ℂ) ^ 2 :=
    fun ζ => Complex.re_add_im _
  have hconj : ∀ (ζ : ℂˣ), ‖(ζ : ℂ)‖ = 1 → conj (ζ : ℂ) = ((ζ⁻¹ : ℂˣ) : ℂ) := fun ζ hζ => by
    rw [Units.val_inv_eq_inv_val, Complex.inv_def, Complex.normSq_eq_norm_sq, hζ]; simp
  have hzc : ∀ (ζ : ℂˣ), ‖(ζ : ℂ)‖ = 1 →
      (((ζ : ℂ) ^ 2).re : ℂ) - (((ζ : ℂ) ^ 2).im : ℂ) * Complex.I = ((ζ⁻¹ : ℂˣ) : ℂ) ^ 2 := fun ζ hζ => by
    rw [← hconj ζ hζ]
    refine Complex.ext_iff.2 ⟨?_, ?_⟩ <;>
      simp only [pow_two, Complex.sub_re, Complex.sub_im, Complex.mul_re, Complex.mul_im, Complex.ofReal_re,
        Complex.ofReal_im, Complex.I_re, Complex.I_im, Complex.conj_re, Complex.conj_im] <;> ring
  have hzc' : ∀ (ζ : ℂˣ), ‖(ζ : ℂ)‖ = 1 →
      ((((ζ⁻¹ : ℂˣ) : ℂ) ^ 2).re : ℂ) - ((((ζ⁻¹ : ℂˣ) : ℂ) ^ 2).im : ℂ) * Complex.I = (ζ : ℂ) ^ 2 := fun ζ hζ => by
    rw [← hconj ζ hζ]
    refine Complex.ext_iff.2 ⟨?_, ?_⟩ <;>
      simp only [pow_two, Complex.sub_re, Complex.sub_im, Complex.mul_re, Complex.mul_im, Complex.ofReal_re,
        Complex.ofReal_im, Complex.I_re, Complex.I_im, Complex.conj_re, Complex.conj_im] <;> ring
  refine ⟨fun ζ hζ g => ?_, fun ζ hζ g => ?_, fun ζ hζ g => ?_, fun ζ hζ g => ?_, fun ζ hζ g => ?_, fun ζ hζ g => ?_⟩
  ·
    simp only [archDelAt, ArchDir.toComplex, ArchDir.toComplexI, Pi.smul_apply, Pi.sub_apply, smul_eq_mul]
    rw [K2C.deriv_at_circle hw hψ hwt ζ hζ g .E, K2C.deriv_at_circle hw hψ hwt ζ hζ g .iE, K2C.conj_dir, K2C.conj_dir]
    simp only
    rw [K2C.of_symm_smul, K2C.of_symm_smul,
      K2C.clm_complex_smul _ ((ζ : ℂ) ^ 2) (Matrix.of.symm (archDirMatrixComplex .E)), K2C.I_smul_dir_E,
      K2C.clm_complex_smul _ ((ζ : ℂ) ^ 2) (Matrix.of.symm (archDirMatrixComplex .iE)), K2C.I_smul_dir_iE,
      map_neg, ← hD, ← hD, hpow]
    linear_combination ((ζ : ℂ) ^ n * (archDerivAtComplex hw .E ψ g - Complex.I * archDerivAtComplex hw .iE ψ g) / 2) * hz ζ +
      ((ζ : ℂ) ^ n * (((ζ : ℂ) ^ 2).im : ℂ) * archDerivAtComplex hw .iE ψ g / 2) * Complex.I_sq
  ·
    simp only [archDelBarAt, ArchDir.toComplex, ArchDir.toComplexI, Pi.smul_apply, Pi.add_apply, smul_eq_mul]
    rw [K2C.deriv_at_circle hw hψ hwt ζ hζ g .E, K2C.deriv_at_circle hw hψ hwt ζ hζ g .iE, K2C.conj_dir, K2C.conj_dir]
    simp only
    rw [K2C.of_symm_smul, K2C.of_symm_smul,
      K2C.clm_complex_smul _ ((ζ : ℂ) ^ 2) (Matrix.of.symm (archDirMatrixComplex .E)), K2C.I_smul_dir_E,
      K2C.clm_complex_smul _ ((ζ : ℂ) ^ 2) (Matrix.of.symm (archDirMatrixComplex .iE)), K2C.I_smul_dir_iE,
      map_neg, ← hD, ← hD, hpow']
    linear_combination ((ζ : ℂ) ^ n * (archDerivAtComplex hw .E ψ g + Complex.I * archDerivAtComplex hw .iE ψ g) / 2) * hzc ζ hζ +
      ((ζ : ℂ) ^ n * (((ζ : ℂ) ^ 2).im : ℂ) * archDerivAtComplex hw .iE ψ g / 2) * Complex.I_sq
  ·
    simp only [archDelAt, ArchDir.toComplex, ArchDir.toComplexI, Pi.smul_apply, Pi.sub_apply, smul_eq_mul]
    rw [K2C.deriv_at_circle hw hψ hwt ζ hζ g .Fm, K2C.deriv_at_circle hw hψ hwt ζ hζ g .iFm, K2C.conj_dir, K2C.conj_dir]
    simp only
    rw [K2C.of_symm_smul, K2C.of_symm_smul,
      K2C.clm_complex_smul _ (((ζ⁻¹ : ℂˣ) : ℂ) ^ 2) (Matrix.of.symm (archDirMatrixComplex .Fm)), K2C.I_smul_dir_Fm,
      K2C.clm_complex_smul _ (((ζ⁻¹ : ℂˣ) : ℂ) ^ 2) (Matrix.of.symm (archDirMatrixComplex .iFm)), K2C.I_smul_dir_iFm,
      map_neg, ← hD, ← hD, hpow']
    linear_combination ((ζ : ℂ) ^ n * (archDerivAtComplex hw .Fm ψ g - Complex.I * archDerivAtComplex hw .iFm ψ g) / 2) * hzi ζ +
      ((ζ : ℂ) ^ n * ((((ζ⁻¹ : ℂˣ) : ℂ) ^ 2).im : ℂ) * archDerivAtComplex hw .iFm ψ g / 2) * Complex.I_sq
  ·
    simp only [archDelBarAt, ArchDir.toComplex, ArchDir.toComplexI, Pi.smul_apply, Pi.add_apply, smul_eq_mul]
    rw [K2C.deriv_at_circle hw hψ hwt ζ hζ g .Fm, K2C.deriv_at_circle hw hψ hwt ζ hζ g .iFm, K2C.conj_dir, K2C.conj_dir]
    simp only
    rw [K2C.of_symm_smul, K2C.of_symm_smul,
      K2C.clm_complex_smul _ (((ζ⁻¹ : ℂˣ) : ℂ) ^ 2) (Matrix.of.symm (archDirMatrixComplex .Fm)), K2C.I_smul_dir_Fm,
      K2C.clm_complex_smul _ (((ζ⁻¹ : ℂˣ) : ℂ) ^ 2) (Matrix.of.symm (archDirMatrixComplex .iFm)), K2C.I_smul_dir_iFm,
      map_neg, ← hD, ← hD, hpow]
    linear_combination ((ζ : ℂ) ^ n * (archDerivAtComplex hw .Fm ψ g + Complex.I * archDerivAtComplex hw .iFm ψ g) / 2) * hzc' ζ hζ +
      ((ζ : ℂ) ^ n * ((((ζ⁻¹ : ℂˣ) : ℂ) ^ 2).im : ℂ) * archDerivAtComplex hw .iFm ψ g / 2) * Complex.I_sq
  ·
    rw [K2C.deriv_at_circle hw hψ hwt ζ hζ g .H, K2C.conj_dir]
    simp only [one_smul]
    rw [← hD]
  · rw [K2C.deriv_at_circle hw hψ hwt ζ hζ g .iH, K2C.conj_dir]
    simp only [one_smul]
    rw [← hD]

end
end S_AutomorphicForm_hasCircleWeightAt_archDelAt_archDelBarAt_archDerivAtComplex_of_hasCircleWeightAt_of_isArchSmoothAtComplex
end P2MW
export P2MW.S_AutomorphicForm_hasCircleWeightAt_archDelAt_archDelBarAt_archDerivAtComplex_of_hasCircleWeightAt_of_isArchSmoothAtComplex (solution)
