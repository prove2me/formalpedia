-- Prove2me | solution 1 for AutomorphicForm.archDerivAt_E_sub_archDerivAt_Fm_eq_smul_of_hasArchCharacterAt
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.553648+00:00
-- url     : https://prove2.me/submissions/a6d08f6f-8ea1-58ae-9275-ea40cc3b734e

import Definitions.Def_AutomorphicForm_ProductionPinsGeneral
import Definitions.Def_AutomorphicForm_CuspidalConstituent
import Definitions.Def_AutomorphicForm_ArchDerivCasimir
import Definitions.Def_AutomorphicForm_FactorizableTestFn
import Definitions.Def_AutomorphicForm_RightConvolution
import Definitions.Def_AutomorphicForm_ArchWeightCharTransport
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AutomorphicForm_archDerivAt_E_sub_archDerivAt_Fm_eq_smul_of_hasArchCharacterAt

set_option autoImplicit false

open NumberField NumberField.AdelicLevel NumberField.AdelicBox
open AutomorphicForm AutomorphicForm.WindowedSiegel AutomorphicForm.SiegelCovering IsDedekindDomain
open AutomorphicForm.CuspidalConstituent

noncomputable section

namespace OsInf17

open NumberField.InfinitePlace NumberField.InfinitePlace.Completion Matrix

variable {F : Type} [Field F] [NumberField F] {w : InfinitePlace F} (hw : w.IsReal)

private def rotMat (t : ℝ) : Matrix (Fin 2) (Fin 2) ℝ := !![Real.cos t, Real.sin t; -Real.sin t, Real.cos t]

omit hw in
private theorem det_rotMat (t : ℝ) : (rotMat t).det = 1 := by
  rw [rotMat, Matrix.det_fin_two_of]
  nlinarith [Real.cos_sq_add_sin_sq t]

private def rotGL (t : ℝ) : GL (Fin 2) ℝ :=
  Matrix.GeneralLinearGroup.mkOfDetNeZero (rotMat t) (by rw [det_rotMat]; exact one_ne_zero)

omit hw in
private theorem rotGL_coe (t : ℝ) : ((rotGL t : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) = rotMat t := rfl

omit hw in
private theorem rotGL_mem (t : ℝ) : rotGL t ∈ rowIsometrySubgroup₀ ℝ := by
  rw [mem_rowIsometrySubgroup₀_iff]
  refine ⟨det_rotMat t, ?_, ?_⟩
  · rw [rotGL_coe, det_rotMat, norm_one]
  · intro x y
    simp only [rotGL_coe, rotMat, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.empty_val', Matrix.cons_val_fin_one, Real.norm_eq_abs, sq_abs]
    linear_combination (x ^ 2 + y ^ 2) * Real.cos_sq_add_sin_sq t

private def rotSO (t : ℝ) : rowIsometrySubgroup₀ ℝ := ⟨rotGL t, rotGL_mem t⟩

omit hw in
private theorem archWeightOneℝ_rotSO (t : ℝ) : ((archWeightOneℝ (rotSO t) : ℂˣ) : ℂ) = Complex.exp (t * Complex.I) := by
  rw [Complex.exp_mul_I]
  show (⟨Real.cos t, Real.sin t⟩ : ℂ) = _
  apply Complex.ext <;> simp [Complex.cos_ofReal_re, Complex.sin_ofReal_re, Complex.cos_ofReal_im, Complex.sin_ofReal_im]

omit [NumberField F] hw in
private theorem norm_symm (hw : w.IsReal) (x : ℝ) : ‖(ringEquivRealOfIsReal hw).symm x‖ = ‖x‖ := by
  have := norm_ringEquivRealOfIsReal hw ((ringEquivRealOfIsReal hw).symm x)
  rw [RingEquiv.apply_symm_apply] at this
  exact this.symm

private def rotAt (t : ℝ) : rowIsometrySubgroup₀ w.Completion :=
  rowIsometrySubgroup₀Map (ringEquivRealOfIsReal hw).symm (norm_symm hw) (rotSO t)

private theorem rotAt_coe (t : ℝ) :
    ((rotAt hw t : rowIsometrySubgroup₀ w.Completion) : GL (Fin 2) w.Completion) =
      glEquivOfRingEquiv (ringEquivRealOfIsReal hw).symm (rotGL t) := rfl

private theorem adelicArchGLInclAt_rotAt (t : ℝ) :
    adelicArchGLInclAt F w ((rotAt hw t : rowIsometrySubgroup₀ w.Completion) : GL (Fin 2) w.Completion) =
      archRealGLAt hw (rotGL t) := rfl

private theorem archWeightCharAt_rotAt (n : ℤ) (t : ℝ) :
    ((archWeightCharAt hw n (rotAt hw t) : ℂˣ) : ℂ) = Complex.exp (Complex.I * n * t) := by
  have hmap : rowIsometrySubgroup₀Map (ringEquivRealOfIsReal hw) (norm_ringEquivRealOfIsReal hw) (rotAt hw t) = rotSO t := by
    apply Subtype.ext
    apply Units.ext
    ext i j
    show (ringEquivRealOfIsReal hw) ((ringEquivRealOfIsReal hw).symm (rotMat t i j)) = rotMat t i j
    exact RingEquiv.apply_symm_apply _ _
  simp only [archWeightCharAt, archWeightOneAt, MonoidHom.comp_apply, hmap, zpowGroupHom_apply, Units.val_zpow_eq_zpow_val,
    archWeightOneℝ_rotSO, ← Complex.exp_int_mul]
  congr 1
  ring

omit hw in
private theorem hasDerivAt_rotMat_entries :
    HasDerivAt (fun t : ℝ => Matrix.of.symm (rotMat t)) (Matrix.of.symm (archDirMatrix .E - archDirMatrix .Fm)) 0 := by
  rw [hasDerivAt_pi]
  intro i
  rw [hasDerivAt_pi]
  intro j
  fin_cases i <;> fin_cases j <;>
    simp only [Matrix.of_symm_apply, rotMat, archDirMatrix, Matrix.sub_apply, Matrix.of_apply, Matrix.cons_val',
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.empty_val', Matrix.cons_val_fin_one, Fin.zero_eta, Fin.mk_one, Fin.isValue,
      sub_zero, zero_sub]
  · simpa using Real.hasDerivAt_cos 0
  · simpa using Real.hasDerivAt_sin 0
  · have h__af := (Real.hasDerivAt_sin 0).neg
    simp at h__af
    exact h__af
  · simpa using Real.hasDerivAt_cos 0

omit hw in
private theorem rotMat_zero : rotMat 0 = 1 := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [rotMat]

private def chart (φ : AdelicGL2 (𝓞 F) F → ℂ) (g : AdelicGL2 (𝓞 F) F) : (Fin 2 → Fin 2 → ℝ) → ℂ :=
  fun e => φ (g * archRealLiftAt hw e)

private theorem archRealGLAt_eq_archRealLiftAt (M : GL (Fin 2) ℝ) :
    archRealGLAt hw M = archRealLiftAt hw (Matrix.of.symm (M : Matrix (Fin 2) (Fin 2) ℝ)) := by
  have hdet : (Matrix.of (Matrix.of.symm (M : Matrix (Fin 2) (Fin 2) ℝ))).det ≠ 0 := by
    rw [Equiv.apply_symm_apply]
    exact ((Matrix.isUnit_iff_isUnit_det _).1 M.isUnit).ne_zero
  rw [archRealLiftAt_of_det_ne_zero hw hdet]
  congr 1
  ext i j
  simp [GeneralLinearGroup.mkOfDetNeZero]

private theorem one_mem_U' : (Matrix.of (Matrix.of.symm (1 : Matrix (Fin 2) (Fin 2) ℝ))).det ≠ 0 := by
  rw [Equiv.apply_symm_apply, Matrix.det_one]; exact one_ne_zero

private theorem archDerivAt_eq_fderiv {φ : AdelicGL2 (𝓞 F) F → ℂ} (hφ : IsArchSmoothAt hw φ) (d : ArchDir) (g : AdelicGL2 (𝓞 F) F) :
    archDerivAt hw d φ g = fderiv ℝ (chart hw φ g) (Matrix.of.symm 1) (Matrix.of.symm (archDirMatrix d)) := by
  have hdiff : HasFDerivAt (chart hw φ g) (fderiv ℝ (chart hw φ g) (Matrix.of.symm 1))
      (Matrix.of.symm (Matrix.of (Matrix.of.symm (1 : Matrix (Fin 2) (Fin 2) ℝ)) * (archFlowMatrix d 0 : Matrix (Fin 2) (Fin 2) ℝ))) := by
    rw [of_symm_mul_archFlowMatrix_zero]
    exact (((hφ g).contDiffAt (isOpen_setOf_det_ne_zero.mem_nhds one_mem_U')).differentiableAt (by simp)).hasFDerivAt
  have hfun : (fun t : ℝ => φ (g * archFlowAt hw d t)) =
      fun t : ℝ => chart hw φ g (Matrix.of.symm (Matrix.of (Matrix.of.symm (1 : Matrix (Fin 2) (Fin 2) ℝ)) *
        (archFlowMatrix d t : Matrix (Fin 2) (Fin 2) ℝ))) := by
    funext t
    show _ = φ (g * archRealLiftAt hw _)
    rw [← archRealLiftAt_mul_archRealGLAt hw one_mem_U', archRealLiftAt_of_symm_one, one_mul, archFlowAt]
  show deriv (fun t : ℝ => φ (g * archFlowAt hw d t)) 0 = _
  rw [hfun]
  have h := (hdiff.comp_hasDerivAt (0 : ℝ) (hasDerivAt_of_symm_mul_archFlowMatrix _ d)).deriv
  simp only [Function.comp_def, Equiv.apply_symm_apply, Matrix.one_mul] at h ⊢
  exact h

private theorem main (n : ℤ) (y : AdelicGL2 (𝓞 F) F → ℂ) (hys : IsArchSmoothAt hw y)
    (hyn : HasArchCharacterAt₀ F w (archWeightCharAt hw n) y) :
    archDerivAt hw .E y - archDerivAt hw .Fm y = (Complex.I * n) • y := by
  funext g
  rw [Pi.sub_apply, Pi.smul_apply, smul_eq_mul, archDerivAt_eq_fderiv hw hys, archDerivAt_eq_fderiv hw hys]

  have hpath : ∀ t : ℝ, y (g * archRealGLAt hw (rotGL t)) = Complex.exp (Complex.I * n * t) * y g := by
    intro t
    rw [← adelicArchGLInclAt_rotAt hw, hyn (rotAt hw t) g, archWeightCharAt_rotAt]
  have hfun : (chart hw y g) ∘ (fun t : ℝ => Matrix.of.symm (rotMat t)) = fun t : ℝ => Complex.exp (Complex.I * n * t) * y g := by
    funext t
    show chart hw y g (Matrix.of.symm (rotMat t)) = _
    rw [← hpath t, archRealGLAt_eq_archRealLiftAt]
    rfl

  have hdiff : HasFDerivAt (chart hw y g) (fderiv ℝ (chart hw y g) (Matrix.of.symm 1)) (Matrix.of.symm (rotMat 0)) := by
    rw [rotMat_zero]
    exact (((hys g).contDiffAt (isOpen_setOf_det_ne_zero.mem_nhds (one_mem_U'))).differentiableAt (by simp)).hasFDerivAt
  have hL : HasDerivAt ((chart hw y g) ∘ (fun t : ℝ => Matrix.of.symm (rotMat t)))
      (fderiv ℝ (chart hw y g) (Matrix.of.symm 1) (Matrix.of.symm (archDirMatrix .E - archDirMatrix .Fm))) 0 :=
    hdiff.comp_hasDerivAt (0 : ℝ) hasDerivAt_rotMat_entries

  have hR : HasDerivAt (fun t : ℝ => Complex.exp (Complex.I * n * t) * y g) (Complex.I * n * y g) 0 := by
    have h1 : HasDerivAt (fun t : ℝ => Complex.I * n * (t : ℂ)) (Complex.I * n) 0 := by
      simpa using (Complex.ofRealCLM.hasDerivAt (x := (0 : ℝ))).const_mul (Complex.I * n)
    have h2 := (h1.cexp).mul_const (y g)
    simpa using h2
  rw [hfun] at hL
  have heq := hL.unique hR
  rw [← heq]
  show _ = (fderiv ℝ (chart hw y g) (Matrix.of.symm 1)) (Matrix.of.symm (archDirMatrix .E) - Matrix.of.symm (archDirMatrix .Fm))
  rw [map_sub]

end OsInf17

end

theorem solution
    (K : Type) [Field K] [NumberField K]
    (w : InfinitePlace K) (hw : w.IsReal) (n : ℤ)
    (y : AdelicGL2 (𝓞 K) K → ℂ) (hys : IsArchSmoothAt hw y)
    (hyn : HasArchCharacterAt₀ K w (archWeightCharAt hw n) y) :
    archDerivAt hw .E y - archDerivAt hw .Fm y = (Complex.I * n) • y :=
  OsInf17.main hw n y hys hyn

end S_AutomorphicForm_archDerivAt_E_sub_archDerivAt_Fm_eq_smul_of_hasArchCharacterAt
end P2MW
export P2MW.S_AutomorphicForm_archDerivAt_E_sub_archDerivAt_Fm_eq_smul_of_hasArchCharacterAt (solution)
