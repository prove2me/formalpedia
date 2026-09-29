-- Prove2me | solution 1 for AutomorphicForm.fderiv_apply_mul_archComplexLiftAt_eq_of_isArchSmoothAtComplex
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.961684+00:00
-- url     : https://prove2.me/submissions/c68c2839-a93c-5076-b49f-ec78e6ae65bc

import Definitions.Def_AutomorphicForm_ArchDerivCasimirComplex
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AutomorphicForm_fderiv_apply_mul_archComplexLiftAt_eq_of_isArchSmoothAtComplex

set_option autoImplicit false

open NumberField NumberField.InfinitePlace AutomorphicForm Matrix Complex

noncomputable section

namespace ArchChartTransportComplex

variable {F : Type} [Field F] [NumberField F] {w : InfinitePlace F}

def dirMatrix : ArchDirComplex → Matrix (Fin 2) (Fin 2) ℂ
  | .H => !![1, 0; 0, -1]
  | .E => !![0, 1; 0, 0]
  | .Fm => !![0, 0; 1, 0]
  | .iH => !![I, 0; 0, -I]
  | .iE => !![0, I; 0, 0]
  | .iFm => !![0, 0; I, 0]

theorem hasDerivAt_ofReal_zero : HasDerivAt (fun t : ℝ => (t : ℂ)) 1 0 := by
  simpa using (hasDerivAt_id (0 : ℝ)).ofReal_comp

theorem hasDerivAt_ofReal_mul_I_zero : HasDerivAt (fun t : ℝ => (t : ℂ) * I) I 0 := by
  simpa using hasDerivAt_ofReal_zero.mul_const I

theorem hasDerivAt_exp_ofReal_zero : HasDerivAt (fun t : ℝ => Complex.exp (t : ℂ)) 1 0 := by
  have h := (Complex.hasDerivAt_exp ((0 : ℝ) : ℂ)).comp (0 : ℝ) hasDerivAt_ofReal_zero
  simpa [Function.comp_def] using h

theorem hasDerivAt_exp_neg_ofReal_zero : HasDerivAt (fun t : ℝ => Complex.exp (-(t : ℂ))) (-1) 0 := by
  have h := (Complex.hasDerivAt_exp (-((0 : ℝ) : ℂ))).comp (0 : ℝ) hasDerivAt_ofReal_zero.neg
  simpa [Function.comp_def] using h

theorem hasDerivAt_exp_ofReal_mul_I_zero : HasDerivAt (fun t : ℝ => Complex.exp ((t : ℂ) * I)) I 0 := by
  have h := (Complex.hasDerivAt_exp (((0 : ℝ) : ℂ) * I)).comp (0 : ℝ) hasDerivAt_ofReal_mul_I_zero
  simpa [Function.comp_def] using h

theorem hasDerivAt_exp_neg_ofReal_mul_I_zero :
    HasDerivAt (fun t : ℝ => Complex.exp (-((t : ℂ) * I))) (-I) 0 := by
  have h := (Complex.hasDerivAt_exp (-(((0 : ℝ) : ℂ) * I))).comp (0 : ℝ) hasDerivAt_ofReal_mul_I_zero.neg
  simpa [Function.comp_def] using h

theorem hasDerivAt_archFlowMatrixComplex_apply (d : ArchDirComplex) (i j : Fin 2) :
    HasDerivAt (fun t : ℝ => (archFlowMatrixComplex d t : Matrix (Fin 2) (Fin 2) ℂ) i j) (dirMatrix d i j) 0 := by
  cases d <;> fin_cases i <;> fin_cases j <;>
    simp only [archFlowMatrixComplex, dirMatrix, splitTorusGL2Complex, unipotentGL2_coe, lowerUnipotentGL2_coe,
      Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.empty_val', Matrix.cons_val_fin_one, Fin.zero_eta, Fin.mk_one, Fin.isValue] <;>
    first
      | exact hasDerivAt_const _ _
      | exact hasDerivAt_ofReal_zero
      | exact hasDerivAt_ofReal_mul_I_zero
      | exact hasDerivAt_exp_ofReal_zero
      | exact hasDerivAt_exp_neg_ofReal_zero
      | exact hasDerivAt_exp_ofReal_mul_I_zero
      | exact hasDerivAt_exp_neg_ofReal_mul_I_zero

theorem hasDerivAt_of_symm_mul_archFlowMatrixComplex (e : Fin 2 → Fin 2 → ℂ) (d : ArchDirComplex) :
    HasDerivAt
      (fun t : ℝ => (Matrix.of.symm (Matrix.of e * (archFlowMatrixComplex d t : Matrix (Fin 2) (Fin 2) ℂ)) :
        Fin 2 → Fin 2 → ℂ))
      (Matrix.of.symm (Matrix.of e * dirMatrix d)) 0 := by
  rw [hasDerivAt_pi]
  intro i
  rw [hasDerivAt_pi]
  intro j
  simp only [Matrix.of_symm_apply, Matrix.mul_apply, Matrix.of_apply]
  exact HasDerivAt.fun_sum fun k _ => (hasDerivAt_archFlowMatrixComplex_apply d k j).const_mul (e i k)

def scalarExpGL2C (b : Bool) (s : ℝ) : GL (Fin 2) ℂ :=
  Units.map (Matrix.scalar (Fin 2) : ℂ →+* Matrix (Fin 2) (Fin 2) ℂ).toMonoidHom
    (Units.mk0 (Complex.exp (if b then (s : ℂ) * I else (s : ℂ))) (Complex.exp_ne_zero _))

theorem scalarExpGL2C_coe (b : Bool) (s : ℝ) :
    (scalarExpGL2C b s : Matrix (Fin 2) (Fin 2) ℂ) =
      Complex.exp (if b then (s : ℂ) * I else (s : ℂ)) • (1 : Matrix (Fin 2) (Fin 2) ℂ) := by
  simp [scalarExpGL2C, Matrix.smul_one_eq_diagonal]

def centralDir : Bool → Matrix (Fin 2) (Fin 2) ℂ
  | false => !![1, 0; 0, 1]
  | true => !![I, 0; 0, I]

theorem hasDerivAt_scalarExpGL2C_apply (b : Bool) (i j : Fin 2) :
    HasDerivAt (fun s : ℝ => (scalarExpGL2C b s : Matrix (Fin 2) (Fin 2) ℂ) i j) (centralDir b i j) 0 := by
  cases b <;> fin_cases i <;> fin_cases j <;>
    simp only [scalarExpGL2C_coe, centralDir, Matrix.smul_apply, smul_eq_mul, Matrix.one_apply_eq,
      Matrix.one_apply_ne, ne_eq, zero_ne_one, one_ne_zero, not_false_eq_true, mul_one, mul_zero,
      Bool.false_eq_true, if_false, if_true, Fin.zero_eta, Fin.mk_one, Fin.isValue,
      Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.empty_val', Matrix.cons_val_fin_one] <;>
    first
      | exact hasDerivAt_const _ _
      | exact hasDerivAt_exp_ofReal_zero
      | exact hasDerivAt_exp_ofReal_mul_I_zero

theorem hasDerivAt_of_symm_mul_scalarExpGL2C (e : Fin 2 → Fin 2 → ℂ) (b : Bool) :
    HasDerivAt
      (fun s : ℝ => (Matrix.of.symm (Matrix.of e * (scalarExpGL2C b s : Matrix (Fin 2) (Fin 2) ℂ)) :
        Fin 2 → Fin 2 → ℂ))
      (Matrix.of.symm (Matrix.of e * centralDir b)) 0 := by
  rw [hasDerivAt_pi]
  intro i
  rw [hasDerivAt_pi]
  intro j
  simp only [Matrix.of_symm_apply, Matrix.mul_apply, Matrix.of_apply]
  exact HasDerivAt.fun_sum fun k _ => (hasDerivAt_scalarExpGL2C_apply b k j).const_mul (e i k)

theorem archComplexLiftAt_mul_archComplexGLAt (hw : w.IsComplex) {e : Fin 2 → Fin 2 → ℂ}
    (h : (Matrix.of e).det ≠ 0) (m : GL (Fin 2) ℂ) :
    archComplexLiftAt hw e * archComplexGLAt hw m =
      archComplexLiftAt hw (Matrix.of.symm (Matrix.of e * (m : Matrix (Fin 2) (Fin 2) ℂ))) := by
  have hm : ((m : Matrix (Fin 2) (Fin 2) ℂ)).det ≠ 0 :=
    ((Matrix.isUnit_iff_isUnit_det _).1 m.isUnit).ne_zero
  have h' : (Matrix.of (Matrix.of.symm (Matrix.of e * (m : Matrix (Fin 2) (Fin 2) ℂ)))).det ≠ 0 := by
    rw [Equiv.apply_symm_apply, Matrix.det_mul]
    exact mul_ne_zero h hm
  rw [archComplexLiftAt_of_det_ne_zero hw h, archComplexLiftAt_of_det_ne_zero hw h', ← map_mul]
  congr 1
  ext i j
  simp [GeneralLinearGroup.mkOfDetNeZero]

theorem det_of_symm_one : (Matrix.of (Matrix.of.symm (1 : Matrix (Fin 2) (Fin 2) ℂ))).det ≠ 0 := by
  rw [Equiv.apply_symm_apply, Matrix.det_one]
  exact one_ne_zero

theorem archComplexLiftAt_of_symm_one (hw : w.IsComplex) :
    archComplexLiftAt hw (Matrix.of.symm (1 : Matrix (Fin 2) (Fin 2) ℂ)) = 1 := by
  rw [archComplexLiftAt_of_det_ne_zero hw det_of_symm_one, ← map_one (archComplexGLAt hw)]
  congr 1
  ext i j
  simp [GeneralLinearGroup.mkOfDetNeZero]

theorem decompose (A : Matrix (Fin 2) (Fin 2) ℂ) :
    (Matrix.of.symm A : Fin 2 → Fin 2 → ℂ) =
      ((A 0 0 - A 1 1) / 2).re • (Matrix.of.symm (dirMatrix ArchDirComplex.H) : Fin 2 → Fin 2 → ℂ) +
      ((A 0 0 - A 1 1) / 2).im • (Matrix.of.symm (dirMatrix ArchDirComplex.iH) : Fin 2 → Fin 2 → ℂ) +
      (A 0 1).re • (Matrix.of.symm (dirMatrix ArchDirComplex.E) : Fin 2 → Fin 2 → ℂ) +
      (A 0 1).im • (Matrix.of.symm (dirMatrix ArchDirComplex.iE) : Fin 2 → Fin 2 → ℂ) +
      (A 1 0).re • (Matrix.of.symm (dirMatrix ArchDirComplex.Fm) : Fin 2 → Fin 2 → ℂ) +
      (A 1 0).im • (Matrix.of.symm (dirMatrix ArchDirComplex.iFm) : Fin 2 → Fin 2 → ℂ) +
      ((A 0 0 + A 1 1) / 2).re • (Matrix.of.symm (centralDir false) : Fin 2 → Fin 2 → ℂ) +
      ((A 0 0 + A 1 1) / 2).im • (Matrix.of.symm (centralDir true) : Fin 2 → Fin 2 → ℂ) := by
  funext i j
  fin_cases i <;> fin_cases j <;>
    simp [dirMatrix, centralDir] <;> apply Complex.ext <;> simp <;> ring

variable (hw : w.IsComplex)

theorem archDerivAtComplex_eq_fderiv (φ : AdelicGL2 (𝓞 F) F → ℂ) (hφ : IsArchSmoothAtComplex hw φ)
    (h : AdelicGL2 (𝓞 F) F) (d : ArchDirComplex) :
    archDerivAtComplex hw d φ h =
      fderiv ℝ (fun e'' : Fin 2 → Fin 2 → ℂ => φ (h * archComplexLiftAt hw e''))
        (Matrix.of.symm (1 : Matrix (Fin 2) (Fin 2) ℂ)) (Matrix.of.symm (dirMatrix d)) := by
  have hopen := isOpen_setOf_det_ne_zero_complex
  have h0 : (Matrix.of.symm (Matrix.of (Matrix.of.symm (1 : Matrix (Fin 2) (Fin 2) ℂ)) *
        (archFlowMatrixComplex d 0 : Matrix (Fin 2) (Fin 2) ℂ)) : Fin 2 → Fin 2 → ℂ) =
      Matrix.of.symm (1 : Matrix (Fin 2) (Fin 2) ℂ) := by
    rw [archFlowMatrixComplex_zero, Units.val_one, mul_one, Equiv.symm_apply_apply]
  have hdiff : HasFDerivAt (fun e' => φ (h * archComplexLiftAt hw e'))
      (fderiv ℝ (fun e' => φ (h * archComplexLiftAt hw e')) (Matrix.of.symm (1 : Matrix (Fin 2) (Fin 2) ℂ)))
      (Matrix.of.symm (Matrix.of (Matrix.of.symm (1 : Matrix (Fin 2) (Fin 2) ℂ)) *
        (archFlowMatrixComplex d 0 : Matrix (Fin 2) (Fin 2) ℂ))) := by
    rw [h0]
    exact (((hφ h).contDiffAt (hopen.mem_nhds det_of_symm_one)).differentiableAt (by simp)).hasFDerivAt
  have hfun : (fun t : ℝ => φ (h * archFlowAtComplex hw d t)) =
      fun t : ℝ => φ (h * archComplexLiftAt hw
        (Matrix.of.symm (Matrix.of (Matrix.of.symm (1 : Matrix (Fin 2) (Fin 2) ℂ)) *
          (archFlowMatrixComplex d t : Matrix (Fin 2) (Fin 2) ℂ)))) := by
    funext t
    rw [← archComplexLiftAt_mul_archComplexGLAt hw det_of_symm_one, archComplexLiftAt_of_symm_one, one_mul,
      archFlowAtComplex]
  show deriv (fun t : ℝ => φ (h * archFlowAtComplex hw d t)) 0 = _
  rw [hfun]
  have := (hdiff.comp_hasDerivAt (0 : ℝ) (hasDerivAt_of_symm_mul_archFlowMatrixComplex _ d)).deriv
  simpa only [Function.comp_def, Equiv.apply_symm_apply, one_mul] using this

theorem deriv_scalar_eq_fderiv (φ : AdelicGL2 (𝓞 F) F → ℂ) (hφ : IsArchSmoothAtComplex hw φ)
    (h : AdelicGL2 (𝓞 F) F) (b : Bool) :
    deriv (fun s : ℝ => φ (h * archComplexGLAt hw (scalarExpGL2C b s))) 0 =
      fderiv ℝ (fun e'' : Fin 2 → Fin 2 → ℂ => φ (h * archComplexLiftAt hw e''))
        (Matrix.of.symm (1 : Matrix (Fin 2) (Fin 2) ℂ)) (Matrix.of.symm (centralDir b)) := by
  have hopen := isOpen_setOf_det_ne_zero_complex
  have h0 : (Matrix.of.symm (Matrix.of (Matrix.of.symm (1 : Matrix (Fin 2) (Fin 2) ℂ)) *
        (scalarExpGL2C b 0 : Matrix (Fin 2) (Fin 2) ℂ)) : Fin 2 → Fin 2 → ℂ) =
      Matrix.of.symm (1 : Matrix (Fin 2) (Fin 2) ℂ) := by
    rw [Equiv.apply_symm_apply, one_mul, scalarExpGL2C_coe]
    cases b <;> simp
  have hdiff : HasFDerivAt (fun e' => φ (h * archComplexLiftAt hw e'))
      (fderiv ℝ (fun e' => φ (h * archComplexLiftAt hw e')) (Matrix.of.symm (1 : Matrix (Fin 2) (Fin 2) ℂ)))
      (Matrix.of.symm (Matrix.of (Matrix.of.symm (1 : Matrix (Fin 2) (Fin 2) ℂ)) *
        (scalarExpGL2C b 0 : Matrix (Fin 2) (Fin 2) ℂ))) := by
    rw [h0]
    exact (((hφ h).contDiffAt (hopen.mem_nhds det_of_symm_one)).differentiableAt (by simp)).hasFDerivAt
  have hfun : (fun s : ℝ => φ (h * archComplexGLAt hw (scalarExpGL2C b s))) =
      fun s : ℝ => φ (h * archComplexLiftAt hw
        (Matrix.of.symm (Matrix.of (Matrix.of.symm (1 : Matrix (Fin 2) (Fin 2) ℂ)) *
          (scalarExpGL2C b s : Matrix (Fin 2) (Fin 2) ℂ)))) := by
    funext s
    rw [← archComplexLiftAt_mul_archComplexGLAt hw det_of_symm_one, archComplexLiftAt_of_symm_one, one_mul]
  rw [hfun]
  have := (hdiff.comp_hasDerivAt (0 : ℝ) (hasDerivAt_of_symm_mul_scalarExpGL2C _ b)).deriv
  simpa only [Function.comp_def, Equiv.apply_symm_apply, one_mul] using this

theorem fderiv_baseChange (φ : AdelicGL2 (𝓞 F) F → ℂ) (hφ : IsArchSmoothAtComplex hw φ)
    (g : AdelicGL2 (𝓞 F) F) (e : Fin 2 → Fin 2 → ℂ) (he : (Matrix.of e).det ≠ 0) (Y : Fin 2 → Fin 2 → ℂ) :
    fderiv ℝ (fun e' : Fin 2 → Fin 2 → ℂ => φ (g * archComplexLiftAt hw e')) e Y =
      fderiv ℝ (fun e'' : Fin 2 → Fin 2 → ℂ => φ (g * archComplexLiftAt hw e * archComplexLiftAt hw e''))
        (Matrix.of.symm (1 : Matrix (Fin 2) (Fin 2) ℂ)) (Matrix.of.symm ((Matrix.of e)⁻¹ * Matrix.of Y)) := by
  have hopen := isOpen_setOf_det_ne_zero_complex
  let L : (Fin 2 → Fin 2 → ℂ) →L[ℝ] (Fin 2 → Fin 2 → ℂ) :=
    LinearMap.toContinuousLinearMap
      { toFun := fun e' => Matrix.of.symm ((Matrix.of e)⁻¹ * Matrix.of e')
        map_add' := fun x y => by
          change (Matrix.of.symm ((Matrix.of e)⁻¹ * (Matrix.of x + Matrix.of y)) : Fin 2 → Fin 2 → ℂ) = _
          rw [Matrix.mul_add]
          rfl
        map_smul' := fun c x => by
          change (Matrix.of.symm ((Matrix.of e)⁻¹ * (c • Matrix.of x)) : Fin 2 → Fin 2 → ℂ) = _
          rw [Matrix.mul_smul]
          rfl }
  have hL : ∀ e', L e' = Matrix.of.symm ((Matrix.of e)⁻¹ * Matrix.of e') := fun _ => rfl
  have hLe : L e = Matrix.of.symm (1 : Matrix (Fin 2) (Fin 2) ℂ) := by
    rw [hL, Matrix.nonsing_inv_mul _ (isUnit_iff_ne_zero.2 he)]
  set ψ : (Fin 2 → Fin 2 → ℂ) → ℂ := fun e'' => φ (g * archComplexLiftAt hw e * archComplexLiftAt hw e'') with hψ
  have hψs : ContDiffOn ℝ (⊤ : ℕ∞) ψ {e'' | (Matrix.of e'').det ≠ 0} := hφ (g * archComplexLiftAt hw e)
  have hfeq : ∀ e' : Fin 2 → Fin 2 → ℂ, (Matrix.of e').det ≠ 0 →
      φ (g * archComplexLiftAt hw e') = ψ (L e') := by
    intro e' he'
    have hdetL : ((Matrix.of e)⁻¹ * Matrix.of e').det ≠ 0 := by
      rw [Matrix.det_mul]
      exact mul_ne_zero (Matrix.isUnit_nonsing_inv_det _ (isUnit_iff_ne_zero.2 he)).ne_zero he'
    have hmul : archComplexLiftAt hw e * archComplexGLAt hw (Matrix.GeneralLinearGroup.mkOfDetNeZero _ hdetL) =
        archComplexLiftAt hw (Matrix.of.symm (Matrix.of e * ((Matrix.of e)⁻¹ * Matrix.of e'))) := by
      rw [archComplexLiftAt_mul_archComplexGLAt hw he]
      rfl
    have hcancel : Matrix.of e * ((Matrix.of e)⁻¹ * Matrix.of e') = Matrix.of e' := by
      rw [← Matrix.mul_assoc, Matrix.mul_nonsing_inv _ (isUnit_iff_ne_zero.2 he), Matrix.one_mul]
    rw [hψ, hL]
    show φ (g * archComplexLiftAt hw e') =
      φ (g * archComplexLiftAt hw e * archComplexLiftAt hw (Matrix.of.symm ((Matrix.of e)⁻¹ * Matrix.of e')))
    rw [archComplexLiftAt_of_det_ne_zero hw (e := Matrix.of.symm ((Matrix.of e)⁻¹ * Matrix.of e'))
      (by rw [Equiv.apply_symm_apply]; exact hdetL)]
    simp only [Equiv.apply_symm_apply]
    rw [mul_assoc, hmul, hcancel, Equiv.symm_apply_apply]
  have hψd : DifferentiableAt ℝ ψ (L e) := by
    rw [hLe]
    exact ((hψs).contDiffAt (hopen.mem_nhds det_of_symm_one)).differentiableAt (by simp)
  have hcomp : HasFDerivAt (fun e' => ψ (L e')) ((fderiv ℝ ψ (L e)).comp L) e :=
    hψd.hasFDerivAt.comp e L.hasFDerivAt
  have hcongr : (fun e' => φ (g * archComplexLiftAt hw e')) =ᶠ[nhds e] fun e' => ψ (L e') := by
    filter_upwards [hopen.mem_nhds he] with e' he'
    exact hfeq e' he'
  rw [(hcomp.congr_of_eventuallyEq hcongr).fderiv, ContinuousLinearMap.comp_apply, hLe, hL]

theorem main (φ : AdelicGL2 (𝓞 F) F → ℂ) (hφ : IsArchSmoothAtComplex hw φ)
    (g : AdelicGL2 (𝓞 F) F) (e : Fin 2 → Fin 2 → ℂ) (he : (Matrix.of e).det ≠ 0) (Y : Fin 2 → Fin 2 → ℂ) :
    fderiv ℝ (fun e' : Fin 2 → Fin 2 → ℂ => φ (g * archComplexLiftAt hw e')) e Y =
      ((((Matrix.of e)⁻¹ * Matrix.of Y) 0 0 - ((Matrix.of e)⁻¹ * Matrix.of Y) 1 1) / 2).re *
          archDerivAtComplex hw ArchDirComplex.H φ (g * archComplexLiftAt hw e) +
      ((((Matrix.of e)⁻¹ * Matrix.of Y) 0 0 - ((Matrix.of e)⁻¹ * Matrix.of Y) 1 1) / 2).im *
          archDerivAtComplex hw ArchDirComplex.iH φ (g * archComplexLiftAt hw e) +
      (((Matrix.of e)⁻¹ * Matrix.of Y) 0 1).re * archDerivAtComplex hw ArchDirComplex.E φ (g * archComplexLiftAt hw e) +
      (((Matrix.of e)⁻¹ * Matrix.of Y) 0 1).im * archDerivAtComplex hw ArchDirComplex.iE φ (g * archComplexLiftAt hw e) +
      (((Matrix.of e)⁻¹ * Matrix.of Y) 1 0).re * archDerivAtComplex hw ArchDirComplex.Fm φ (g * archComplexLiftAt hw e) +
      (((Matrix.of e)⁻¹ * Matrix.of Y) 1 0).im * archDerivAtComplex hw ArchDirComplex.iFm φ (g * archComplexLiftAt hw e) +
      ((((Matrix.of e)⁻¹ * Matrix.of Y) 0 0 + ((Matrix.of e)⁻¹ * Matrix.of Y) 1 1) / 2).re *
          deriv (fun s : ℝ => φ (g * archComplexLiftAt hw e *
            archComplexGLAt hw (Units.map (Matrix.scalar (Fin 2) : ℂ →+* Matrix (Fin 2) (Fin 2) ℂ).toMonoidHom
              (Units.mk0 (Complex.exp (s : ℂ)) (Complex.exp_ne_zero _))))) 0 +
      ((((Matrix.of e)⁻¹ * Matrix.of Y) 0 0 + ((Matrix.of e)⁻¹ * Matrix.of Y) 1 1) / 2).im *
          deriv (fun s : ℝ => φ (g * archComplexLiftAt hw e *
            archComplexGLAt hw (Units.map (Matrix.scalar (Fin 2) : ℂ →+* Matrix (Fin 2) (Fin 2) ℂ).toMonoidHom
              (Units.mk0 (Complex.exp ((s : ℂ) * I)) (Complex.exp_ne_zero _))))) 0 := by
  set A : Matrix (Fin 2) (Fin 2) ℂ := (Matrix.of e)⁻¹ * Matrix.of Y with hA
  set h : AdelicGL2 (𝓞 F) F := g * archComplexLiftAt hw e with hh
  rw [fderiv_baseChange hw φ hφ g e he Y, ← hA, decompose A]
  have hfalse : (fun s : ℝ => φ (h * archComplexGLAt hw (Units.map (Matrix.scalar (Fin 2) : ℂ →+* Matrix (Fin 2) (Fin 2) ℂ).toMonoidHom
      (Units.mk0 (Complex.exp (s : ℂ)) (Complex.exp_ne_zero _))))) =
      fun s : ℝ => φ (h * archComplexGLAt hw (scalarExpGL2C false s)) := by
    funext s; simp [scalarExpGL2C]
  have htrue : (fun s : ℝ => φ (h * archComplexGLAt hw (Units.map (Matrix.scalar (Fin 2) : ℂ →+* Matrix (Fin 2) (Fin 2) ℂ).toMonoidHom
      (Units.mk0 (Complex.exp ((s : ℂ) * I)) (Complex.exp_ne_zero _))))) =
      fun s : ℝ => φ (h * archComplexGLAt hw (scalarExpGL2C true s)) := by
    funext s; simp [scalarExpGL2C]
  rw [hfalse, htrue]
  rw [map_add, map_add, map_add, map_add, map_add, map_add, map_add,
    map_smul, map_smul, map_smul, map_smul, map_smul, map_smul, map_smul, map_smul,
    ← archDerivAtComplex_eq_fderiv hw φ hφ h ArchDirComplex.H, ← archDerivAtComplex_eq_fderiv hw φ hφ h ArchDirComplex.iH,
    ← archDerivAtComplex_eq_fderiv hw φ hφ h ArchDirComplex.E, ← archDerivAtComplex_eq_fderiv hw φ hφ h ArchDirComplex.iE,
    ← archDerivAtComplex_eq_fderiv hw φ hφ h ArchDirComplex.Fm, ← archDerivAtComplex_eq_fderiv hw φ hφ h ArchDirComplex.iFm,
    ← deriv_scalar_eq_fderiv hw φ hφ h false, ← deriv_scalar_eq_fderiv hw φ hφ h true]
  simp only [Complex.real_smul]

end ArchChartTransportComplex

end

open ArchChartTransportComplex in
theorem solution
    (F : Type) [Field F] [NumberField F] {w : InfinitePlace F} (hw : w.IsComplex)
    (φ : AdelicGL2 (𝓞 F) F → ℂ) (hφ : IsArchSmoothAtComplex hw φ)
    (g : AdelicGL2 (𝓞 F) F) (e : Fin 2 → Fin 2 → ℂ) (he : (Matrix.of e).det ≠ 0) (Y : Fin 2 → Fin 2 → ℂ) :
    fderiv ℝ (fun e' : Fin 2 → Fin 2 → ℂ => φ (g * archComplexLiftAt hw e')) e Y =
      ((((Matrix.of e)⁻¹ * Matrix.of Y) 0 0 - ((Matrix.of e)⁻¹ * Matrix.of Y) 1 1) / 2).re *
          archDerivAtComplex hw ArchDirComplex.H φ (g * archComplexLiftAt hw e) +
      ((((Matrix.of e)⁻¹ * Matrix.of Y) 0 0 - ((Matrix.of e)⁻¹ * Matrix.of Y) 1 1) / 2).im *
          archDerivAtComplex hw ArchDirComplex.iH φ (g * archComplexLiftAt hw e) +
      (((Matrix.of e)⁻¹ * Matrix.of Y) 0 1).re * archDerivAtComplex hw ArchDirComplex.E φ (g * archComplexLiftAt hw e) +
      (((Matrix.of e)⁻¹ * Matrix.of Y) 0 1).im * archDerivAtComplex hw ArchDirComplex.iE φ (g * archComplexLiftAt hw e) +
      (((Matrix.of e)⁻¹ * Matrix.of Y) 1 0).re * archDerivAtComplex hw ArchDirComplex.Fm φ (g * archComplexLiftAt hw e) +
      (((Matrix.of e)⁻¹ * Matrix.of Y) 1 0).im * archDerivAtComplex hw ArchDirComplex.iFm φ (g * archComplexLiftAt hw e) +
      ((((Matrix.of e)⁻¹ * Matrix.of Y) 0 0 + ((Matrix.of e)⁻¹ * Matrix.of Y) 1 1) / 2).re *
          deriv (fun s : ℝ => φ (g * archComplexLiftAt hw e *
            archComplexGLAt hw (Units.map (Matrix.scalar (Fin 2) : ℂ →+* Matrix (Fin 2) (Fin 2) ℂ).toMonoidHom
              (Units.mk0 (Complex.exp (s : ℂ)) (Complex.exp_ne_zero _))))) 0 +
      ((((Matrix.of e)⁻¹ * Matrix.of Y) 0 0 + ((Matrix.of e)⁻¹ * Matrix.of Y) 1 1) / 2).im *
          deriv (fun s : ℝ => φ (g * archComplexLiftAt hw e *
            archComplexGLAt hw (Units.map (Matrix.scalar (Fin 2) : ℂ →+* Matrix (Fin 2) (Fin 2) ℂ).toMonoidHom
              (Units.mk0 (Complex.exp ((s : ℂ) * I)) (Complex.exp_ne_zero _))))) 0 :=
  ArchChartTransportComplex.main hw φ hφ g e he Y

end S_AutomorphicForm_fderiv_apply_mul_archComplexLiftAt_eq_of_isArchSmoothAtComplex
end P2MW
export P2MW.S_AutomorphicForm_fderiv_apply_mul_archComplexLiftAt_eq_of_isArchSmoothAtComplex (solution)
