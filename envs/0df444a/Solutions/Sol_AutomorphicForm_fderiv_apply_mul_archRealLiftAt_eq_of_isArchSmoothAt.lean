-- Prove2me | solution 1 for AutomorphicForm.fderiv_apply_mul_archRealLiftAt_eq_of_isArchSmoothAt
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.961684+00:00
-- url     : https://prove2.me/submissions/0e489837-fbd1-51ab-8ff6-d5d8d0523aee

import Definitions.Def_AutomorphicForm_ArchDerivCasimir
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AutomorphicForm_fderiv_apply_mul_archRealLiftAt_eq_of_isArchSmoothAt

set_option autoImplicit false

open NumberField NumberField.InfinitePlace AutomorphicForm Matrix

noncomputable section

namespace ArchChartTransport

variable {F : Type} [Field F] [NumberField F] {w : InfinitePlace F}

def scalarExpGL2 (s : ℝ) : GL (Fin 2) ℝ :=
  Units.map (Matrix.scalar (Fin 2) : ℝ →+* Matrix (Fin 2) (Fin 2) ℝ).toMonoidHom
    (Units.mk0 (Real.exp s) (Real.exp_ne_zero s))

theorem scalarExpGL2_coe (s : ℝ) :
    (scalarExpGL2 s : Matrix (Fin 2) (Fin 2) ℝ) = Real.exp s • (1 : Matrix (Fin 2) (Fin 2) ℝ) := by
  simp [scalarExpGL2, Matrix.smul_one_eq_diagonal]

theorem hasDerivAt_scalarExpGL2_apply (i j : Fin 2) :
    HasDerivAt (fun s : ℝ => (scalarExpGL2 s : Matrix (Fin 2) (Fin 2) ℝ) i j)
      ((1 : Matrix (Fin 2) (Fin 2) ℝ) i j) 0 := by
  simp only [scalarExpGL2_coe, Matrix.smul_apply, smul_eq_mul]
  have h := (Real.hasDerivAt_exp 0).mul_const ((1 : Matrix (Fin 2) (Fin 2) ℝ) i j)
  simpa using h

theorem hasDerivAt_of_symm_mul_scalarExpGL2 (e : Fin 2 → Fin 2 → ℝ) :
    HasDerivAt
      (fun s : ℝ => (Matrix.of.symm (Matrix.of e * (scalarExpGL2 s : Matrix (Fin 2) (Fin 2) ℝ)) :
        Fin 2 → Fin 2 → ℝ))
      (Matrix.of.symm (Matrix.of e * (1 : Matrix (Fin 2) (Fin 2) ℝ))) 0 := by
  rw [hasDerivAt_pi]
  intro i
  rw [hasDerivAt_pi]
  intro j
  simp only [Matrix.of_symm_apply, Matrix.mul_apply, Matrix.of_apply]
  exact HasDerivAt.fun_sum fun k _ => (hasDerivAt_scalarExpGL2_apply k j).const_mul (e i k)

theorem decompose (A : Matrix (Fin 2) (Fin 2) ℝ) :
    (Matrix.of.symm A : Fin 2 → Fin 2 → ℝ) =
      ((A 0 0 - A 1 1) / 2) • (Matrix.of.symm (archDirMatrix ArchDir.H) : Fin 2 → Fin 2 → ℝ) +
      (A 0 1) • (Matrix.of.symm (archDirMatrix ArchDir.E) : Fin 2 → Fin 2 → ℝ) +
      (A 1 0) • (Matrix.of.symm (archDirMatrix ArchDir.Fm) : Fin 2 → Fin 2 → ℝ) +
      ((A 0 0 + A 1 1) / 2) • (Matrix.of.symm (1 : Matrix (Fin 2) (Fin 2) ℝ) : Fin 2 → Fin 2 → ℝ) := by
  funext i j
  fin_cases i <;> fin_cases j <;>
    simp [archDirMatrix] <;> ring

variable (hw : w.IsReal)

theorem archDerivAt_eq_fderiv (φ : AdelicGL2 (𝓞 F) F → ℂ) (hφ : IsArchSmoothAt hw φ)
    (h : AdelicGL2 (𝓞 F) F) (d : ArchDir) :
    archDerivAt hw d φ h =
      fderiv ℝ (fun e'' : Fin 2 → Fin 2 → ℝ => φ (h * archRealLiftAt hw e''))
        (Matrix.of.symm (1 : Matrix (Fin 2) (Fin 2) ℝ)) (Matrix.of.symm (archDirMatrix d)) := by
  have hopen := isOpen_setOf_det_ne_zero
  have hdet : (Matrix.of (Matrix.of.symm (1 : Matrix (Fin 2) (Fin 2) ℝ))).det ≠ 0 := by
    rw [Equiv.apply_symm_apply, Matrix.det_one]
    exact one_ne_zero
  have hdiff : HasFDerivAt (fun e' => φ (h * archRealLiftAt hw e'))
      (fderiv ℝ (fun e' => φ (h * archRealLiftAt hw e')) (Matrix.of.symm (1 : Matrix (Fin 2) (Fin 2) ℝ)))
      (Matrix.of.symm (Matrix.of (Matrix.of.symm (1 : Matrix (Fin 2) (Fin 2) ℝ)) *
        (archFlowMatrix d 0 : Matrix (Fin 2) (Fin 2) ℝ))) := by
    rw [of_symm_mul_archFlowMatrix_zero]
    exact (((hφ h).contDiffAt (hopen.mem_nhds hdet)).differentiableAt (by simp)).hasFDerivAt
  have hfun : (fun t : ℝ => φ (h * archFlowAt hw d t)) =
      fun t : ℝ => φ (h * archRealLiftAt hw
        (Matrix.of.symm (Matrix.of (Matrix.of.symm (1 : Matrix (Fin 2) (Fin 2) ℝ)) *
          (archFlowMatrix d t : Matrix (Fin 2) (Fin 2) ℝ)))) := by
    funext t
    rw [← archRealLiftAt_mul_archRealGLAt hw hdet, archRealLiftAt_of_symm_one, one_mul, archFlowAt]
  show deriv (fun t : ℝ => φ (h * archFlowAt hw d t)) 0 = _
  rw [hfun]
  have := (hdiff.comp_hasDerivAt (0 : ℝ) (hasDerivAt_of_symm_mul_archFlowMatrix _ d)).deriv
  simpa only [Function.comp_def, Equiv.apply_symm_apply, one_mul] using this

theorem deriv_scalar_eq_fderiv (φ : AdelicGL2 (𝓞 F) F → ℂ) (hφ : IsArchSmoothAt hw φ)
    (h : AdelicGL2 (𝓞 F) F) :
    deriv (fun s : ℝ => φ (h * archRealGLAt hw (scalarExpGL2 s))) 0 =
      fderiv ℝ (fun e'' : Fin 2 → Fin 2 → ℝ => φ (h * archRealLiftAt hw e''))
        (Matrix.of.symm (1 : Matrix (Fin 2) (Fin 2) ℝ)) (Matrix.of.symm (1 : Matrix (Fin 2) (Fin 2) ℝ)) := by
  have hopen := isOpen_setOf_det_ne_zero
  have hdet : (Matrix.of (Matrix.of.symm (1 : Matrix (Fin 2) (Fin 2) ℝ))).det ≠ 0 := by
    rw [Equiv.apply_symm_apply, Matrix.det_one]
    exact one_ne_zero
  have h0 : (Matrix.of.symm (Matrix.of (Matrix.of.symm (1 : Matrix (Fin 2) (Fin 2) ℝ)) *
        (scalarExpGL2 0 : Matrix (Fin 2) (Fin 2) ℝ)) : Fin 2 → Fin 2 → ℝ) =
      Matrix.of.symm (1 : Matrix (Fin 2) (Fin 2) ℝ) := by
    rw [Equiv.apply_symm_apply, one_mul, scalarExpGL2_coe, Real.exp_zero, one_smul]
  have hdiff : HasFDerivAt (fun e' => φ (h * archRealLiftAt hw e'))
      (fderiv ℝ (fun e' => φ (h * archRealLiftAt hw e')) (Matrix.of.symm (1 : Matrix (Fin 2) (Fin 2) ℝ)))
      (Matrix.of.symm (Matrix.of (Matrix.of.symm (1 : Matrix (Fin 2) (Fin 2) ℝ)) *
        (scalarExpGL2 0 : Matrix (Fin 2) (Fin 2) ℝ))) := by
    rw [h0]
    exact (((hφ h).contDiffAt (hopen.mem_nhds hdet)).differentiableAt (by simp)).hasFDerivAt
  have hfun : (fun s : ℝ => φ (h * archRealGLAt hw (scalarExpGL2 s))) =
      fun s : ℝ => φ (h * archRealLiftAt hw
        (Matrix.of.symm (Matrix.of (Matrix.of.symm (1 : Matrix (Fin 2) (Fin 2) ℝ)) *
          (scalarExpGL2 s : Matrix (Fin 2) (Fin 2) ℝ)))) := by
    funext s
    rw [← archRealLiftAt_mul_archRealGLAt hw hdet, archRealLiftAt_of_symm_one, one_mul]
  rw [hfun]
  have := (hdiff.comp_hasDerivAt (0 : ℝ) (hasDerivAt_of_symm_mul_scalarExpGL2 _)).deriv
  simpa only [Function.comp_def, Equiv.apply_symm_apply, one_mul, mul_one] using this

theorem fderiv_baseChange (φ : AdelicGL2 (𝓞 F) F → ℂ) (hφ : IsArchSmoothAt hw φ)
    (g : AdelicGL2 (𝓞 F) F) (e : Fin 2 → Fin 2 → ℝ) (he : (Matrix.of e).det ≠ 0) (Y : Fin 2 → Fin 2 → ℝ) :
    fderiv ℝ (fun e' : Fin 2 → Fin 2 → ℝ => φ (g * archRealLiftAt hw e')) e Y =
      fderiv ℝ (fun e'' : Fin 2 → Fin 2 → ℝ => φ (g * archRealLiftAt hw e * archRealLiftAt hw e''))
        (Matrix.of.symm (1 : Matrix (Fin 2) (Fin 2) ℝ)) (Matrix.of.symm ((Matrix.of e)⁻¹ * Matrix.of Y)) := by
  have hopen := isOpen_setOf_det_ne_zero

  let L : (Fin 2 → Fin 2 → ℝ) →L[ℝ] (Fin 2 → Fin 2 → ℝ) :=
    LinearMap.toContinuousLinearMap
      { toFun := fun e' => Matrix.of.symm ((Matrix.of e)⁻¹ * Matrix.of e')
        map_add' := fun x y => by
          change (Matrix.of.symm ((Matrix.of e)⁻¹ * (Matrix.of x + Matrix.of y)) : Fin 2 → Fin 2 → ℝ) = _
          rw [Matrix.mul_add]
          rfl
        map_smul' := fun c x => by
          change (Matrix.of.symm ((Matrix.of e)⁻¹ * (c • Matrix.of x)) : Fin 2 → Fin 2 → ℝ) = _
          rw [Matrix.mul_smul]
          rfl }
  have hL : ∀ e', L e' = Matrix.of.symm ((Matrix.of e)⁻¹ * Matrix.of e') := fun _ => rfl
  have hLe : L e = Matrix.of.symm (1 : Matrix (Fin 2) (Fin 2) ℝ) := by
    rw [hL, Matrix.nonsing_inv_mul _ (isUnit_iff_ne_zero.2 he)]
  have hdet1 : (Matrix.of (Matrix.of.symm (1 : Matrix (Fin 2) (Fin 2) ℝ))).det ≠ 0 := by
    rw [Equiv.apply_symm_apply, Matrix.det_one]
    exact one_ne_zero

  set ψ : (Fin 2 → Fin 2 → ℝ) → ℂ := fun e'' => φ (g * archRealLiftAt hw e * archRealLiftAt hw e'') with hψ
  have hψs : ContDiffOn ℝ (⊤ : ℕ∞) ψ {e'' | (Matrix.of e'').det ≠ 0} := hφ (g * archRealLiftAt hw e)

  have hfeq : ∀ e' : Fin 2 → Fin 2 → ℝ, (Matrix.of e').det ≠ 0 →
      φ (g * archRealLiftAt hw e') = ψ (L e') := by
    intro e' he'
    have hdetL : ((Matrix.of e)⁻¹ * Matrix.of e').det ≠ 0 := by
      rw [Matrix.det_mul]
      exact mul_ne_zero (Matrix.isUnit_nonsing_inv_det _ (isUnit_iff_ne_zero.2 he)).ne_zero he'
    have hmul : archRealLiftAt hw e * archRealGLAt hw (Matrix.GeneralLinearGroup.mkOfDetNeZero _ hdetL) =
        archRealLiftAt hw (Matrix.of.symm (Matrix.of e * ((Matrix.of e)⁻¹ * Matrix.of e'))) := by
      rw [archRealLiftAt_mul_archRealGLAt hw he]
      rfl
    have hcancel : Matrix.of e * ((Matrix.of e)⁻¹ * Matrix.of e') = Matrix.of e' := by
      rw [← Matrix.mul_assoc,
        Matrix.mul_nonsing_inv _ (isUnit_iff_ne_zero.2 he),
        Matrix.one_mul]
    rw [hψ, hL]
    show φ (g * archRealLiftAt hw e') =
      φ (g * archRealLiftAt hw e * archRealLiftAt hw (Matrix.of.symm ((Matrix.of e)⁻¹ * Matrix.of e')))
    rw [archRealLiftAt_of_det_ne_zero hw (e := Matrix.of.symm ((Matrix.of e)⁻¹ * Matrix.of e'))
      (by rw [Equiv.apply_symm_apply]; exact hdetL)]
    simp only [Equiv.apply_symm_apply]
    rw [mul_assoc, hmul, hcancel, Equiv.symm_apply_apply]

  have hψd : DifferentiableAt ℝ ψ (L e) := by
    rw [hLe]
    exact ((hψs).contDiffAt (hopen.mem_nhds hdet1)).differentiableAt (by simp)
  have hcomp : HasFDerivAt (fun e' => ψ (L e')) ((fderiv ℝ ψ (L e)).comp L) e :=
    hψd.hasFDerivAt.comp e L.hasFDerivAt
  have hcongr : (fun e' => φ (g * archRealLiftAt hw e')) =ᶠ[nhds e] fun e' => ψ (L e') := by
    filter_upwards [hopen.mem_nhds he] with e' he'
    exact hfeq e' he'
  rw [(hcomp.congr_of_eventuallyEq hcongr).fderiv, ContinuousLinearMap.comp_apply, hLe, hL]

theorem main (φ : AdelicGL2 (𝓞 F) F → ℂ) (hφ : IsArchSmoothAt hw φ)
    (g : AdelicGL2 (𝓞 F) F) (e : Fin 2 → Fin 2 → ℝ) (he : (Matrix.of e).det ≠ 0) (Y : Fin 2 → Fin 2 → ℝ) :
    fderiv ℝ (fun e' : Fin 2 → Fin 2 → ℝ => φ (g * archRealLiftAt hw e')) e Y =
      ((((Matrix.of e)⁻¹ * Matrix.of Y) 0 0 - ((Matrix.of e)⁻¹ * Matrix.of Y) 1 1) / 2 : ℝ) *
          archDerivAt hw ArchDir.H φ (g * archRealLiftAt hw e) +
      ((((Matrix.of e)⁻¹ * Matrix.of Y) 0 1 : ℝ) : ℂ) * archDerivAt hw ArchDir.E φ (g * archRealLiftAt hw e) +
      ((((Matrix.of e)⁻¹ * Matrix.of Y) 1 0 : ℝ) : ℂ) * archDerivAt hw ArchDir.Fm φ (g * archRealLiftAt hw e) +
      ((((Matrix.of e)⁻¹ * Matrix.of Y) 0 0 + ((Matrix.of e)⁻¹ * Matrix.of Y) 1 1) / 2 : ℝ) *
          deriv (fun s : ℝ => φ (g * archRealLiftAt hw e *
            archRealGLAt hw (Units.map (Matrix.scalar (Fin 2) : ℝ →+* Matrix (Fin 2) (Fin 2) ℝ).toMonoidHom
              (Units.mk0 (Real.exp s) (Real.exp_ne_zero s))))) 0 := by
  set A : Matrix (Fin 2) (Fin 2) ℝ := (Matrix.of e)⁻¹ * Matrix.of Y with hA
  set h : AdelicGL2 (𝓞 F) F := g * archRealLiftAt hw e with hh
  have hφh : IsArchSmoothAt hw φ := hφ
  rw [fderiv_baseChange hw φ hφ g e he Y, ← hA, decompose A]
  set D := fderiv ℝ (fun e'' : Fin 2 → Fin 2 → ℝ => φ (h * archRealLiftAt hw e''))
    (Matrix.of.symm (1 : Matrix (Fin 2) (Fin 2) ℝ)) with hD
  rw [map_add, map_add, map_add, map_smul, map_smul, map_smul, map_smul,
    ← archDerivAt_eq_fderiv hw φ hφ h ArchDir.H, ← archDerivAt_eq_fderiv hw φ hφ h ArchDir.E,
    ← archDerivAt_eq_fderiv hw φ hφ h ArchDir.Fm, ← deriv_scalar_eq_fderiv hw φ hφ h]
  simp only [Complex.real_smul, Complex.ofReal_div, Complex.ofReal_sub, Complex.ofReal_add,
    Complex.ofReal_ofNat, scalarExpGL2]

end ArchChartTransport

end

open ArchChartTransport in
theorem solution
    (F : Type) [Field F] [NumberField F] {w : InfinitePlace F} (hw : w.IsReal)
    (φ : AdelicGL2 (𝓞 F) F → ℂ) (hφ : IsArchSmoothAt hw φ)
    (g : AdelicGL2 (𝓞 F) F) (e : Fin 2 → Fin 2 → ℝ) (he : (Matrix.of e).det ≠ 0) (Y : Fin 2 → Fin 2 → ℝ) :
    fderiv ℝ (fun e' : Fin 2 → Fin 2 → ℝ => φ (g * archRealLiftAt hw e')) e Y =
      ((((Matrix.of e)⁻¹ * Matrix.of Y) 0 0 - ((Matrix.of e)⁻¹ * Matrix.of Y) 1 1) / 2 : ℝ) *
          archDerivAt hw ArchDir.H φ (g * archRealLiftAt hw e) +
      ((((Matrix.of e)⁻¹ * Matrix.of Y) 0 1 : ℝ) : ℂ) * archDerivAt hw ArchDir.E φ (g * archRealLiftAt hw e) +
      ((((Matrix.of e)⁻¹ * Matrix.of Y) 1 0 : ℝ) : ℂ) * archDerivAt hw ArchDir.Fm φ (g * archRealLiftAt hw e) +
      ((((Matrix.of e)⁻¹ * Matrix.of Y) 0 0 + ((Matrix.of e)⁻¹ * Matrix.of Y) 1 1) / 2 : ℝ) *
          deriv (fun s : ℝ => φ (g * archRealLiftAt hw e *
            archRealGLAt hw (Units.map (Matrix.scalar (Fin 2) : ℝ →+* Matrix (Fin 2) (Fin 2) ℝ).toMonoidHom
              (Units.mk0 (Real.exp s) (Real.exp_ne_zero s))))) 0 :=
  ArchChartTransport.main hw φ hφ g e he Y

end S_AutomorphicForm_fderiv_apply_mul_archRealLiftAt_eq_of_isArchSmoothAt
end P2MW
export P2MW.S_AutomorphicForm_fderiv_apply_mul_archRealLiftAt_eq_of_isArchSmoothAt (solution)
