-- Prove2me | solution 1 for AutomorphicForm.archCasimirAt_rightTranslate_archRealGLAt
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.553648+00:00
-- url     : https://prove2.me/submissions/a7117e7a-29a0-510d-8cda-9ca2fa79194a

import Definitions.Def_AutomorphicForm_ProductionPinsGeneral
import Definitions.Def_AutomorphicForm_CuspidalConstituent
import Definitions.Def_AutomorphicForm_ArchDerivCasimir
import Definitions.Def_AutomorphicForm_FactorizableTestFn
import Definitions.Def_AutomorphicForm_RightConvolution
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AutomorphicForm_archCasimirAt_rightTranslate_archRealGLAt

set_option autoImplicit false

open NumberField NumberField.AdelicLevel NumberField.AdelicBox
open AutomorphicForm AutomorphicForm.WindowedSiegel AutomorphicForm.SiegelCovering IsDedekindDomain
open AutomorphicForm.CuspidalConstituent

noncomputable section

namespace CasCore17

open NumberField.InfinitePlace NumberField.InfinitePlace.Completion Matrix

variable {F : Type} [Field F] [NumberField F] {w : InfinitePlace F} (hw : w.IsReal)

theorem archRealGLAt_eq_archRealLiftAt (M : GL (Fin 2) ℝ) :
    archRealGLAt hw M = archRealLiftAt hw (Matrix.of.symm (M : Matrix (Fin 2) (Fin 2) ℝ)) := by
  have hdet : (Matrix.of (Matrix.of.symm (M : Matrix (Fin 2) (Fin 2) ℝ))).det ≠ 0 := by
    rw [Equiv.apply_symm_apply]
    exact ((Matrix.isUnit_iff_isUnit_det _).1 M.isUnit).ne_zero
  rw [archRealLiftAt_of_det_ne_zero hw hdet]
  congr 1
  ext i j
  simp [GeneralLinearGroup.mkOfDetNeZero]

theorem archRealGLAt_mul_archRealLiftAt (M : GL (Fin 2) ℝ) {e : Fin 2 → Fin 2 → ℝ} (h : (Matrix.of e).det ≠ 0) :
    archRealGLAt hw M * archRealLiftAt hw e =
      archRealLiftAt hw (Matrix.of.symm ((M : Matrix (Fin 2) (Fin 2) ℝ) * Matrix.of e)) := by
  have hM : ((M : Matrix (Fin 2) (Fin 2) ℝ)).det ≠ 0 := ((Matrix.isUnit_iff_isUnit_det _).1 M.isUnit).ne_zero
  have h' : (Matrix.of (Matrix.of.symm ((M : Matrix (Fin 2) (Fin 2) ℝ) * Matrix.of e))).det ≠ 0 := by
    rw [Equiv.apply_symm_apply, Matrix.det_mul]
    exact mul_ne_zero hM h
  rw [archRealLiftAt_of_det_ne_zero hw h, archRealLiftAt_of_det_ne_zero hw h', ← map_mul]
  congr 1
  ext i j
  simp [GeneralLinearGroup.mkOfDetNeZero]

def conjArr (M : GL (Fin 2) ℝ) (e : Fin 2 → Fin 2 → ℝ) : Fin 2 → Fin 2 → ℝ :=
  Matrix.of.symm (((M⁻¹ : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) * Matrix.of e * (M : Matrix (Fin 2) (Fin 2) ℝ))

theorem det_conjArr (M : GL (Fin 2) ℝ) (e : Fin 2 → Fin 2 → ℝ) :
    (Matrix.of (conjArr M e)).det = (Matrix.of e).det := by
  rw [conjArr, Equiv.apply_symm_apply, Matrix.det_mul, Matrix.det_mul]
  have hMM : ((M⁻¹ : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ).det * (M : Matrix (Fin 2) (Fin 2) ℝ).det = 1 := by
    rw [← Matrix.det_mul, show ((M⁻¹ : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) * (M : Matrix (Fin 2) (Fin 2) ℝ) =
      ((M⁻¹ * M : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) from rfl, inv_mul_cancel, Units.val_one, Matrix.det_one]
  calc ((M⁻¹ : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ).det * (Matrix.of e).det * (M : Matrix (Fin 2) (Fin 2) ℝ).det
      = (((M⁻¹ : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ).det * (M : Matrix (Fin 2) (Fin 2) ℝ).det) * (Matrix.of e).det := by
        ring
    _ = (Matrix.of e).det := by rw [hMM, one_mul]

theorem archRealLiftAt_mul_archRealGLAt_eq (M : GL (Fin 2) ℝ) (e : Fin 2 → Fin 2 → ℝ) :
    archRealLiftAt hw e * archRealGLAt hw M = archRealGLAt hw M * archRealLiftAt hw (conjArr M e) := by
  by_cases h : (Matrix.of e).det ≠ 0
  · have h' : (Matrix.of (conjArr M e)).det ≠ 0 := by rwa [det_conjArr]
    rw [archRealLiftAt_mul_archRealGLAt hw h, archRealGLAt_mul_archRealLiftAt hw M h']
    congr 1
    rw [conjArr, Equiv.apply_symm_apply, ← Matrix.mul_assoc, ← Matrix.mul_assoc,
      show (M : Matrix (Fin 2) (Fin 2) ℝ) * ((M⁻¹ : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) =
        ((M * M⁻¹ : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) from rfl, mul_inv_cancel, Units.val_one, Matrix.one_mul]
  · push Not at h
    have h' : ¬ (Matrix.of (conjArr M e)).det ≠ 0 := by rw [det_conjArr]; exact fun hh => hh h
    have h0 : ¬ (Matrix.of e).det ≠ 0 := fun hh => hh h
    rw [archRealLiftAt, dif_neg h0, archRealLiftAt, dif_neg h', one_mul, mul_one]

def chart (φ : AdelicGL2 (𝓞 F) F → ℂ) (g : AdelicGL2 (𝓞 F) F) : (Fin 2 → Fin 2 → ℝ) → ℂ :=
  fun e => φ (g * archRealLiftAt hw e)

theorem chart_rightTranslate (M : GL (Fin 2) ℝ) (φ : AdelicGL2 (𝓞 F) F → ℂ) (g : AdelicGL2 (𝓞 F) F) :
    chart hw (rightTranslate F (archRealGLAt hw M) φ) g = chart hw φ (g * archRealGLAt hw M) ∘ conjArr M := by
  funext e
  show φ (g * archRealLiftAt hw e * archRealGLAt hw M) = φ (g * archRealGLAt hw M * archRealLiftAt hw (conjArr M e))
  rw [mul_assoc, archRealLiftAt_mul_archRealGLAt_eq hw M e, ← mul_assoc]

def conjCLM (M : GL (Fin 2) ℝ) : (Fin 2 → Fin 2 → ℝ) →L[ℝ] (Fin 2 → Fin 2 → ℝ) :=
  LinearMap.toContinuousLinearMap
    { toFun := conjArr M
      map_add' := fun x y => by
        unfold conjArr
        rw [show Matrix.of (x + y) = Matrix.of x + Matrix.of y from rfl, Matrix.mul_add, Matrix.add_mul]
        rfl
      map_smul' := fun c x => by
        unfold conjArr
        rw [show Matrix.of (c • x) = c • Matrix.of x from rfl, Matrix.mul_smul, Matrix.smul_mul]
        rfl }

theorem conjCLM_apply (M : GL (Fin 2) ℝ) (e : Fin 2 → Fin 2 → ℝ) : conjCLM M e = conjArr M e := rfl

theorem coe_conjCLM (M : GL (Fin 2) ℝ) : (conjCLM M : (Fin 2 → Fin 2 → ℝ) → (Fin 2 → Fin 2 → ℝ)) = conjArr M := rfl

theorem conjArr_one (M : GL (Fin 2) ℝ) : conjArr M (Matrix.of.symm 1) = Matrix.of.symm 1 := by
  unfold conjArr
  rw [Equiv.apply_symm_apply, Matrix.mul_one,
    show ((M⁻¹ : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) * (M : Matrix (Fin 2) (Fin 2) ℝ) =
      ((M⁻¹ * M : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) from rfl, inv_mul_cancel, Units.val_one]

end CasCore17

namespace CasCore17

open NumberField.InfinitePlace NumberField.InfinitePlace.Completion Matrix

variable {F : Type} [Field F] [NumberField F] {w : InfinitePlace F} (hw : w.IsReal)

abbrev U : Set (Fin 2 → Fin 2 → ℝ) := {e | (Matrix.of e).det ≠ 0}

theorem one_mem_U : (Matrix.of.symm (1 : Matrix (Fin 2) (Fin 2) ℝ)) ∈ U := by
  show (Matrix.of (Matrix.of.symm (1 : Matrix (Fin 2) (Fin 2) ℝ))).det ≠ 0
  rw [Equiv.apply_symm_apply, Matrix.det_one]
  exact one_ne_zero

def D1 (φ : AdelicGL2 (𝓞 F) F → ℂ) (g : AdelicGL2 (𝓞 F) F) (Y : Matrix (Fin 2) (Fin 2) ℝ) : ℂ :=
  fderiv ℝ (chart hw φ g) (Matrix.of.symm 1) (Matrix.of.symm Y)

theorem contDiffAt_chart {φ : AdelicGL2 (𝓞 F) F → ℂ} (hφ : IsArchSmoothAt hw φ) (g : AdelicGL2 (𝓞 F) F)
    {e : Fin 2 → Fin 2 → ℝ} (he : (Matrix.of e).det ≠ 0) : ContDiffAt ℝ (⊤ : ℕ∞) (chart hw φ g) e :=
  (hφ g).contDiffAt (isOpen_setOf_det_ne_zero.mem_nhds he)

theorem hasFDerivAt_chart {φ : AdelicGL2 (𝓞 F) F → ℂ} (hφ : IsArchSmoothAt hw φ) (g : AdelicGL2 (𝓞 F) F)
    {e : Fin 2 → Fin 2 → ℝ} (he : (Matrix.of e).det ≠ 0) :
    HasFDerivAt (chart hw φ g) (fderiv ℝ (chart hw φ g) e) e :=
  ((contDiffAt_chart hw hφ g he).differentiableAt (by simp)).hasFDerivAt

theorem archDerivAt_apply_mul_archRealLiftAt {φ : AdelicGL2 (𝓞 F) F → ℂ} (hφ : IsArchSmoothAt hw φ) (d : ArchDir)
    (g : AdelicGL2 (𝓞 F) F) {e : Fin 2 → Fin 2 → ℝ} (he : (Matrix.of e).det ≠ 0) :
    archDerivAt hw d φ (g * archRealLiftAt hw e) =
      fderiv ℝ (chart hw φ g) e (Matrix.of.symm (Matrix.of e * archDirMatrix d)) := by
  have hdiff : HasFDerivAt (chart hw φ g) (fderiv ℝ (chart hw φ g) e)
      (Matrix.of.symm (Matrix.of e * (archFlowMatrix d 0 : Matrix (Fin 2) (Fin 2) ℝ))) := by
    rw [of_symm_mul_archFlowMatrix_zero]
    exact hasFDerivAt_chart hw hφ g he
  have hfun : (fun t : ℝ => φ (g * archRealLiftAt hw e * archFlowAt hw d t)) =
      fun t : ℝ => chart hw φ g (Matrix.of.symm (Matrix.of e * (archFlowMatrix d t : Matrix (Fin 2) (Fin 2) ℝ))) := by
    funext t
    show _ = φ (g * archRealLiftAt hw _)
    rw [archFlowAt, mul_assoc, archRealLiftAt_mul_archRealGLAt hw he]
  show deriv (fun t : ℝ => φ (g * archRealLiftAt hw e * archFlowAt hw d t)) 0 = _
  rw [hfun]
  simpa only [Function.comp_def] using
    (hdiff.comp_hasDerivAt (0 : ℝ) (hasDerivAt_of_symm_mul_archFlowMatrix e d)).deriv

theorem archDerivAt_eq_D1 {φ : AdelicGL2 (𝓞 F) F → ℂ} (hφ : IsArchSmoothAt hw φ) (d : ArchDir)
    (g : AdelicGL2 (𝓞 F) F) : archDerivAt hw d φ g = D1 hw φ g (archDirMatrix d) := by
  have h := archDerivAt_apply_mul_archRealLiftAt hw hφ d g (e := Matrix.of.symm 1) one_mem_U
  rw [archRealLiftAt_of_symm_one, mul_one, Equiv.apply_symm_apply, Matrix.one_mul] at h
  exact h

theorem isArchSmoothAt_rightTranslate (M : GL (Fin 2) ℝ) {φ : AdelicGL2 (𝓞 F) F → ℂ} (hφ : IsArchSmoothAt hw φ) :
    IsArchSmoothAt hw (rightTranslate F (archRealGLAt hw M) φ) := by
  intro g
  show ContDiffOn ℝ (⊤ : ℕ∞) (chart hw (rightTranslate F (archRealGLAt hw M) φ) g) U
  rw [chart_rightTranslate, ← coe_conjCLM]
  refine (hφ (g * archRealGLAt hw M)).comp (conjCLM M).contDiff.contDiffOn fun e he => ?_
  show (Matrix.of (conjArr M e)).det ≠ 0
  rw [det_conjArr]
  exact he

theorem conjCLM_of_symm (M : GL (Fin 2) ℝ) (Y : Matrix (Fin 2) (Fin 2) ℝ) :
    conjCLM M (Matrix.of.symm Y) =
      Matrix.of.symm (((M⁻¹ : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) * Y * (M : Matrix (Fin 2) (Fin 2) ℝ)) := by
  rw [conjCLM_apply, conjArr, Equiv.apply_symm_apply]

theorem archDerivAt_rightTranslate (M : GL (Fin 2) ℝ) {φ : AdelicGL2 (𝓞 F) F → ℂ} (hφ : IsArchSmoothAt hw φ)
    (d : ArchDir) (g : AdelicGL2 (𝓞 F) F) :
    archDerivAt hw d (rightTranslate F (archRealGLAt hw M) φ) g =
      D1 hw φ (g * archRealGLAt hw M)
        (((M⁻¹ : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) * archDirMatrix d * (M : Matrix (Fin 2) (Fin 2) ℝ)) := by
  rw [archDerivAt_eq_D1 hw (isArchSmoothAt_rightTranslate hw M hφ), D1, D1, chart_rightTranslate, ← coe_conjCLM,
    ← conjCLM_of_symm]
  have hd : DifferentiableAt ℝ (chart hw φ (g * archRealGLAt hw M)) (conjCLM M (Matrix.of.symm 1)) := by
    rw [conjCLM_apply, conjArr_one]
    exact (contDiffAt_chart hw hφ _ one_mem_U).differentiableAt (by simp)
  rw [fderiv_comp _ hd (conjCLM M).differentiableAt, ContinuousLinearMap.fderiv, ContinuousLinearMap.comp_apply,
    conjCLM_apply M (Matrix.of.symm 1), conjArr_one]

end CasCore17

namespace CasCore17

open NumberField.InfinitePlace NumberField.InfinitePlace.Completion Matrix

variable {F : Type} [Field F] [NumberField F] {w : InfinitePlace F} (hw : w.IsReal)

def D2 (φ : AdelicGL2 (𝓞 F) F → ℂ) (g : AdelicGL2 (𝓞 F) F) (Y Z : Matrix (Fin 2) (Fin 2) ℝ) : ℂ :=
  fderiv ℝ (fderiv ℝ (chart hw φ g)) (Matrix.of.symm 1) (Matrix.of.symm Y) (Matrix.of.symm Z)

omit hw in
theorem hasDerivAt_flow_entries (d : ArchDir) :
    HasDerivAt (fun t : ℝ => Matrix.of.symm ((archFlowMatrix d t : Matrix (Fin 2) (Fin 2) ℝ)))
      (Matrix.of.symm (archDirMatrix d)) 0 := by
  have h := hasDerivAt_of_symm_mul_archFlowMatrix (Matrix.of.symm 1) d
  simp only [Equiv.apply_symm_apply, Matrix.one_mul] at h
  exact h

omit hw in
theorem hasDerivAt_flow_mul_const (d : ArchDir) (X : Matrix (Fin 2) (Fin 2) ℝ) :
    HasDerivAt (fun t : ℝ => Matrix.of.symm ((archFlowMatrix d t : Matrix (Fin 2) (Fin 2) ℝ) * X))
      (Matrix.of.symm (archDirMatrix d * X)) 0 := by
  rw [hasDerivAt_pi]
  intro i
  rw [hasDerivAt_pi]
  intro j
  simp only [Matrix.of_symm_apply, Matrix.mul_apply]
  exact HasDerivAt.fun_sum fun k _ => (hasDerivAt_archFlowMatrix_apply d i k).mul_const (X k j)

theorem archDerivAt_archDerivAt_eq {φ : AdelicGL2 (𝓞 F) F → ℂ} (hφ : IsArchSmoothAt hw φ) (i j : ArchDir)
    (g : AdelicGL2 (𝓞 F) F) :
    archDerivAt hw i (archDerivAt hw j φ) g =
      D2 hw φ g (archDirMatrix i) (archDirMatrix j) + D1 hw φ g (archDirMatrix i * archDirMatrix j) := by
  have hfun : (fun t : ℝ => archDerivAt hw j φ (g * archFlowAt hw i t)) =
      fun t => (fderiv ℝ (chart hw φ g) (Matrix.of.symm ((archFlowMatrix i t : Matrix (Fin 2) (Fin 2) ℝ))))
        (Matrix.of.symm ((archFlowMatrix i t : Matrix (Fin 2) (Fin 2) ℝ) * archDirMatrix j)) := by
    funext t
    have hdet : (Matrix.of (Matrix.of.symm ((archFlowMatrix i t : Matrix (Fin 2) (Fin 2) ℝ)))).det ≠ 0 := by
      rw [Equiv.apply_symm_apply]
      exact ((Matrix.isUnit_iff_isUnit_det _).1 (archFlowMatrix i t).isUnit).ne_zero
    rw [archFlowAt, archRealGLAt_eq_archRealLiftAt, archDerivAt_apply_mul_archRealLiftAt hw hφ j g hdet,
      Equiv.apply_symm_apply]
  have hchart : ContDiffAt ℝ (⊤ : ℕ∞) (chart hw φ g) (Matrix.of.symm 1) := contDiffAt_chart hw hφ g one_mem_U
  have hA0 : HasFDerivAt (fderiv ℝ (chart hw φ g)) (fderiv ℝ (fderiv ℝ (chart hw φ g)) (Matrix.of.symm 1))
      (Matrix.of.symm 1) :=
    ((hchart.fderiv_right (m := 2) (by norm_cast)).differentiableAt (by simp)).hasFDerivAt
  have hγ0 : Matrix.of.symm ((archFlowMatrix i 0 : Matrix (Fin 2) (Fin 2) ℝ)) = Matrix.of.symm 1 := by
    rw [archFlowMatrix_zero, Units.val_one]
  have hA : HasDerivAt (fun t : ℝ => fderiv ℝ (chart hw φ g) (Matrix.of.symm ((archFlowMatrix i t : Matrix (Fin 2) (Fin 2) ℝ))))
      (fderiv ℝ (fderiv ℝ (chart hw φ g)) (Matrix.of.symm 1) (Matrix.of.symm (archDirMatrix i))) 0 :=
    hA0.comp_hasDerivAt_of_eq (0 : ℝ) (hasDerivAt_flow_entries i) hγ0.symm
  have h := hA.clm_apply (hasDerivAt_flow_mul_const i (archDirMatrix j))
  show deriv (fun t : ℝ => archDerivAt hw j φ (g * archFlowAt hw i t)) 0 = _
  rw [hfun, h.deriv]
  simp only [archFlowMatrix_zero, Units.val_one, Matrix.one_mul, D2, D1]

theorem D2_symm {φ : AdelicGL2 (𝓞 F) F → ℂ} (hφ : IsArchSmoothAt hw φ) (g : AdelicGL2 (𝓞 F) F)
    (Y Z : Matrix (Fin 2) (Fin 2) ℝ) : D2 hw φ g Y Z = D2 hw φ g Z Y :=
  ((contDiffAt_chart hw hφ g one_mem_U).isSymmSndFDerivAt (by simp; norm_cast)).eq _ _

theorem D1_sub (φ : AdelicGL2 (𝓞 F) F → ℂ) (g : AdelicGL2 (𝓞 F) F) (Y Z : Matrix (Fin 2) (Fin 2) ℝ) :
    D1 hw φ g (Y - Z) = D1 hw φ g Y - D1 hw φ g Z := by
  show fderiv ℝ (chart hw φ g) (Matrix.of.symm 1) (Matrix.of.symm Y - Matrix.of.symm Z) = _
  rw [map_sub]
  rfl

theorem D1_add (φ : AdelicGL2 (𝓞 F) F → ℂ) (g : AdelicGL2 (𝓞 F) F) (Y Z : Matrix (Fin 2) (Fin 2) ℝ) :
    D1 hw φ g (Y + Z) = D1 hw φ g Y + D1 hw φ g Z := by
  show fderiv ℝ (chart hw φ g) (Matrix.of.symm 1) (Matrix.of.symm Y + Matrix.of.symm Z) = _
  rw [map_add]
  rfl

theorem D1_smul (φ : AdelicGL2 (𝓞 F) F → ℂ) (g : AdelicGL2 (𝓞 F) F) (c : ℝ) (Y : Matrix (Fin 2) (Fin 2) ℝ) :
    D1 hw φ g (c • Y) = (c : ℂ) * D1 hw φ g Y := by
  show fderiv ℝ (chart hw φ g) (Matrix.of.symm 1) (c • Matrix.of.symm Y) = _
  rw [map_smul, Complex.real_smul]
  rfl

theorem archDerivAt_comm {φ : AdelicGL2 (𝓞 F) F → ℂ} (hφ : IsArchSmoothAt hw φ) (i j : ArchDir)
    (g : AdelicGL2 (𝓞 F) F) :
    archDerivAt hw i (archDerivAt hw j φ) g - archDerivAt hw j (archDerivAt hw i φ) g =
      D1 hw φ g (archDirMatrix i * archDirMatrix j - archDirMatrix j * archDirMatrix i) := by
  rw [archDerivAt_archDerivAt_eq hw hφ, archDerivAt_archDerivAt_eq hw hφ, D2_symm hw hφ g (archDirMatrix j), D1_sub]
  ring

end CasCore17

namespace CasCore17

open NumberField.InfinitePlace NumberField.InfinitePlace.Completion Matrix

variable {F : Type} [Field F] [NumberField F] {w : InfinitePlace F} (hw : w.IsReal)

def AdM (M : GL (Fin 2) ℝ) (X : Matrix (Fin 2) (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  ((M⁻¹ : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) * X * (M : Matrix (Fin 2) (Fin 2) ℝ)

omit hw in
theorem trace_archDirMatrix (d : ArchDir) : Matrix.trace (archDirMatrix d) = 0 := by
  cases d <;> simp [archDirMatrix, Matrix.trace_fin_two]

omit hw in
theorem AdM_traceless (M : GL (Fin 2) ℝ) (d : ArchDir) : (AdM M (archDirMatrix d)) 1 1 = -(AdM M (archDirMatrix d)) 0 0 := by
  have h : Matrix.trace (AdM M (archDirMatrix d)) = 0 := by
    rw [AdM, Matrix.trace_units_conj', trace_archDirMatrix]
  rw [Matrix.trace_fin_two] at h
  linarith

omit hw in

theorem eq_smul_archDirMatrix (Y : Matrix (Fin 2) (Fin 2) ℝ) (hY : Y 1 1 = -Y 0 0) :
    Y = Y 0 0 • archDirMatrix .H + Y 0 1 • archDirMatrix .E + Y 1 0 • archDirMatrix .Fm := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [archDirMatrix, hY]

def cf (M : GL (Fin 2) ℝ) (d e : ArchDir) : ℂ :=
  match e with
  | .H => ((AdM M (archDirMatrix d)) 0 0 : ℝ)
  | .E => ((AdM M (archDirMatrix d)) 0 1 : ℝ)
  | .Fm => ((AdM M (archDirMatrix d)) 1 0 : ℝ)

def Dconj (M : GL (Fin 2) ℝ) (d : ArchDir) (θ : AdelicGL2 (𝓞 F) F → ℂ) : AdelicGL2 (𝓞 F) F → ℂ :=
  cf M d .H • archDerivAt hw .H θ + cf M d .E • archDerivAt hw .E θ + cf M d .Fm • archDerivAt hw .Fm θ

theorem isArchSmoothAt_Dconj (M : GL (Fin 2) ℝ) (d : ArchDir) {θ : AdelicGL2 (𝓞 F) F → ℂ} (hθ : IsArchSmoothAt hw θ) :
    IsArchSmoothAt hw (Dconj hw M d θ) :=
  (((hθ.archDerivAt .H).smul _).add ((hθ.archDerivAt .E).smul _)).add ((hθ.archDerivAt .Fm).smul _)

theorem Dconj_apply (M : GL (Fin 2) ℝ) (d : ArchDir) (θ : AdelicGL2 (𝓞 F) F → ℂ) (g : AdelicGL2 (𝓞 F) F) :
    Dconj hw M d θ g = cf M d .H * archDerivAt hw .H θ g + cf M d .E * archDerivAt hw .E θ g +
      cf M d .Fm * archDerivAt hw .Fm θ g := by
  simp only [Dconj, Pi.add_apply, Pi.smul_apply, smul_eq_mul]

theorem D1_AdM {θ : AdelicGL2 (𝓞 F) F → ℂ} (hθ : IsArchSmoothAt hw θ) (M : GL (Fin 2) ℝ) (d : ArchDir)
    (g : AdelicGL2 (𝓞 F) F) : D1 hw θ g (AdM M (archDirMatrix d)) = Dconj hw M d θ g := by
  conv_lhs => rw [eq_smul_archDirMatrix (AdM M (archDirMatrix d)) (AdM_traceless M d)]
  rw [D1_add, D1_add, D1_smul, D1_smul, D1_smul, ← archDerivAt_eq_D1 hw hθ, ← archDerivAt_eq_D1 hw hθ,
    ← archDerivAt_eq_D1 hw hθ, Dconj_apply]
  rfl

theorem archDerivAt_rightTranslate_eq_Dconj (M : GL (Fin 2) ℝ) {θ : AdelicGL2 (𝓞 F) F → ℂ} (hθ : IsArchSmoothAt hw θ)
    (d : ArchDir) : archDerivAt hw d (rightTranslate F (archRealGLAt hw M) θ) = rightTranslate F (archRealGLAt hw M) (Dconj hw M d θ) := by
  funext g
  rw [archDerivAt_rightTranslate hw M hθ, ← AdM, D1_AdM hw hθ]
  rfl

theorem archDerivAt_Dconj (M : GL (Fin 2) ℝ) (d i : ArchDir) {θ : AdelicGL2 (𝓞 F) F → ℂ} (hθ : IsArchSmoothAt hw θ)
    (g : AdelicGL2 (𝓞 F) F) :
    archDerivAt hw i (Dconj hw M d θ) g = cf M d .H * archDerivAt hw i (archDerivAt hw .H θ) g +
      cf M d .E * archDerivAt hw i (archDerivAt hw .E θ) g + cf M d .Fm * archDerivAt hw i (archDerivAt hw .Fm θ) g := by
  unfold Dconj
  rw [archDerivAt_add (((hθ.archDerivAt .H).smul _).add ((hθ.archDerivAt .E).smul _)) ((hθ.archDerivAt .Fm).smul _),
    archDerivAt_add ((hθ.archDerivAt .H).smul _) ((hθ.archDerivAt .E).smul _), archDerivAt_smul, archDerivAt_smul,
    archDerivAt_smul]
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]

omit hw in
theorem rightTranslate_combo (k : AdelicGL2 (𝓞 F) F) (a b : ℂ) (θ₁ θ₂ θ₃ : AdelicGL2 (𝓞 F) F → ℂ) :
    -(a • rightTranslate F k θ₁ - b • rightTranslate F k θ₂ + rightTranslate F k θ₃) =
      rightTranslate F k (-(a • θ₁ - b • θ₂ + θ₃)) := by
  funext g
  simp only [rightTranslate, Pi.neg_apply, Pi.add_apply, Pi.sub_apply, Pi.smul_apply]

end CasCore17

namespace CasCore17

open NumberField.InfinitePlace NumberField.InfinitePlace.Completion Matrix

variable {F : Type} [Field F] [NumberField F] {w : InfinitePlace F} (hw : w.IsReal)

omit hw in
theorem AdM_eq (M : GL (Fin 2) ℝ) (X : Matrix (Fin 2) (Fin 2) ℝ) :
    AdM M X = ((M : Matrix (Fin 2) (Fin 2) ℝ)).det⁻¹ • (Matrix.adjugate (M : Matrix (Fin 2) (Fin 2) ℝ) * X * (M : Matrix (Fin 2) (Fin 2) ℝ)) := by
  rw [AdM, Matrix.coe_units_inv, Matrix.inv_def, Ring.inverse_eq_inv', Matrix.smul_mul, Matrix.smul_mul]

omit hw in
theorem cf_H_H (M : GL (Fin 2) ℝ) :
    cf M .H .H = ((((M : Matrix (Fin 2) (Fin 2) ℝ)).det⁻¹ * ((M : Matrix (Fin 2) (Fin 2) ℝ) 0 0 * (M : Matrix (Fin 2) (Fin 2) ℝ) 1 1 + (M : Matrix (Fin 2) (Fin 2) ℝ) 0 1 * (M : Matrix (Fin 2) (Fin 2) ℝ) 1 0) : ℝ) : ℂ) := by
  simp only [cf, AdM_eq, Matrix.adjugate_fin_two, Matrix.smul_apply, smul_eq_mul, Matrix.mul_apply, Fin.sum_univ_two,
    archDirMatrix, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.empty_val',
    Matrix.cons_val_fin_one]
  push_cast
  ring

omit hw in
theorem cf_H_E (M : GL (Fin 2) ℝ) :
    cf M .H .E = ((((M : Matrix (Fin 2) (Fin 2) ℝ)).det⁻¹ * (2 * (M : Matrix (Fin 2) (Fin 2) ℝ) 0 1 * (M : Matrix (Fin 2) (Fin 2) ℝ) 1 1) : ℝ) : ℂ) := by
  simp only [cf, AdM_eq, Matrix.adjugate_fin_two, Matrix.smul_apply, smul_eq_mul, Matrix.mul_apply, Fin.sum_univ_two,
    archDirMatrix, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.empty_val',
    Matrix.cons_val_fin_one]
  push_cast
  ring

omit hw in
theorem cf_H_Fm (M : GL (Fin 2) ℝ) :
    cf M .H .Fm = ((((M : Matrix (Fin 2) (Fin 2) ℝ)).det⁻¹ * (-(2 * (M : Matrix (Fin 2) (Fin 2) ℝ) 0 0 * (M : Matrix (Fin 2) (Fin 2) ℝ) 1 0)) : ℝ) : ℂ) := by
  simp only [cf, AdM_eq, Matrix.adjugate_fin_two, Matrix.smul_apply, smul_eq_mul, Matrix.mul_apply, Fin.sum_univ_two,
    archDirMatrix, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.empty_val',
    Matrix.cons_val_fin_one]
  push_cast
  ring

omit hw in
theorem cf_E_H (M : GL (Fin 2) ℝ) :
    cf M .E .H = ((((M : Matrix (Fin 2) (Fin 2) ℝ)).det⁻¹ * ((M : Matrix (Fin 2) (Fin 2) ℝ) 1 0 * (M : Matrix (Fin 2) (Fin 2) ℝ) 1 1) : ℝ) : ℂ) := by
  simp only [cf, AdM_eq, Matrix.adjugate_fin_two, Matrix.smul_apply, smul_eq_mul, Matrix.mul_apply, Fin.sum_univ_two,
    archDirMatrix, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.empty_val',
    Matrix.cons_val_fin_one]
  push_cast
  ring

omit hw in
theorem cf_E_E (M : GL (Fin 2) ℝ) :
    cf M .E .E = ((((M : Matrix (Fin 2) (Fin 2) ℝ)).det⁻¹ * ((M : Matrix (Fin 2) (Fin 2) ℝ) 1 1 * (M : Matrix (Fin 2) (Fin 2) ℝ) 1 1) : ℝ) : ℂ) := by
  simp only [cf, AdM_eq, Matrix.adjugate_fin_two, Matrix.smul_apply, smul_eq_mul, Matrix.mul_apply, Fin.sum_univ_two,
    archDirMatrix, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.empty_val',
    Matrix.cons_val_fin_one]
  push_cast
  ring

omit hw in
theorem cf_E_Fm (M : GL (Fin 2) ℝ) :
    cf M .E .Fm = ((((M : Matrix (Fin 2) (Fin 2) ℝ)).det⁻¹ * (-((M : Matrix (Fin 2) (Fin 2) ℝ) 1 0 * (M : Matrix (Fin 2) (Fin 2) ℝ) 1 0)) : ℝ) : ℂ) := by
  simp only [cf, AdM_eq, Matrix.adjugate_fin_two, Matrix.smul_apply, smul_eq_mul, Matrix.mul_apply, Fin.sum_univ_two,
    archDirMatrix, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.empty_val',
    Matrix.cons_val_fin_one]
  push_cast
  ring

omit hw in
theorem cf_Fm_H (M : GL (Fin 2) ℝ) :
    cf M .Fm .H = ((((M : Matrix (Fin 2) (Fin 2) ℝ)).det⁻¹ * (-((M : Matrix (Fin 2) (Fin 2) ℝ) 0 0 * (M : Matrix (Fin 2) (Fin 2) ℝ) 0 1)) : ℝ) : ℂ) := by
  simp only [cf, AdM_eq, Matrix.adjugate_fin_two, Matrix.smul_apply, smul_eq_mul, Matrix.mul_apply, Fin.sum_univ_two,
    archDirMatrix, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.empty_val',
    Matrix.cons_val_fin_one]
  push_cast
  ring

omit hw in
theorem cf_Fm_E (M : GL (Fin 2) ℝ) :
    cf M .Fm .E = ((((M : Matrix (Fin 2) (Fin 2) ℝ)).det⁻¹ * (-((M : Matrix (Fin 2) (Fin 2) ℝ) 0 1 * (M : Matrix (Fin 2) (Fin 2) ℝ) 0 1)) : ℝ) : ℂ) := by
  simp only [cf, AdM_eq, Matrix.adjugate_fin_two, Matrix.smul_apply, smul_eq_mul, Matrix.mul_apply, Fin.sum_univ_two,
    archDirMatrix, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.empty_val',
    Matrix.cons_val_fin_one]
  push_cast
  ring

omit hw in
theorem cf_Fm_Fm (M : GL (Fin 2) ℝ) :
    cf M .Fm .Fm = ((((M : Matrix (Fin 2) (Fin 2) ℝ)).det⁻¹ * ((M : Matrix (Fin 2) (Fin 2) ℝ) 0 0 * (M : Matrix (Fin 2) (Fin 2) ℝ) 0 0) : ℝ) : ℂ) := by
  simp only [cf, AdM_eq, Matrix.adjugate_fin_two, Matrix.smul_apply, smul_eq_mul, Matrix.mul_apply, Fin.sum_univ_two,
    archDirMatrix, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.empty_val',
    Matrix.cons_val_fin_one]
  push_cast
  ring

omit hw in
theorem bracket_H_E : archDirMatrix .H * archDirMatrix .E - archDirMatrix .E * archDirMatrix .H = (2 : ℝ) • archDirMatrix .E := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [archDirMatrix, Matrix.mul_apply, Fin.sum_univ_two] <;> norm_num

omit hw in
theorem bracket_H_Fm : archDirMatrix .H * archDirMatrix .Fm - archDirMatrix .Fm * archDirMatrix .H = (-2 : ℝ) • archDirMatrix .Fm := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [archDirMatrix, Matrix.mul_apply, Fin.sum_univ_two] <;> norm_num

omit hw in
theorem bracket_E_Fm : archDirMatrix .E * archDirMatrix .Fm - archDirMatrix .Fm * archDirMatrix .E = (1 : ℝ) • archDirMatrix .H := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [archDirMatrix, Matrix.mul_apply, Fin.sum_univ_two]

theorem rel_E_H {φ : AdelicGL2 (𝓞 F) F → ℂ} (hφ : IsArchSmoothAt hw φ) (g : AdelicGL2 (𝓞 F) F) :
    archDerivAt hw .E (archDerivAt hw .H φ) g = archDerivAt hw .H (archDerivAt hw .E φ) g - 2 * archDerivAt hw .E φ g := by
  have h := archDerivAt_comm hw hφ .H .E g
  rw [bracket_H_E, D1_smul, ← archDerivAt_eq_D1 hw hφ] at h
  push_cast at h
  linear_combination -h

theorem rel_Fm_H {φ : AdelicGL2 (𝓞 F) F → ℂ} (hφ : IsArchSmoothAt hw φ) (g : AdelicGL2 (𝓞 F) F) :
    archDerivAt hw .Fm (archDerivAt hw .H φ) g = archDerivAt hw .H (archDerivAt hw .Fm φ) g + 2 * archDerivAt hw .Fm φ g := by
  have h := archDerivAt_comm hw hφ .H .Fm g
  rw [bracket_H_Fm, D1_smul, ← archDerivAt_eq_D1 hw hφ] at h
  push_cast at h
  linear_combination -h

theorem rel_Fm_E {φ : AdelicGL2 (𝓞 F) F → ℂ} (hφ : IsArchSmoothAt hw φ) (g : AdelicGL2 (𝓞 F) F) :
    archDerivAt hw .Fm (archDerivAt hw .E φ) g = archDerivAt hw .E (archDerivAt hw .Fm φ) g - archDerivAt hw .H φ g := by
  have h := archDerivAt_comm hw hφ .E .Fm g
  rw [bracket_E_Fm, D1_smul, ← archDerivAt_eq_D1 hw hφ] at h
  push_cast at h
  linear_combination -h

end CasCore17

namespace CasCore17

open NumberField.InfinitePlace NumberField.InfinitePlace.Completion Matrix

variable {F : Type} [Field F] [NumberField F] {w : InfinitePlace F} (hw : w.IsReal)

omit hw in
theorem continuous_rightTranslate {θ : AdelicGL2 (𝓞 F) F → ℂ} (hθ : Continuous θ) (k : AdelicGL2 (𝓞 F) F) :
    Continuous (rightTranslate F k θ) :=
  hθ.comp (continuous_id.mul continuous_const)

theorem continuous_Dconj (M : GL (Fin 2) ℝ) (d : ArchDir) {θ : AdelicGL2 (𝓞 F) F → ℂ}
    (h : ∀ e : ArchDir, Continuous (archDerivAt hw e θ)) : Continuous (Dconj hw M d θ) := by
  unfold Dconj
  exact (((h .H).const_smul (cf M d .H)).add ((h .E).const_smul (cf M d .E))).add ((h .Fm).const_smul (cf M d .Fm))

theorem continuous_archDerivAt_Dconj (M : GL (Fin 2) ℝ) (d i : ArchDir) {θ : AdelicGL2 (𝓞 F) F → ℂ}
    (hθ : IsArchSmoothAt hw θ) (h2 : ∀ e e' : ArchDir, Continuous (archDerivAt hw e (archDerivAt hw e' θ))) :
    Continuous (archDerivAt hw i (Dconj hw M d θ)) := by
  have : archDerivAt hw i (Dconj hw M d θ) = fun g => cf M d .H * archDerivAt hw i (archDerivAt hw .H θ) g +
      cf M d .E * archDerivAt hw i (archDerivAt hw .E θ) g + cf M d .Fm * archDerivAt hw i (archDerivAt hw .Fm θ) g :=
    funext fun g => archDerivAt_Dconj hw M d i hθ g
  rw [this]
  exact ((continuous_const.mul (h2 i .H)).add (continuous_const.mul (h2 i .E))).add (continuous_const.mul (h2 i .Fm))

theorem casimir_identity (M : GL (Fin 2) ℝ) {φ : AdelicGL2 (𝓞 F) F → ℂ} (hφ : IsArchSmoothAt hw φ) (g : AdelicGL2 (𝓞 F) F) :
    -((1 / 4 : ℂ) * Dconj hw M .H (Dconj hw M .H φ) g - (1 / 2 : ℂ) * Dconj hw M .H φ g + Dconj hw M .E (Dconj hw M .Fm φ) g) =
      archCasimirAt hw φ g := by
  have hdet : (((M : Matrix (Fin 2) (Fin 2) ℝ)).det : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr ((Matrix.isUnit_iff_isUnit_det _).1 M.isUnit).ne_zero
  have hdetR : ((M : Matrix (Fin 2) (Fin 2) ℝ)).det = (M : Matrix (Fin 2) (Fin 2) ℝ) 0 0 * (M : Matrix (Fin 2) (Fin 2) ℝ) 1 1 -
      (M : Matrix (Fin 2) (Fin 2) ℝ) 0 1 * (M : Matrix (Fin 2) (Fin 2) ℝ) 1 0 := Matrix.det_fin_two _
  show _ = (-((1 / 4 : ℂ) • archDerivAt hw .H (archDerivAt hw .H φ) - (1 / 2 : ℂ) • archDerivAt hw .H φ +
    archDerivAt hw .E (archDerivAt hw .Fm φ))) g
  simp only [Pi.neg_apply, Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, Dconj_apply,
    archDerivAt_Dconj hw M _ _ hφ, rel_E_H hw hφ, rel_Fm_H hw hφ, rel_Fm_E hw hφ,
    cf_H_H, cf_H_E, cf_H_Fm, cf_E_H, cf_E_E, cf_E_Fm, cf_Fm_H, cf_Fm_E, cf_Fm_Fm]
  push_cast
  rw [hdetR] at hdet ⊢
  push_cast at hdet ⊢
  field_simp
  ring

theorem archCasimirAt_rightTranslate (M : GL (Fin 2) ℝ) {φ : AdelicGL2 (𝓞 F) F → ℂ} (hφ : IsArchSmoothAt hw φ) :
    archCasimirAt hw (rightTranslate F (archRealGLAt hw M) φ) = rightTranslate F (archRealGLAt hw M) (archCasimirAt hw φ) := by
  have h1 : archDerivAt hw .H (rightTranslate F (archRealGLAt hw M) φ) = rightTranslate F (archRealGLAt hw M) (Dconj hw M .H φ) :=
    archDerivAt_rightTranslate_eq_Dconj hw M hφ .H
  have h2 : archDerivAt hw .H (archDerivAt hw .H (rightTranslate F (archRealGLAt hw M) φ)) =
      rightTranslate F (archRealGLAt hw M) (Dconj hw M .H (Dconj hw M .H φ)) := by
    rw [h1]
    exact archDerivAt_rightTranslate_eq_Dconj hw M (isArchSmoothAt_Dconj hw M .H hφ) .H
  have h3 : archDerivAt hw .Fm (rightTranslate F (archRealGLAt hw M) φ) = rightTranslate F (archRealGLAt hw M) (Dconj hw M .Fm φ) :=
    archDerivAt_rightTranslate_eq_Dconj hw M hφ .Fm
  have h4 : archDerivAt hw .E (archDerivAt hw .Fm (rightTranslate F (archRealGLAt hw M) φ)) =
      rightTranslate F (archRealGLAt hw M) (Dconj hw M .E (Dconj hw M .Fm φ)) := by
    rw [h3]
    exact archDerivAt_rightTranslate_eq_Dconj hw M (isArchSmoothAt_Dconj hw M .Fm hφ) .E
  rw [archCasimirAt, h2, h1, h4]
  funext g
  simp only [Pi.neg_apply, Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, rightTranslate]
  exact casimir_identity hw M hφ (g * archRealGLAt hw M)

theorem package (M : GL (Fin 2) ℝ) (x : AdelicGL2 (𝓞 F) F → ℂ) (hxs : IsArchSmoothAt hw x)
    (hD1 : ∀ d : ArchDir, Continuous (archDerivAt hw d x))
    (hD2 : ∀ d d' : ArchDir, Continuous (archDerivAt hw d (archDerivAt hw d' x))) :
    IsArchSmoothAt hw (rightTranslate F (archRealGLAt hw M) x) ∧
    (∀ d : ArchDir, Continuous (archDerivAt hw d (rightTranslate F (archRealGLAt hw M) x))) ∧
    (∀ d d' : ArchDir, Continuous (archDerivAt hw d (archDerivAt hw d' (rightTranslate F (archRealGLAt hw M) x)))) ∧
    archCasimirAt hw (rightTranslate F (archRealGLAt hw M) x) = rightTranslate F (archRealGLAt hw M) (archCasimirAt hw x) := by
  refine ⟨isArchSmoothAt_rightTranslate hw M hxs, fun d => ?_, fun d d' => ?_, archCasimirAt_rightTranslate hw M hxs⟩
  · rw [archDerivAt_rightTranslate_eq_Dconj hw M hxs]
    exact continuous_rightTranslate (continuous_Dconj hw M d hD1) _
  · rw [archDerivAt_rightTranslate_eq_Dconj hw M hxs, archDerivAt_rightTranslate_eq_Dconj hw M (isArchSmoothAt_Dconj hw M d' hxs)]
    refine continuous_rightTranslate (continuous_Dconj hw M d fun e => ?_) _
    exact continuous_archDerivAt_Dconj hw M d' e hxs hD2

end CasCore17

end

theorem solution
    (K : Type) [Field K] [NumberField K]
    (w : InfinitePlace K) (hw : w.IsReal)
    (x : AdelicGL2 (𝓞 K) K → ℂ) (hxc : Continuous x) (hxs : IsArchSmoothAt hw x)
    (hD1 : ∀ d : ArchDir, Continuous (archDerivAt hw d x))
    (hD2 : ∀ d d' : ArchDir, Continuous (archDerivAt hw d (archDerivAt hw d' x))) :
    ∀ m : GL (Fin 2) ℝ,
        IsArchSmoothAt hw (rightTranslate K (archRealGLAt hw m) x) ∧
        (∀ d : ArchDir, Continuous (archDerivAt hw d (rightTranslate K (archRealGLAt hw m) x))) ∧
        (∀ d d' : ArchDir, Continuous (archDerivAt hw d (archDerivAt hw d'
          (rightTranslate K (archRealGLAt hw m) x)))) ∧
        archCasimirAt hw (rightTranslate K (archRealGLAt hw m) x) =
          rightTranslate K (archRealGLAt hw m) (archCasimirAt hw x) := by
  intro m
  exact CasCore17.package hw m x hxs hD1 hD2

end S_AutomorphicForm_archCasimirAt_rightTranslate_archRealGLAt
end P2MW
export P2MW.S_AutomorphicForm_archCasimirAt_rightTranslate_archRealGLAt (solution)
