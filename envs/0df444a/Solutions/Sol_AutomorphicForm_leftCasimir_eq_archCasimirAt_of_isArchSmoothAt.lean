-- Prove2me | solution 1 for AutomorphicForm.leftCasimir_eq_archCasimirAt_of_isArchSmoothAt
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:05.340288+00:00
-- url     : https://prove2.me/submissions/68e6cfe8-1960-5f1d-bcea-88ee7378d9f8

import Definitions.Def_AutomorphicForm_ProductionPinsGeneral
import Definitions.Def_AutomorphicForm_CuspidalConstituent
import Definitions.Def_AutomorphicForm_ArchDerivCasimir
import Definitions.Def_AutomorphicForm_FactorizableTestFn
import Definitions.Def_AutomorphicForm_RightConvolution
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AutomorphicForm_leftCasimir_eq_archCasimirAt_of_isArchSmoothAt

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

private theorem _root_.CasCore17.isArchSmoothAt_rightTranslate (M : GL (Fin 2) ℝ) {φ : AdelicGL2 (𝓞 F) F → ℂ} (hφ : IsArchSmoothAt hw φ) :
    IsArchSmoothAt hw (rightTranslate F (archRealGLAt hw M) φ) := by
  intro g
  show ContDiffOn ℝ (⊤ : ℕ∞) (chart hw (rightTranslate F (archRealGLAt hw M) φ) g) U
  rw [chart_rightTranslate, ← coe_conjCLM]
  refine (hφ (g * archRealGLAt hw M)).comp (conjCLM M).contDiff.contDiffOn fun e he => ?_
  show (Matrix.of (conjArr M e)).det ≠ 0
  rw [det_conjArr]
  exact he

p2m_export "CasCore17" "isArchSmoothAt_rightTranslate"
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

private theorem _root_.CasCore17.archCasimirAt_rightTranslate (M : GL (Fin 2) ℝ) {φ : AdelicGL2 (𝓞 F) F → ℂ} (hφ : IsArchSmoothAt hw φ) :
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

p2m_export "CasCore17" "archCasimirAt_rightTranslate"

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

namespace CommAway17

open NumberField.InfinitePlace NumberField.InfinitePlace.Completion

variable {F : Type} [Field F] [NumberField F]

section Commuting

variable {w : InfinitePlace F} (hw : w.IsReal) {k : AdelicGL2 (𝓞 F) F}
  (hk : ∀ m : GL (Fin 2) ℝ, archRealGLAt hw m * k = k * archRealGLAt hw m)

include hk

theorem archRealLiftAt_mul_comm (e : Fin 2 → Fin 2 → ℝ) : archRealLiftAt hw e * k = k * archRealLiftAt hw e := by
  unfold archRealLiftAt
  split_ifs
  · exact hk _
  · rw [one_mul, mul_one]

theorem archFlowAt_mul_comm (d : ArchDir) (t : ℝ) : archFlowAt hw d t * k = k * archFlowAt hw d t :=
  hk _

private theorem _root_.CommAway17.isArchSmoothAt_rightTranslate {φ : AdelicGL2 (𝓞 F) F → ℂ} (hφ : IsArchSmoothAt hw φ) :
    IsArchSmoothAt hw (rightTranslate F k φ) := by
  intro g
  show ContDiffOn ℝ (⊤ : ℕ∞) (fun e => φ (g * archRealLiftAt hw e * k)) _
  have hfun : (fun e : Fin 2 → Fin 2 → ℝ => φ (g * archRealLiftAt hw e * k)) =
      fun e => φ (g * k * archRealLiftAt hw e) := by
    funext e
    rw [mul_assoc, archRealLiftAt_mul_comm hw hk e, ← mul_assoc]
  rw [hfun]
  exact hφ (g * k)

p2m_export "CommAway17" "isArchSmoothAt_rightTranslate"
theorem archDerivAt_rightTranslate (d : ArchDir) (φ : AdelicGL2 (𝓞 F) F → ℂ) :
    archDerivAt hw d (rightTranslate F k φ) = rightTranslate F k (archDerivAt hw d φ) := by
  funext g
  show deriv (fun t : ℝ => φ (g * archFlowAt hw d t * k)) 0 = deriv (fun t : ℝ => φ (g * k * archFlowAt hw d t)) 0
  congr 1
  funext t
  rw [mul_assoc, archFlowAt_mul_comm hw hk d t, ← mul_assoc]

private theorem _root_.CommAway17.archCasimirAt_rightTranslate (φ : AdelicGL2 (𝓞 F) F → ℂ) :
    archCasimirAt hw (rightTranslate F k φ) = rightTranslate F k (archCasimirAt hw φ) := by
  rw [archCasimirAt, archCasimirAt, archDerivAt_rightTranslate hw hk .H φ,
    archDerivAt_rightTranslate hw hk .H (archDerivAt hw .H φ), archDerivAt_rightTranslate hw hk .Fm φ,
    archDerivAt_rightTranslate hw hk .E (archDerivAt hw .Fm φ)]
  rfl

p2m_export "CommAway17" "archCasimirAt_rightTranslate"
omit hk in
theorem continuous_rightTranslate {φ : AdelicGL2 (𝓞 F) F → ℂ} (hφ : Continuous φ) (k' : AdelicGL2 (𝓞 F) F) :
    Continuous (rightTranslate F k' φ) :=
  hφ.comp (continuous_id.mul continuous_const)

theorem package (x : AdelicGL2 (𝓞 F) F → ℂ) (hxs : IsArchSmoothAt hw x)
    (hD1 : ∀ d : ArchDir, Continuous (archDerivAt hw d x))
    (hD2 : ∀ d d' : ArchDir, Continuous (archDerivAt hw d (archDerivAt hw d' x))) :
    IsArchSmoothAt hw (rightTranslate F k x) ∧
    (∀ d : ArchDir, Continuous (archDerivAt hw d (rightTranslate F k x))) ∧
    (∀ d d' : ArchDir, Continuous (archDerivAt hw d (archDerivAt hw d' (rightTranslate F k x)))) ∧
    archCasimirAt hw (rightTranslate F k x) = rightTranslate F k (archCasimirAt hw x) := by
  refine ⟨isArchSmoothAt_rightTranslate hw hk hxs, fun d => ?_, fun d d' => ?_, archCasimirAt_rightTranslate hw hk x⟩
  · rw [archDerivAt_rightTranslate hw hk]
    exact continuous_rightTranslate (hD1 d) k
  · rw [archDerivAt_rightTranslate hw hk, archDerivAt_rightTranslate hw hk]
    exact continuous_rightTranslate (hD2 d d') k

end Commuting

theorem archRealGLAt_mul_rowIsometryInclAt₀_comm {w w' : InfinitePlace F} (hw : w.IsReal) (hne : w' ≠ w)
    (k : rowIsometrySubgroup₀ w'.Completion) (m : GL (Fin 2) ℝ) :
    archRealGLAt hw m * rowIsometryInclAt₀ F w' k = rowIsometryInclAt₀ F w' k * archRealGLAt hw m := by
  rw [rowIsometryInclAt₀_apply]
  show adelicArchGLInclAt F w _ * adelicArchGLInclAt F w' _ = adelicArchGLInclAt F w' _ * adelicArchGLInclAt F w _
  exact (commute_adelicArchGLInclAt_of_ne F (Ne.symm hne) _ _).eq

end CommAway17

namespace Elem17LR

open NumberField.InfinitePlace NumberField.InfinitePlace.Completion

variable {F : Type} [Field F] [NumberField F]

omit [NumberField F] in
theorem glArch_ext {x y : GL (Fin 2) (InfiniteAdeleRing F)}
    (h : ∀ w : InfinitePlace F, archComponent F w x = archComponent F w y) : x = y := by
  refine Matrix.GeneralLinearGroup.ext fun i j => funext fun w => ?_
  exact congrArg (fun g : GL (Fin 2) w.Completion => (g : Matrix (Fin 2) (Fin 2) w.Completion) i j) (h w)

theorem glArch_archRealGLAt {w : InfinitePlace F} (hw : w.IsReal) (m : GL (Fin 2) ℝ) :
    glArch (𝓞 F) F (archRealGLAt hw m) = archGLIncl F w (glEquivOfRingEquiv (ringEquivRealOfIsReal hw).symm m) :=
  glArch_adelicArchGLIncl F _

theorem archComponent_glArch_archRealGLAt_self {w : InfinitePlace F} (hw : w.IsReal) (m : GL (Fin 2) ℝ) :
    archComponent F w (glArch (𝓞 F) F (archRealGLAt hw m)) =
      glEquivOfRingEquiv (ringEquivRealOfIsReal hw).symm m := by
  rw [glArch_archRealGLAt, archComponent_archGLIncl_self]

theorem archComponent_glArch_archRealGLAt_of_ne {w w' : InfinitePlace F} (hw : w.IsReal) (hw' : w' ≠ w)
    (m : GL (Fin 2) ℝ) : archComponent F w' (glArch (𝓞 F) F (archRealGLAt hw m)) = 1 := by
  rw [glArch_archRealGLAt, archComponent_archGLIncl_of_ne F hw']

theorem glFin_archRealGLAt {w : InfinitePlace F} (hw : w.IsReal) (m : GL (Fin 2) ℝ) :
    glFin (𝓞 F) F (archRealGLAt hw m) = 1 :=
  glFin_adelicArchGLIncl F _

theorem archRealGLAt_mul_comm_of_archComponent_eq_one {w : InfinitePlace F} (hw : w.IsReal) (m : GL (Fin 2) ℝ)
    {g : AdelicGL2 (𝓞 F) F} (hg : archComponent F w (glArch (𝓞 F) F g) = 1) :
    archRealGLAt hw m * g = g * archRealGLAt hw m := by
  apply eq_of_glArch_eq_of_glFin_eq
  · rw [map_mul, map_mul]
    apply glArch_ext
    intro w'
    rw [map_mul, map_mul]
    by_cases hw' : w' = w
    · subst hw'; rw [hg, mul_one, one_mul]
    · rw [archComponent_glArch_archRealGLAt_of_ne hw hw', one_mul, mul_one]
  · rw [map_mul, map_mul, glFin_archRealGLAt, one_mul, mul_one]

end Elem17LR

namespace CasLR17

open NumberField.InfinitePlace NumberField.InfinitePlace.Completion Matrix CasCore17

variable {F : Type} [Field F] [NumberField F] {w : InfinitePlace F} (hw : w.IsReal)

def Ld (d : ArchDir) (θ : AdelicGL2 (𝓞 F) F → ℂ) (y : AdelicGL2 (𝓞 F) F) : ℂ :=
  deriv (fun t : ℝ => θ (archFlowAt hw d (-t) * y)) 0

omit hw in
theorem hasDerivAt_negflow_mul_const (d : ArchDir) (X : Matrix (Fin 2) (Fin 2) ℝ) :
    HasDerivAt (fun t : ℝ => Matrix.of.symm ((archFlowMatrix d (-t) : Matrix (Fin 2) (Fin 2) ℝ) * X))
      (Matrix.of.symm (-(archDirMatrix d * X))) 0 := by
  rw [hasDerivAt_pi]
  intro i
  rw [hasDerivAt_pi]
  intro j
  simp only [Matrix.of_symm_apply, Matrix.mul_apply, Matrix.neg_apply]
  rw [← Finset.sum_neg_distrib]
  refine HasDerivAt.fun_sum fun k _ => ?_
  have h := ((hasDerivAt_archFlowMatrix_apply d i k).comp_of_eq (0 : ℝ) (hasDerivAt_neg (0 : ℝ)) neg_zero.symm).mul_const (X k j)
  simpa using h

omit hw in
theorem hasDerivAt_const_mul_negflow (d : ArchDir) (X : Matrix (Fin 2) (Fin 2) ℝ) :
    HasDerivAt (fun t : ℝ => Matrix.of.symm (X * (archFlowMatrix d (-t) : Matrix (Fin 2) (Fin 2) ℝ)))
      (Matrix.of.symm (-(X * archDirMatrix d))) 0 := by
  rw [hasDerivAt_pi]
  intro i
  rw [hasDerivAt_pi]
  intro j
  simp only [Matrix.of_symm_apply, Matrix.mul_apply, Matrix.neg_apply]
  rw [← Finset.sum_neg_distrib]
  refine HasDerivAt.fun_sum fun k _ => ?_
  have h := ((hasDerivAt_archFlowMatrix_apply d k j).comp_of_eq (0 : ℝ) (hasDerivAt_neg (0 : ℝ)) neg_zero.symm).const_mul (X i k)
  simpa using h

theorem negflow_mul_lift (d : ArchDir) (t : ℝ) {e : Fin 2 → Fin 2 → ℝ} (he : (Matrix.of e).det ≠ 0) :
    archFlowAt hw d (-t) * archRealLiftAt hw e =
      1 * archRealLiftAt hw (Matrix.of.symm ((archFlowMatrix d (-t) : Matrix (Fin 2) (Fin 2) ℝ) * Matrix.of e)) := by
  rw [one_mul, archFlowAt, archRealGLAt_mul_archRealLiftAt hw _ he]

theorem Ld_apply_lift {θ : AdelicGL2 (𝓞 F) F → ℂ} (hθ : IsArchSmoothAt hw θ) (d : ArchDir)
    {e : Fin 2 → Fin 2 → ℝ} (he : (Matrix.of e).det ≠ 0) :
    Ld hw d θ (archRealLiftAt hw e) = fderiv ℝ (chart hw θ 1) e (Matrix.of.symm (-(archDirMatrix d * Matrix.of e))) := by
  have hfun : (fun t : ℝ => θ (archFlowAt hw d (-t) * archRealLiftAt hw e)) =
      fun t => chart hw θ 1 (Matrix.of.symm ((archFlowMatrix d (-t) : Matrix (Fin 2) (Fin 2) ℝ) * Matrix.of e)) := by
    funext t
    rw [negflow_mul_lift hw d t he]
    rfl
  have h0 : Matrix.of.symm ((archFlowMatrix d (-0) : Matrix (Fin 2) (Fin 2) ℝ) * Matrix.of e) = e := by
    rw [neg_zero, archFlowMatrix_zero, Units.val_one, Matrix.one_mul, Equiv.symm_apply_apply]
  have hdiff : HasFDerivAt (chart hw θ 1) (fderiv ℝ (chart hw θ 1) e)
      (Matrix.of.symm ((archFlowMatrix d (-0) : Matrix (Fin 2) (Fin 2) ℝ) * Matrix.of e)) := by
    rw [h0]; exact hasFDerivAt_chart hw hθ 1 he
  show deriv (fun t : ℝ => θ (archFlowAt hw d (-t) * archRealLiftAt hw e)) 0 = _
  rw [hfun]
  exact (hdiff.comp_hasDerivAt (0 : ℝ) (hasDerivAt_negflow_mul_const d (Matrix.of e))).deriv

theorem Ld_one {θ : AdelicGL2 (𝓞 F) F → ℂ} (hθ : IsArchSmoothAt hw θ) (d : ArchDir) :
    Ld hw d θ 1 = -archDerivAt hw d θ 1 := by
  have h := Ld_apply_lift hw hθ d (e := Matrix.of.symm 1) one_mem_U
  rw [archRealLiftAt_of_symm_one, Equiv.apply_symm_apply, Matrix.mul_one] at h
  rw [h, archDerivAt_eq_D1 hw hθ, D1]
  show fderiv ℝ (chart hw θ 1) (Matrix.of.symm 1) (-Matrix.of.symm (archDirMatrix d)) = _
  rw [map_neg]

theorem Ld_Ld_one {θ : AdelicGL2 (𝓞 F) F → ℂ} (hθ : IsArchSmoothAt hw θ) (i j : ArchDir) :
    Ld hw i (Ld hw j θ) 1 = D2 hw θ 1 (archDirMatrix i) (archDirMatrix j) + D1 hw θ 1 (archDirMatrix j * archDirMatrix i) := by
  have hfun : (fun t : ℝ => Ld hw j θ (archFlowAt hw i (-t) * 1)) =
      fun t => (fderiv ℝ (chart hw θ 1) (Matrix.of.symm ((archFlowMatrix i (-t) : Matrix (Fin 2) (Fin 2) ℝ))))
        (Matrix.of.symm (-(archDirMatrix j * (archFlowMatrix i (-t) : Matrix (Fin 2) (Fin 2) ℝ)))) := by
    funext t
    have hdet : (Matrix.of (Matrix.of.symm ((archFlowMatrix i (-t) : Matrix (Fin 2) (Fin 2) ℝ)))).det ≠ 0 := by
      rw [Equiv.apply_symm_apply]
      exact ((Matrix.isUnit_iff_isUnit_det _).1 (archFlowMatrix i (-t)).isUnit).ne_zero
    rw [mul_one, archFlowAt, archRealGLAt_eq_archRealLiftAt, Ld_apply_lift hw hθ j hdet, Equiv.apply_symm_apply]
  have hchart : ContDiffAt ℝ (⊤ : ℕ∞) (chart hw θ 1) (Matrix.of.symm 1) := contDiffAt_chart hw hθ 1 one_mem_U
  have hA0 : HasFDerivAt (fderiv ℝ (chart hw θ 1)) (fderiv ℝ (fderiv ℝ (chart hw θ 1)) (Matrix.of.symm 1))
      (Matrix.of.symm 1) :=
    ((hchart.fderiv_right (m := 2) (by norm_cast)).differentiableAt (by simp)).hasFDerivAt
  have hγ : HasDerivAt (fun t : ℝ => Matrix.of.symm ((archFlowMatrix i (-t) : Matrix (Fin 2) (Fin 2) ℝ)))
      (Matrix.of.symm (-archDirMatrix i)) 0 := by
    have h := hasDerivAt_negflow_mul_const i (1 : Matrix (Fin 2) (Fin 2) ℝ)
    simp only [Matrix.mul_one] at h
    exact h
  have hγ0 : Matrix.of.symm ((archFlowMatrix i (-0) : Matrix (Fin 2) (Fin 2) ℝ)) = Matrix.of.symm 1 := by
    rw [neg_zero, archFlowMatrix_zero, Units.val_one]
  have hA : HasDerivAt (fun t : ℝ => fderiv ℝ (chart hw θ 1) (Matrix.of.symm ((archFlowMatrix i (-t) : Matrix (Fin 2) (Fin 2) ℝ))))
      (fderiv ℝ (fderiv ℝ (chart hw θ 1)) (Matrix.of.symm 1) (Matrix.of.symm (-archDirMatrix i))) 0 :=
    hA0.comp_hasDerivAt_of_eq (0 : ℝ) hγ hγ0.symm
  have hv : HasDerivAt (fun t : ℝ => Matrix.of.symm (-(archDirMatrix j * (archFlowMatrix i (-t) : Matrix (Fin 2) (Fin 2) ℝ))))
      (Matrix.of.symm (archDirMatrix j * archDirMatrix i)) 0 := by
    have h := (hasDerivAt_const_mul_negflow i (archDirMatrix j)).neg
    convert h using 1
    all_goals first | rfl | exact (neg_neg _).symm
  have h := hA.clm_apply hv
  show deriv (fun t : ℝ => Ld hw j θ (archFlowAt hw i (-t) * 1)) 0 = _
  rw [hfun, h.deriv]
  simp only [neg_zero, archFlowMatrix_zero, Units.val_one, Matrix.mul_one, D2, D1]
  have e1 : (fderiv ℝ (fderiv ℝ (chart hw θ 1)) (Matrix.of.symm 1)) (Matrix.of.symm (-archDirMatrix i)) =
      -((fderiv ℝ (fderiv ℝ (chart hw θ 1)) (Matrix.of.symm 1)) (Matrix.of.symm (archDirMatrix i))) := map_neg _ _
  have e2 : ((fderiv ℝ (fderiv ℝ (chart hw θ 1)) (Matrix.of.symm 1)) (Matrix.of.symm (archDirMatrix i))) (Matrix.of.symm (-archDirMatrix j)) =
      -(((fderiv ℝ (fderiv ℝ (chart hw θ 1)) (Matrix.of.symm 1)) (Matrix.of.symm (archDirMatrix i))) (Matrix.of.symm (archDirMatrix j))) :=
    map_neg _ _
  rw [e1, ContinuousLinearMap.neg_apply, e2, neg_neg]

theorem leftCasimir_one {θ : AdelicGL2 (𝓞 F) F → ℂ} (hθ : IsArchSmoothAt hw θ) :
    -((1 / 4 : ℂ) * Ld hw .H (Ld hw .H θ) 1 - (1 / 2 : ℂ) * Ld hw .H θ 1 + Ld hw .E (Ld hw .Fm θ) 1) = archCasimirAt hw θ 1 := by
  rw [Ld_Ld_one hw hθ, Ld_Ld_one hw hθ, Ld_one hw hθ]
  have h1 := archDerivAt_archDerivAt_eq hw hθ .H .H 1
  have h2 := archDerivAt_archDerivAt_eq hw hθ .E .Fm 1
  have h3 : D1 hw θ 1 (archDirMatrix .Fm * archDirMatrix .E) = D1 hw θ 1 (archDirMatrix .E * archDirMatrix .Fm) - archDerivAt hw .H θ 1 := by
    have hb : archDirMatrix .Fm * archDirMatrix .E = archDirMatrix .E * archDirMatrix .Fm - (1 : ℝ) • archDirMatrix .H := by
      rw [← bracket_E_Fm]; abel
    rw [hb, D1_sub, D1_smul, ← archDerivAt_eq_D1 hw hθ]
    push_cast
    ring
  show _ = (-((1 / 4 : ℂ) • archDerivAt hw .H (archDerivAt hw .H θ) - (1 / 2 : ℂ) • archDerivAt hw .H θ +
    archDerivAt hw .E (archDerivAt hw .Fm θ))) 1
  simp only [Pi.neg_apply, Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
  rw [h1, h2, h3]
  ring

omit hw in
theorem rightTranslate_mul (a b : AdelicGL2 (𝓞 F) F) (θ : AdelicGL2 (𝓞 F) F → ℂ) :
    rightTranslate F (a * b) θ = rightTranslate F a (rightTranslate F b θ) := by
  funext z
  simp only [rightTranslate, mul_assoc]

theorem Ld_rightTranslate (d : ArchDir) (θ : AdelicGL2 (𝓞 F) F → ℂ) (y : AdelicGL2 (𝓞 F) F) :
    Ld hw d (rightTranslate F y θ) = rightTranslate F y (Ld hw d θ) := by
  funext z
  simp only [Ld, rightTranslate, mul_assoc]

theorem exists_decomp (y : AdelicGL2 (𝓞 F) F) :
    ∃ (m : GL (Fin 2) ℝ) (y' : AdelicGL2 (𝓞 F) F), archComponent F w (glArch (𝓞 F) F y') = 1 ∧ y = archRealGLAt hw m * y' := by
  set m : GL (Fin 2) ℝ := (glEquivOfRingEquiv (ringEquivRealOfIsReal hw).symm).symm (archComponent F w (glArch (𝓞 F) F y)) with hm
  refine ⟨m, (archRealGLAt hw m)⁻¹ * y, ?_, by rw [mul_inv_cancel_left]⟩
  rw [map_mul, map_mul, map_inv, map_inv, Elem17LR.archComponent_glArch_archRealGLAt_self, hm, MulEquiv.apply_symm_apply,
    inv_mul_cancel]

theorem archCasimirAt_rightTranslate_any (y : AdelicGL2 (𝓞 F) F) {θ : AdelicGL2 (𝓞 F) F → ℂ} (hθ : IsArchSmoothAt hw θ) :
    archCasimirAt hw (rightTranslate F y θ) = rightTranslate F y (archCasimirAt hw θ) := by
  obtain ⟨m, y', hy', rfl⟩ := exists_decomp hw y
  have hk : ∀ M : GL (Fin 2) ℝ, archRealGLAt hw M * y' = y' * archRealGLAt hw M :=
    fun M => Elem17LR.archRealGLAt_mul_comm_of_archComponent_eq_one hw M hy'
  rw [rightTranslate_mul, rightTranslate_mul, CasCore17.archCasimirAt_rightTranslate hw m (CommAway17.isArchSmoothAt_rightTranslate hw hk hθ),
    CommAway17.archCasimirAt_rightTranslate hw hk]

theorem isArchSmoothAt_rightTranslate_any (y : AdelicGL2 (𝓞 F) F) {θ : AdelicGL2 (𝓞 F) F → ℂ} (hθ : IsArchSmoothAt hw θ) :
    IsArchSmoothAt hw (rightTranslate F y θ) := by
  obtain ⟨m, y', hy', rfl⟩ := exists_decomp hw y
  have hk : ∀ M : GL (Fin 2) ℝ, archRealGLAt hw M * y' = y' * archRealGLAt hw M :=
    fun M => Elem17LR.archRealGLAt_mul_comm_of_archComponent_eq_one hw M hy'
  rw [rightTranslate_mul]
  exact CasCore17.isArchSmoothAt_rightTranslate hw m (CommAway17.isArchSmoothAt_rightTranslate hw hk hθ)

theorem leftCasimir_eq {θ : AdelicGL2 (𝓞 F) F → ℂ} (hθ : IsArchSmoothAt hw θ) (y : AdelicGL2 (𝓞 F) F) :
    -((1 / 4 : ℂ) * Ld hw .H (Ld hw .H θ) y - (1 / 2 : ℂ) * Ld hw .H θ y + Ld hw .E (Ld hw .Fm θ) y) = archCasimirAt hw θ y := by
  have h := leftCasimir_one hw (isArchSmoothAt_rightTranslate_any hw y hθ)
  rw [Ld_rightTranslate, Ld_rightTranslate, Ld_rightTranslate, Ld_rightTranslate, archCasimirAt_rightTranslate_any hw y hθ] at h
  simpa only [rightTranslate, one_mul] using h

end CasLR17

end

theorem solution
    (K : Type) [Field K] [NumberField K]
    (w : InfinitePlace K) (hw : w.IsReal)
    (θ : AdelicGL2 (𝓞 K) K → ℂ) (hθ : IsArchSmoothAt hw θ) :
    let L : ArchDir → (AdelicGL2 (𝓞 K) K → ℂ) → (AdelicGL2 (𝓞 K) K → ℂ) :=
      fun d γ y => deriv (fun t : ℝ => γ (archFlowAt hw d (-t) * y)) 0
    ∀ y : AdelicGL2 (𝓞 K) K,
      -((1 / 4 : ℂ) * L .H (L .H θ) y - (1 / 2 : ℂ) * L .H θ y + L .E (L .Fm θ) y) = archCasimirAt hw θ y := by
  intro L y
  exact CasLR17.leftCasimir_eq hw hθ y

end S_AutomorphicForm_leftCasimir_eq_archCasimirAt_of_isArchSmoothAt
end P2MW
export P2MW.S_AutomorphicForm_leftCasimir_eq_archCasimirAt_of_isArchSmoothAt (solution)
