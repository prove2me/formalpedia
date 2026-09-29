-- Prove2me | solution 1 for AutomorphicForm.archOccursInClassOf_isArchLoweringAnnihilatedAt_of_not_archOccursInClassOf_archWeightChar_sub_two_of_coversModCentre_of_pos
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.553648+00:00
-- url     : https://prove2.me/submissions/8d9fdaf7-be8e-53ea-ac39-d02e092d8b15

import Mathlib
import Definitions.Def_AutomorphicForm_TranslateSpanOccurrence
import Definitions.Def_AutomorphicForm_ArchLoweringAnnihilated
import Definitions.Def_AutomorphicForm_ArchDerivCasimir
import Definitions.Def_AutomorphicForm_BoundedGenuineCuspRealization
import Definitions.Def_AutomorphicForm_IsotypicCuspSpace
import Theorems.Thm_AutomorphicForm_exists_isFactorizableTestFn_hasArchCharacterAt_rightConv_ne_zero_of_hasArchCharacterAt
import Theorems.Thm_AutomorphicForm_isCuspidalFn_isKfSmooth_levelInvariant_isHeckeCosetEigenfunctionAt_rightConv_of_isFactorizableTestFn_of_support_subset
import Theorems.Thm_AutomorphicForm_isBoundedOnSiegelWindows_rightConv_of_isCuspAutomorphicFnAt_of_coversModCentre
import Theorems.Thm_AutomorphicForm_continuous_rightConv_and_contDiff_of_isFactorizableTestFn
import Theorems.Thm_AutomorphicForm_continuous_and_hasCompactSupport_of_isFactorizableTestFn
import Theorems.Thm_AutomorphicForm_archDerivAt_rightConv_eq_rightConv_deriv_of_isFactorizableTestFn
import Theorems.Thm_AutomorphicForm_lowering_fderiv_mul_rotation_eq_exp_mul_of_weight
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

p2m_attr_erase "ext" "IsDedekindDomain.HeightOneSpectrum.adicCompletion.ext"
p2m_attr_erase "ext" "NumberField.InfinitePlace.Completion.ext"
namespace P2MW.S_AutomorphicForm_archOccursInClassOf_isArchLoweringAnnihilatedAt_of_not_archOccursInClassOf_archWeightChar_sub_two_of_coversModCentre_of_pos
p2m_attr_erase "instance" "RestrictedProduct.SecondCountableTopology_of_principal instCountableElemSetSetsCofinite_definitions instCountableOfNumberField_definitions"
p2m_attr_erase "simp" "ContinuousAddEquiv.restrictedProductPi_apply RestrictedProduct.flatten_homeomorph_apply RestrictedProduct.flatten_homeomorph'_symm_apply ContinuousMulEquiv.restrictedProductPi_symm_apply RestrictedProduct.flatten_homeomorph'_apply RestrictedProduct.flatten_homeomorph_symm_apply ContinuousMulEquiv.restrictedProductPi_apply ContinuousAddEquiv.restrictedProductPi_symm_apply RingEquiv.restrictedProductCongr_symm_apply RingEquiv.restrictedProductCongrRight_apply MulEquiv.restrictedProductCongrRight_apply Equiv.restrictedProductProd_symm_apply_coe Equiv.restrictedProductCongrRight_apply AddEquiv.restrictedProductCongr_apply Equiv.restrictedProductCongrLeft'_symm_apply_apply Equiv.restrictedProductCongr_apply_apply Equiv.restrictedProductCongrLeft_apply_apply RestrictedProduct.flatten_equiv'_apply AddEquiv.restrictedProductCongrRight_apply Equiv.restrictedProductCongr_symm_apply Equiv.restrictedProductCongrRight_symm_apply RestrictedProduct.flatten_equiv'_symm_apply AddEquiv.restrictedProductCongrLeft'_apply Equiv.restrictedProductCongrLeft'_apply RestrictedProduct.flatten_apply RingEquiv.restrictedProductCongr_apply_apply RingEquiv.restrictedProductCongrLeft'_apply Equiv.restrictedProductProd_apply RestrictedProduct.flatten_equiv_apply RestrictedProduct.flatten_equiv_symm_apply LinearEquiv.restrictedProductCongrLeft'_apply RestrictedProduct.not_mem_support RestrictedProduct.mem_structureSubring_iff RestrictedProduct.not_mem_mulSupport RestrictedProduct.support_neg RestrictedProduct.mem_indexSupport_iff RestrictedProduct.mulSupport_inv RestrictedProduct.mapAlongLinearMap_apply"

set_option autoImplicit false

p2m_open "NumberField NumberField.AdelicLevel NumberField.AdelicBox NumberField.AdelicHaar NumberField.AdelicVolume MeasureTheory AutomorphicForm P2MW.S_AutomorphicForm_archOccursInClassOf_isArchLoweringAnnihilatedAt_of_not_archOccursInClassOf_archWeightChar_sub_two_of_coversModCentre_of_pos.AutomorphicForm AutomorphicForm.WindowedSiegel AutomorphicForm.SiegelCovering AutomorphicForm.SmoothCusp NumberField.InfinitePlace NumberField.InfinitePlace.Completion"

open scoped Classical

noncomputable section

namespace AutomorphicForm
p2m_export "AutomorphicForm" "ArchOccursInClassOf SmoothCuspRealizationAt finiteAdelicGL2Subgroup lsXiMemberAt_iff CarrierPins productionPinsOf AdelicGL2 centralScalar HeckeEigensystem glEquivOfRingEquiv rowIsometrySubgroup₀Map norm_ringEquivRealOfIsReal rowIsometrySubgroup₀ mem_rowIsometrySubgroup₀_iff entries_of_mem_rowIsometrySubgroup₀ archWeightOneℝ archWeightCharℝ HasArchCharacterAt₀ adelicArchGLInclAt glFin_adelicArchGLIncl adelicGLHaar_mul_right_centreCutSiegelSet_lt_top IsGenuineCuspRealizationAt loweringAt archSliceAt archSliceAt_apply_of_det_ne_zero IsArchLoweringAnnihilatedAt archRealGLAt archRealLiftAt archRealLiftAt_of_det_ne_zero isOpen_setOf_det_ne_zero IsArchSmoothAt ArchDir archFlowMatrix archFlowAt archFlowAt_zero archFlowAt_add archDerivAt archDirMatrix archRealLiftAt_mul_archRealGLAt hasDerivAt_of_symm_mul_archFlowMatrix of_symm_mul_archFlowMatrix_zero archRealLiftAt_of_symm_one rightConv rightConv_apply rightConv_comp_mul_left exists_isFactorizableTestFn_hasArchCharacterAt_rightConv_ne_zero_of_hasArchCharacterAt IsArchTestFactor IsFactorizableTestFn isCuspidalFn_isKfSmooth_levelInvariant_isHeckeCosetEigenfunctionAt_rightConv_of_isFactorizableTestFn_of_support_subset isBoundedOnSiegelWindows_rightConv_of_isCuspAutomorphicFnAt_of_coversModCentre continuous_rightConv_and_contDiff_of_isFactorizableTestFn continuous_and_hasCompactSupport_of_isFactorizableTestFn archDerivAt_rightConv_eq_rightConv_deriv_of_isFactorizableTestFn lowering_fderiv_mul_rotation_eq_exp_mul_of_weight"
p2m_open "AutomorphicForm"

namespace LowerEdgePos

def rotMat (θ : ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  !![Real.cos θ, Real.sin θ; -Real.sin θ, Real.cos θ]

theorem det_rotMat (θ : ℝ) : (rotMat θ).det = 1 := by
  have h : Real.cos θ * Real.cos θ + Real.sin θ * Real.sin θ = 1 := by
    rw [← sq, ← sq]; exact Real.cos_sq_add_sin_sq θ
  simp [rotMat, Matrix.det_fin_two]
  linarith

def rotGL (θ : ℝ) : GL (Fin 2) ℝ :=
  Matrix.GeneralLinearGroup.mkOfDetNeZero (rotMat θ) (by rw [det_rotMat]; exact one_ne_zero)

theorem rotGL_coe (θ : ℝ) : ((rotGL θ : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) = rotMat θ := rfl

theorem rotGL_mem (θ : ℝ) : rotGL θ ∈ rowIsometrySubgroup₀ ℝ := by
  rw [mem_rowIsometrySubgroup₀_iff]
  refine ⟨det_rotMat θ, ?_, ?_⟩
  · rw [rotGL_coe, det_rotMat, norm_one]
  · intro x y
    have h00 : ((rotGL θ : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) 0 0 = Real.cos θ := rfl
    have h01 : ((rotGL θ : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) 0 1 = Real.sin θ := rfl
    have h10 : ((rotGL θ : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) 1 0 = -Real.sin θ := rfl
    have h11 : ((rotGL θ : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) 1 1 = Real.cos θ := rfl
    rw [h00, h01, h10, h11, Real.norm_eq_abs, Real.norm_eq_abs, Real.norm_eq_abs, Real.norm_eq_abs,
      sq_abs, sq_abs, sq_abs, sq_abs]
    linear_combination (x ^ 2 + y ^ 2) * Real.cos_sq_add_sin_sq θ

def rotSO (θ : ℝ) : rowIsometrySubgroup₀ ℝ := ⟨rotGL θ, rotGL_mem θ⟩

theorem archWeightOneℝ_rotSO (θ : ℝ) :
    ((archWeightOneℝ (rotSO θ) : ℂˣ) : ℂ) = ⟨Real.cos θ, Real.sin θ⟩ := rfl

theorem archWeightOneℝ_rotSO_eq_exp (θ : ℝ) :
    ((archWeightOneℝ (rotSO θ) : ℂˣ) : ℂ) = Complex.exp (θ * Complex.I) := by
  rw [archWeightOneℝ_rotSO, Complex.exp_mul_I]
  apply Complex.ext <;>
    simp [Complex.cos_ofReal_re, Complex.sin_ofReal_re, Complex.cos_ofReal_im,
      Complex.sin_ofReal_im]

theorem archWeightCharℝ_rotSO_eq_exp (k : ℤ) (θ : ℝ) :
    ((archWeightCharℝ k (rotSO θ) : ℂˣ) : ℂ) = Complex.exp (Complex.I * k * θ) := by
  rw [archWeightCharℝ, MonoidHom.comp_apply, zpowGroupHom_apply, Units.val_zpow_eq_zpow_val,
    archWeightOneℝ_rotSO_eq_exp, ← Complex.exp_int_mul]
  congr 1
  ring

theorem rotSO_surjective : Function.Surjective rotSO := by
  intro k
  obtain ⟨h10, h11, hab⟩ := entries_of_mem_rowIsometrySubgroup₀ k.2
  set a : ℝ := ((k : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) 0 0 with ha
  set b : ℝ := ((k : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) 0 1 with hb
  set z : ℂ := ⟨a, b⟩ with hz
  have hnorm : ‖z‖ = 1 := by
    have : Complex.normSq z = 1 := by
      rw [hz, Complex.normSq_mk]
      nlinarith [hab]
    have h2 : ‖z‖ ^ 2 = 1 := by rw [← Complex.normSq_eq_norm_sq]; exact this
    have h3 : 0 ≤ ‖z‖ := norm_nonneg z
    nlinarith [h2, h3]
  have hz0 : z ≠ 0 := by
    intro h
    rw [h, norm_zero] at hnorm
    exact zero_ne_one hnorm
  refine ⟨Complex.arg z, ?_⟩
  have hc : Real.cos (Complex.arg z) = a := by rw [Complex.cos_arg hz0, hnorm, div_one]
  have hs : Real.sin (Complex.arg z) = b := by rw [Complex.sin_arg, hnorm, div_one]
  apply Subtype.ext
  apply Units.ext
  change rotMat (Complex.arg z) = ((k : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ)
  rw [Matrix.eta_fin_two ((k : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ), ← ha, ← hb, h10, h11,
    rotMat, hc, hs]

section Transport

variable (F : Type) [Field F] [NumberField F]

def rotAt {w : InfinitePlace F} (hw : w.IsReal)
    (he : ∀ x : ℝ, ‖(ringEquivRealOfIsReal hw).symm x‖ = ‖x‖) (θ : ℝ) :
    rowIsometrySubgroup₀ w.Completion :=
  rowIsometrySubgroup₀Map (ringEquivRealOfIsReal hw).symm he (rotSO θ)

omit [NumberField F] in
theorem norm_symm_ringEquivRealOfIsReal {w : InfinitePlace F} (hw : w.IsReal) (x : ℝ) :
    ‖(ringEquivRealOfIsReal hw).symm x‖ = ‖x‖ := by
  have := norm_ringEquivRealOfIsReal hw ((ringEquivRealOfIsReal hw).symm x)
  rw [RingEquiv.apply_symm_apply] at this
  exact this.symm

variable {F}

omit [NumberField F] in
theorem rowIsometrySubgroup₀Map_rotAt {w : InfinitePlace F} (hw : w.IsReal)
    (he : ∀ x : ℝ, ‖(ringEquivRealOfIsReal hw).symm x‖ = ‖x‖) (θ : ℝ) :
    rowIsometrySubgroup₀Map (ringEquivRealOfIsReal hw) (norm_ringEquivRealOfIsReal hw)
      (rotAt F hw he θ) = rotSO θ := by
  apply Subtype.ext
  apply Units.ext
  ext i j
  change (ringEquivRealOfIsReal hw) ((ringEquivRealOfIsReal hw).symm (rotMat θ i j)) = rotMat θ i j
  exact RingEquiv.apply_symm_apply _ _

omit [NumberField F] in

theorem rotAt_surjective {w : InfinitePlace F} (hw : w.IsReal)
    (he : ∀ x : ℝ, ‖(ringEquivRealOfIsReal hw).symm x‖ = ‖x‖) (κ : rowIsometrySubgroup₀ w.Completion) :
    ∃ θ : ℝ, rotAt F hw he θ = κ := by
  obtain ⟨θ, hθ⟩ := rotSO_surjective
    (rowIsometrySubgroup₀Map (ringEquivRealOfIsReal hw) (norm_ringEquivRealOfIsReal hw) κ)
  refine ⟨θ, ?_⟩
  apply Subtype.ext
  apply Units.ext
  ext i j
  change (ringEquivRealOfIsReal hw).symm (((rotSO θ : rowIsometrySubgroup₀ ℝ) : GL (Fin 2) ℝ) i j) = _
  rw [hθ]
  exact RingEquiv.symm_apply_apply _ _

omit [NumberField F] in

theorem weightChar_rotAt {w : InfinitePlace F} (hw : w.IsReal)
    (he : ∀ x : ℝ, ‖(ringEquivRealOfIsReal hw).symm x‖ = ‖x‖) (k : ℤ) (θ : ℝ) :
    ((((archWeightCharℝ k).comp (rowIsometrySubgroup₀Map (ringEquivRealOfIsReal hw)
        (norm_ringEquivRealOfIsReal hw))) (rotAt F hw he θ) : ℂˣ) : ℂ)
      = Complex.exp (Complex.I * k * θ) := by
  rw [MonoidHom.comp_apply, rowIsometrySubgroup₀Map_rotAt, archWeightCharℝ_rotSO_eq_exp]

theorem archRealGLAt_rotGL {w : InfinitePlace F} (hw : w.IsReal)
    (he : ∀ x : ℝ, ‖(ringEquivRealOfIsReal hw).symm x‖ = ‖x‖) (θ : ℝ) :
    archRealGLAt hw (rotGL θ) =
      adelicArchGLInclAt F w ((rotAt F hw he θ : rowIsometrySubgroup₀ w.Completion) : GL (Fin 2) w.Completion) :=
  rfl

theorem archRealLiftAt_rotMat {w : InfinitePlace F} (hw : w.IsReal)
    (he : ∀ x : ℝ, ‖(ringEquivRealOfIsReal hw).symm x‖ = ‖x‖) (θ : ℝ) :
    archRealLiftAt hw (rotMat θ) =
      adelicArchGLInclAt F w ((rotAt F hw he θ : rowIsometrySubgroup₀ w.Completion) : GL (Fin 2) w.Completion) := by
  have hdet : (Matrix.of (rotMat θ : Fin 2 → Fin 2 → ℝ)).det ≠ 0 := by
    change (rotMat θ).det ≠ 0
    rw [det_rotMat]; exact one_ne_zero
  rw [archRealLiftAt_of_det_ne_zero hw hdet, ← archRealGLAt_rotGL hw he]
  congr 1

end Transport

section Lift

variable {F : Type} [Field F] [NumberField F]

theorem archRealLiftAt_eq_incl {w : InfinitePlace F} (hw : w.IsReal) {e : Fin 2 → Fin 2 → ℝ}
    (h : (Matrix.of e).det ≠ 0) :
    archRealLiftAt hw e =
      adelicArchGLInclAt F w
        (Matrix.GeneralLinearGroup.map (ringEquivRealOfIsReal hw).symm.toRingHom
          (Matrix.GeneralLinearGroup.mkOfDetNeZero (Matrix.of e) h)) := by
  rw [archRealLiftAt_of_det_ne_zero hw h]
  change adelicArchGLInclAt F w (glEquivOfRingEquiv (ringEquivRealOfIsReal hw).symm
    (Matrix.GeneralLinearGroup.mkOfDetNeZero (Matrix.of e) h)) = _
  congr 1

theorem archSliceAt_eq_of_det_ne_zero {w : InfinitePlace F} (hw : w.IsReal)
    (φ : AdelicGL2 (𝓞 F) F → ℂ) (g : AdelicGL2 (𝓞 F) F) {e : Fin 2 → Fin 2 → ℝ}
    (h : (Matrix.of e).det ≠ 0) :
    archSliceAt w hw φ g e = φ (g * archRealLiftAt hw e) := by
  rw [archSliceAt_apply_of_det_ne_zero w hw φ g e h, archRealLiftAt_eq_incl hw h]

theorem archSliceAt_eventuallyEq {w : InfinitePlace F} (hw : w.IsReal)
    (φ : AdelicGL2 (𝓞 F) F → ℂ) (g : AdelicGL2 (𝓞 F) F) {e : Fin 2 → Fin 2 → ℝ}
    (h : (Matrix.of e).det ≠ 0) :
    archSliceAt w hw φ g =ᶠ[nhds e] fun e' => φ (g * archRealLiftAt hw e') := by
  filter_upwards [isOpen_setOf_det_ne_zero.mem_nhds h] with e' he'
  exact archSliceAt_eq_of_det_ne_zero hw φ g he'

end Lift

section Lowering

variable {F : Type} [Field F] [NumberField F]

def lowerFn {w : InfinitePlace F} (hw : w.IsReal) (φ : AdelicGL2 (𝓞 F) F → ℂ) :
    AdelicGL2 (𝓞 F) F → ℂ :=
  fun g => (archDerivAt hw .H φ g - Complex.I * archDerivAt hw .E φ g - Complex.I * archDerivAt hw .Fm φ g) / 2

theorem archDerivAt_apply_mul_lift {w : InfinitePlace F} {hw : w.IsReal} {φ : AdelicGL2 (𝓞 F) F → ℂ}
    (hφ : IsArchSmoothAt hw φ) (d : ArchDir) (g : AdelicGL2 (𝓞 F) F) {e : Fin 2 → Fin 2 → ℝ}
    (he : (Matrix.of e).det ≠ 0) :
    archDerivAt hw d φ (g * archRealLiftAt hw e) =
      fderiv ℝ (fun e' => φ (g * archRealLiftAt hw e')) e (Matrix.of.symm (Matrix.of e * archDirMatrix d)) := by
  have hdiff : HasFDerivAt (fun e' => φ (g * archRealLiftAt hw e'))
      (fderiv ℝ (fun e' => φ (g * archRealLiftAt hw e')) e)
      (Matrix.of.symm (Matrix.of e * (archFlowMatrix d 0 : Matrix (Fin 2) (Fin 2) ℝ))) := by
    rw [of_symm_mul_archFlowMatrix_zero]
    exact (((hφ g).contDiffAt (isOpen_setOf_det_ne_zero.mem_nhds he)).differentiableAt (by simp)).hasFDerivAt
  have hfun : (fun t : ℝ => φ (g * archRealLiftAt hw e * archFlowAt hw d t)) =
      fun t : ℝ => φ (g * archRealLiftAt hw
        (Matrix.of.symm (Matrix.of e * (archFlowMatrix d t : Matrix (Fin 2) (Fin 2) ℝ)))) := by
    funext t
    rw [archFlowAt, mul_assoc, archRealLiftAt_mul_archRealGLAt hw he]
  show deriv (fun t : ℝ => φ (g * archRealLiftAt hw e * archFlowAt hw d t)) 0 = _
  rw [hfun]
  simpa only [Function.comp_def] using
    (hdiff.comp_hasDerivAt (0 : ℝ) (hasDerivAt_of_symm_mul_archFlowMatrix e d)).deriv

theorem lowerFn_apply_mul_lift {w : InfinitePlace F} {hw : w.IsReal} {φ : AdelicGL2 (𝓞 F) F → ℂ}
    (hφ : IsArchSmoothAt hw φ) (g : AdelicGL2 (𝓞 F) F) {e : Fin 2 → Fin 2 → ℝ}
    (he : (Matrix.of e).det ≠ 0) :
    lowerFn hw φ (g * archRealLiftAt hw e) =
      loweringAt (fun e' => φ (g * archRealLiftAt hw e')) (Matrix.of e) := by
  set S : (Fin 2 → Fin 2 → ℝ) → ℂ := fun e' => φ (g * archRealLiftAt hw e') with hS
  have hH := archDerivAt_apply_mul_lift hφ .H g he
  have hE := archDerivAt_apply_mul_lift hφ .E g he
  have hF := archDerivAt_apply_mul_lift hφ .Fm g he
  have hmat : (!![(0 : ℝ), 1; 1, 0] : Matrix (Fin 2) (Fin 2) ℝ) = archDirMatrix .E + archDirMatrix .Fm := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [archDirMatrix]
  have hsum : fderiv ℝ S e (Matrix.of.symm (Matrix.of e * !![(0 : ℝ), 1; 1, 0])) =
      fderiv ℝ S e (Matrix.of.symm (Matrix.of e * archDirMatrix .E)) +
        fderiv ℝ S e (Matrix.of.symm (Matrix.of e * archDirMatrix .Fm)) := by
    rw [← map_add, hmat, Matrix.mul_add]
    rfl
  show (archDerivAt hw .H φ (g * archRealLiftAt hw e) - Complex.I * archDerivAt hw .E φ (g * archRealLiftAt hw e) -
      Complex.I * archDerivAt hw .Fm φ (g * archRealLiftAt hw e)) / 2 =
    (fderiv ℝ S e (Matrix.of.symm (Matrix.of e * archDirMatrix .H)) -
      Complex.I * fderiv ℝ S e (Matrix.of.symm (Matrix.of e * !![(0 : ℝ), 1; 1, 0]))) / 2
  rw [hH, hE, hF, hsum]
  ring

theorem archRealLiftAt_one' {w : InfinitePlace F} (hw : w.IsReal) :
    archRealLiftAt hw ((1 : Matrix (Fin 2) (Fin 2) ℝ) : Fin 2 → Fin 2 → ℝ) = 1 :=
  archRealLiftAt_of_symm_one hw

theorem det_of_one_ne_zero : (Matrix.of ((1 : Matrix (Fin 2) (Fin 2) ℝ) : Fin 2 → Fin 2 → ℝ)).det ≠ 0 := by
  change (1 : Matrix (Fin 2) (Fin 2) ℝ).det ≠ 0
  rw [Matrix.det_one]; exact one_ne_zero

theorem lowerFn_apply {w : InfinitePlace F} {hw : w.IsReal} {φ : AdelicGL2 (𝓞 F) F → ℂ}
    (hφ : IsArchSmoothAt hw φ) (g : AdelicGL2 (𝓞 F) F) :
    lowerFn hw φ g = loweringAt (fun e' => φ (g * archRealLiftAt hw e')) 1 := by
  have h := lowerFn_apply_mul_lift hφ g det_of_one_ne_zero
  rw [archRealLiftAt_one', mul_one] at h
  exact h

theorem slice_mul_rotMat {w : InfinitePlace F} (hw : w.IsReal) (k : ℤ)
    (φ : AdelicGL2 (𝓞 F) F → ℂ)
    (hk : HasArchCharacterAt₀ F w
      ((archWeightCharℝ k).comp (rowIsometrySubgroup₀Map (ringEquivRealOfIsReal hw)
        (norm_ringEquivRealOfIsReal hw))) φ)
    (g : AdelicGL2 (𝓞 F) F) (m : Matrix (Fin 2) (Fin 2) ℝ) (hm : m.det ≠ 0) (θ : ℝ) :
    φ (g * archRealLiftAt hw ((m * rotMat θ : Matrix (Fin 2) (Fin 2) ℝ) : Fin 2 → Fin 2 → ℝ)) =
      Complex.exp (Complex.I * k * θ) * φ (g * archRealLiftAt hw (m : Fin 2 → Fin 2 → ℝ)) := by
  have he := norm_symm_ringEquivRealOfIsReal F hw
  have hm' : (Matrix.of (m : Fin 2 → Fin 2 → ℝ)).det ≠ 0 := hm
  have h1 : archRealLiftAt hw ((m * rotMat θ : Matrix (Fin 2) (Fin 2) ℝ) : Fin 2 → Fin 2 → ℝ)
      = archRealLiftAt hw (m : Fin 2 → Fin 2 → ℝ) * archRealGLAt hw (rotGL θ) := by
    rw [archRealLiftAt_mul_archRealGLAt hw hm']
    rfl
  rw [h1, archRealGLAt_rotGL hw he, ← mul_assoc]
  have h := hk (rotAt F hw he θ) (g * archRealLiftAt hw (m : Fin 2 → Fin 2 → ℝ))
  rw [weightChar_rotAt hw he] at h
  exact h

theorem hasArchCharacterAt₀_lowerFn {w : InfinitePlace F} (hw : w.IsReal) (k : ℤ)
    {φ : AdelicGL2 (𝓞 F) F → ℂ} (hφ : IsArchSmoothAt hw φ)
    (hk : HasArchCharacterAt₀ F w
      ((archWeightCharℝ k).comp (rowIsometrySubgroup₀Map (ringEquivRealOfIsReal hw)
        (norm_ringEquivRealOfIsReal hw))) φ) :
    HasArchCharacterAt₀ F w
      ((archWeightCharℝ (k - 2)).comp (rowIsometrySubgroup₀Map (ringEquivRealOfIsReal hw)
        (norm_ringEquivRealOfIsReal hw))) (lowerFn hw φ) := by
  have he := norm_symm_ringEquivRealOfIsReal F hw
  intro κ g
  obtain ⟨θ, rfl⟩ := rotAt_surjective hw he κ
  rw [weightChar_rotAt hw he, ← archRealLiftAt_rotMat hw he]

  set S : (Fin 2 → Fin 2 → ℝ) → ℂ := fun e' => φ (g * archRealLiftAt hw e') with hS
  have hdet : (Matrix.of (rotMat θ : Fin 2 → Fin 2 → ℝ)).det ≠ 0 := by
    change (rotMat θ).det ≠ 0
    rw [det_rotMat]; exact one_ne_zero
  rw [lowerFn_apply_mul_lift hφ g hdet, lowerFn_apply hφ g]

  have hF : ∀ m : Matrix (Fin 2) (Fin 2) ℝ, 0 < m.det → DifferentiableAt ℝ S m := fun m hm =>
    ((hφ g).contDiffAt (isOpen_setOf_det_ne_zero.mem_nhds (show (Matrix.of _).det ≠ 0 from hm.ne'))).differentiableAt
      (by simp)
  have hkS : ∀ m : Matrix (Fin 2) (Fin 2) ℝ, 0 < m.det → ∀ θ' : ℝ,
      S (m * !![Real.cos θ', Real.sin θ'; -Real.sin θ', Real.cos θ']) = Complex.exp (Complex.I * k * θ') * S m :=
    fun m hm θ' => slice_mul_rotMat hw k φ hk g m hm.ne' θ'
  have h := AutomorphicForm.lowering_fderiv_mul_rotation_eq_exp_mul_of_weight S k hF hkS 1
    (by rw [Matrix.det_one]; exact one_pos) θ
  rw [one_mul] at h
  have hsub : (((k - 2 : ℤ) : ℂ)) = (k : ℂ) - 2 := by push_cast; ring
  rw [hsub]
  exact h

theorem isArchLoweringAnnihilatedAt_of_lowerFn_eq_zero {w : InfinitePlace F} (hw : w.IsReal)
    {φ : AdelicGL2 (𝓞 F) F → ℂ} (hφ : IsArchSmoothAt hw φ) (h0 : ∀ g, lowerFn hw φ g = 0) :
    IsArchLoweringAnnihilatedAt w hw φ := by
  intro g z
  set e : Fin 2 → Fin 2 → ℝ := ((!![z.im, z.re; 0, 1] : Matrix (Fin 2) (Fin 2) ℝ) : Fin 2 → Fin 2 → ℝ) with he
  have hdet : (Matrix.of e).det ≠ 0 := by
    change (!![z.im, z.re; 0, 1] : Matrix (Fin 2) (Fin 2) ℝ).det ≠ 0
    rw [Matrix.det_fin_two_of]
    simp [z.im_ne_zero]
  have hev := archSliceAt_eventuallyEq hw φ g hdet
  have hdiffS : DifferentiableAt ℝ (fun e' => φ (g * archRealLiftAt hw e')) e :=
    ((hφ g).contDiffAt (isOpen_setOf_det_ne_zero.mem_nhds hdet)).differentiableAt (by simp)
  refine ⟨hev.differentiableAt_iff.mpr hdiffS, ?_⟩
  have hfd : fderiv ℝ (archSliceAt w hw φ g) (Matrix.of e) =
      fderiv ℝ (fun e' => φ (g * archRealLiftAt hw e')) (Matrix.of e) :=
    hev.fderiv_eq
  have hL : loweringAt (archSliceAt w hw φ g) (Matrix.of e) =
      loweringAt (fun e' => φ (g * archRealLiftAt hw e')) (Matrix.of e) := by
    simp only [loweringAt, hfd]
  change loweringAt (archSliceAt w hw φ g) (Matrix.of e) = 0
  rw [hL, ← lowerFn_apply_mul_lift hφ g hdet]
  exact h0 _

end Lowering

section Conv

variable {F : Type} [Field F] [NumberField F]

theorem rightConv_const_mul_left (c : ℂ) (φ f : AdelicGL2 (𝓞 F) F → ℂ) (g : AdelicGL2 (𝓞 F) F) :
    rightConv F (fun x => c * φ x) f g = c * rightConv F φ f g := by
  simp only [rightConv_apply, mul_assoc]
  exact integral_const_mul _ _

theorem integrable_conv_integrand {φ f : AdelicGL2 (𝓞 F) F → ℂ} (hφ : Continuous φ)
    (hf : Continuous f) (hfc : HasCompactSupport f) (g : AdelicGL2 (𝓞 F) F) :
    letI := AdelicHaar.glBorel (Fin 2) (𝓞 F) F
    Integrable (fun x => φ (g * x) * f x) (AdelicHaar.adelicGLHaar (Fin 2) (𝓞 F) F) := by
  letI : MeasurableSpace (AdelicGL2 (𝓞 F) F) := AdelicHaar.glBorel (Fin 2) (𝓞 F) F
  haveI : BorelSpace (AdelicGL2 (𝓞 F) F) := AdelicHaar.borelSpace_glBorel (Fin 2) (𝓞 F) F
  haveI : (AdelicHaar.adelicGLHaar (Fin 2) (𝓞 F) F).IsHaarMeasure :=
    AdelicHaar.isHaarMeasure_adelicGLHaar (Fin 2) (𝓞 F) F
  refine Continuous.integrable_of_hasCompactSupport ((hφ.comp (continuous_const.mul continuous_id)).mul hf) ?_
  exact hfc.mul_left

theorem rightConv_beta {φ₀ : AdelicGL2 (𝓞 F) F → ℂ} (hφ₀ : Continuous φ₀)
    (A B C : AdelicGL2 (𝓞 F) F → ℂ)
    (hA : Continuous A ∧ HasCompactSupport A) (hB : Continuous B ∧ HasCompactSupport B)
    (hC : Continuous C ∧ HasCompactSupport C) (g : AdelicGL2 (𝓞 F) F) :
    rightConv F φ₀ (fun y => (A y - Complex.I * B y - Complex.I * C y) / 2) g =
      (rightConv F φ₀ A g - Complex.I * rightConv F φ₀ B g - Complex.I * rightConv F φ₀ C g) / 2 := by
  letI : MeasurableSpace (AdelicGL2 (𝓞 F) F) := AdelicHaar.glBorel (Fin 2) (𝓞 F) F
  have h3 : Integrable (fun a => φ₀ (g * a) * A a) (AdelicHaar.adelicGLHaar (Fin 2) (𝓞 F) F) :=
    integrable_conv_integrand hφ₀ hA.1 hA.2 g
  have hIB : Integrable (fun a => φ₀ (g * a) * B a) (AdelicHaar.adelicGLHaar (Fin 2) (𝓞 F) F) :=
    integrable_conv_integrand hφ₀ hB.1 hB.2 g
  have hIC : Integrable (fun a => φ₀ (g * a) * C a) (AdelicHaar.adelicGLHaar (Fin 2) (𝓞 F) F) :=
    integrable_conv_integrand hφ₀ hC.1 hC.2 g
  have h4 : Integrable (fun a => Complex.I * (φ₀ (g * a) * B a)) (AdelicHaar.adelicGLHaar (Fin 2) (𝓞 F) F) :=
    hIB.const_mul _
  have h2 : Integrable (fun a => Complex.I * (φ₀ (g * a) * C a)) (AdelicHaar.adelicGLHaar (Fin 2) (𝓞 F) F) :=
    hIC.const_mul _
  have h1 : Integrable (fun a => φ₀ (g * a) * A a - Complex.I * (φ₀ (g * a) * B a))
      (AdelicHaar.adelicGLHaar (Fin 2) (𝓞 F) F) := h3.sub h4
  have hfun : (fun x => φ₀ (g * x) * ((A x - Complex.I * B x - Complex.I * C x) / 2)) =
      fun x => (φ₀ (g * x) * A x - Complex.I * (φ₀ (g * x) * B x) - Complex.I * (φ₀ (g * x) * C x)) / 2 := by
    funext x; ring
  simp only [rightConv_apply]
  rw [hfun, integral_div, integral_sub h1 h2, integral_sub h3 h4, integral_const_mul, integral_const_mul]

theorem lowerFn_rightConv {w : InfinitePlace F} (hw : w.IsReal) {φ₀ α : AdelicGL2 (𝓞 F) F → ℂ}
    (hφ₀ : Continuous φ₀) (hα : IsFactorizableTestFn F α)
    (αd : ArchDir → AdelicGL2 (𝓞 F) F → ℂ)
    (hαd : ∀ d, αd d = fun y => deriv (fun t : ℝ => α (archFlowAt hw d (-t) * y)) 0)
    (hαdc : ∀ d, Continuous (αd d) ∧ HasCompactSupport (αd d)) :
    lowerFn hw (rightConv F φ₀ α) =
      rightConv F φ₀ (fun y => (αd .H y - Complex.I * αd .E y - Complex.I * αd .Fm y) / 2) := by
  have hderiv : ∀ d, archDerivAt hw d (rightConv F φ₀ α) = rightConv F φ₀ (αd d) := fun d => by
    rw [hαd d]
    exact ((AutomorphicForm.archDerivAt_rightConv_eq_rightConv_deriv_of_isFactorizableTestFn F hw d).1
      φ₀ α hφ₀ hα).2
  funext g
  rw [rightConv_beta hφ₀ _ _ _ (hαdc .H) (hαdc .E) (hαdc .Fm)]
  simp only [lowerFn, hderiv]

theorem exists_ne_zero_of_deriv_ne_zero {w : InfinitePlace F} (hw : w.IsReal) (d : ArchDir)
    (α : AdelicGL2 (𝓞 F) F → ℂ) (y : AdelicGL2 (𝓞 F) F)
    (h : deriv (fun t : ℝ => α (archFlowAt hw d (-t) * y)) 0 ≠ 0) :
    ∃ t : ℝ, α (archFlowAt hw d (-t) * y) ≠ 0 := by
  by_contra hcon
  push Not at hcon
  apply h
  have : (fun t : ℝ => α (archFlowAt hw d (-t) * y)) = fun _ => 0 := funext hcon
  rw [this, deriv_const]

theorem support_adapted_of_deriv {w : InfinitePlace F} (hw : w.IsReal) {α : AdelicGL2 (𝓞 F) F → ℂ}
    (U : Subgroup (AdelicGL2 (𝓞 F) F))
    (hαs : ∀ x, α x ≠ 0 → ∃ a u : AdelicGL2 (𝓞 F) F, glFin (𝓞 F) F a = 1 ∧ u ∈ U ∧ x = a * u)
    (αd : ArchDir → AdelicGL2 (𝓞 F) F → ℂ)
    (hαd : ∀ d, αd d = fun y => deriv (fun t : ℝ => α (archFlowAt hw d (-t) * y)) 0)
    (x : AdelicGL2 (𝓞 F) F)
    (hx : (αd .H x - Complex.I * αd .E x - Complex.I * αd .Fm x) / 2 ≠ 0) :
    ∃ a u : AdelicGL2 (𝓞 F) F, glFin (𝓞 F) F a = 1 ∧ u ∈ U ∧ x = a * u := by

  have hsome : ∃ d, αd d x ≠ 0 := by
    by_contra hcon
    push Not at hcon
    apply hx
    rw [hcon .H, hcon .E, hcon .Fm]
    ring
  obtain ⟨d, hd⟩ := hsome
  rw [hαd d] at hd
  obtain ⟨t, ht⟩ := exists_ne_zero_of_deriv_ne_zero hw d α x hd
  obtain ⟨a, u, ha, hu, hxu⟩ := hαs _ ht
  refine ⟨archFlowAt hw d t * a, u, ?_, hu, ?_⟩
  · rw [map_mul, ha, mul_one]
    exact glFin_adelicArchGLIncl F _
  · have hinv : archFlowAt hw d t * archFlowAt hw d (-t) = 1 := by
      rw [← archFlowAt_add, add_neg_cancel, archFlowAt_zero]
    calc x = archFlowAt hw d t * (archFlowAt hw d (-t) * x) := by rw [← mul_assoc, hinv, one_mul]
      _ = archFlowAt hw d t * a * u := by rw [hxu, mul_assoc]

theorem isFactorizableTestFn_beta {w : InfinitePlace F} (hw : w.IsReal) {α : AdelicGL2 (𝓞 F) F → ℂ}
    (hα : IsFactorizableTestFn F α)
    (αd : ArchDir → AdelicGL2 (𝓞 F) F → ℂ)
    (hαd : ∀ d, αd d = fun y => deriv (fun t : ℝ => α (archFlowAt hw d (-t) * y)) 0) :
    IsFactorizableTestFn F (fun y => (αd .H y - Complex.I * αd .E y - Complex.I * αd .Fm y) / 2) ∧
      ∀ d, IsFactorizableTestFn F (αd d) := by
  obtain ⟨fa, ff, hfa, hff, hfac⟩ := hα

  have hd : ∀ d, ∃ fa' : GL (Fin 2) (InfiniteAdeleRing F) → ℂ, IsArchTestFactor F fa' ∧
      αd d = fun y => fa' (glArch (𝓞 F) F y) * ff (glFin (𝓞 F) F y) := by
    intro d
    obtain ⟨fa', hfa', heq⟩ := (AutomorphicForm.archDerivAt_rightConv_eq_rightConv_deriv_of_isFactorizableTestFn
      F hw d).2.1 fa ff hfa
    refine ⟨fa', hfa', ?_⟩
    rw [hαd d, ← heq]
    funext y
    congr 1
    funext t
    exact hfac _
  choose fa' hfa' heq using hd
  refine ⟨⟨fun m => (fa' .H m - Complex.I * fa' .E m - Complex.I * fa' .Fm m) / 2, ff, ?_, hff, ?_⟩,
    fun d => ⟨fa' d, ff, hfa' d, hff, fun y => by rw [heq d]⟩⟩
  ·
    obtain ⟨⟨ΦH, hΦH, hH⟩, hcH⟩ := hfa' .H
    obtain ⟨⟨ΦE, hΦE, hE⟩, hcE⟩ := hfa' .E
    obtain ⟨⟨ΦF, hΦF, hF⟩, hcF⟩ := hfa' .Fm
    refine ⟨⟨fun e => (ΦH e - Complex.I * ΦE e - Complex.I * ΦF e) / 2, ?_, fun m => ?_⟩, ?_⟩
    · exact ((hΦH.sub (contDiff_const.mul hΦE)).sub (contDiff_const.mul hΦF)).div_const _
    · simp only [hH, hE, hF]
    · have h1 : HasCompactSupport (fun m => fa' .H m - Complex.I * fa' .E m - Complex.I * fa' .Fm m) := by
        refine (hcH.sub ?_).sub ?_
        · exact hcE.mul_left
        · exact hcF.mul_left
      have h2 := h1.mul_right (f' := fun _ => (2 : ℂ)⁻¹)
      simp only [div_eq_mul_inv, mul_comm] at h2 ⊢
      first | exact h2 | (convert h2 using 1)
  · intro y
    simp only [heq]
    ring

end Conv

section Witness

variable {F : Type} [Field F] [NumberField F]

structure Setup (F : Type) [Field F] [NumberField F] where
  c : ℝ
  u : ℝ
  d₁ : ℝ
  d₂ : ℝ
  T : Finset (AdelicGL2 (𝓞 F) F)
  hd : d₁ < d₂
  hc : 0 < c
  hd₁ : 0 < d₁
  hcov : CoversModCentre F (⋃ x ∈ T, (· * x) '' centreCutSiegelSet F c u d₁ d₂)
  Θ' : HeckeEigensystem F ℂ
  R' : SmoothCuspRealizationAt F
    (productionPinsOf F (⋃ x ∈ T, (· * x) '' centreCutSiegelSet F c u d₁ d₂)
      (fun N => levelOne (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F) (fun v => heckeGen (𝓞 F) F v) (adelicBox F))
    Θ'.toRawCentral
  hR' : Continuous R'.toFun

namespace Setup

variable (X : Setup F)

abbrev D : Set (AdelicGL2 (𝓞 F) F) := ⋃ x ∈ X.T, (· * x) '' centreCutSiegelSet F X.c X.u X.d₁ X.d₂

abbrev pins : CarrierPins F :=
  productionPinsOf F X.D (fun N => levelOne (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F)
    (fun v => heckeGen (𝓞 F) F v) (adelicBox F)

abbrev U : Subgroup (AdelicGL2 (𝓞 F) F) := levelOne (𝓞 F) F X.Θ'.toRawCentral.level ⊓ finiteAdelicGL2Subgroup F

theorem measurableSet_D :
    letI := AdelicHaar.glBorel (Fin 2) (𝓞 F) F
    MeasurableSet X.D := by
  letI : MeasurableSpace (AdelicGL2 (𝓞 F) F) := AdelicHaar.glBorel (Fin 2) (𝓞 F) F
  haveI : BorelSpace (AdelicGL2 (𝓞 F) F) := AdelicHaar.borelSpace_glBorel (Fin 2) (𝓞 F) F
  refine Finset.measurableSet_biUnion _ fun x _ => ?_
  have himg : (· * x) '' centreCutSiegelSet F X.c X.u X.d₁ X.d₂
      = (· * x⁻¹) ⁻¹' centreCutSiegelSet F X.c X.u X.d₁ X.d₂ := by
    ext g; simp [Set.mem_preimage]
  rw [himg]
  exact measurable_mul_const x⁻¹ (measurableSet_centreCutSiegelSet X.c X.u X.d₁ X.d₂)

theorem measure_D_lt_top :
    letI := AdelicHaar.glBorel (Fin 2) (𝓞 F) F
    AdelicHaar.adelicGLHaar (Fin 2) (𝓞 F) F X.D < ⊤ := by
  letI : MeasurableSpace (AdelicGL2 (𝓞 F) F) := AdelicHaar.glBorel (Fin 2) (𝓞 F) F
  refine (measure_biUnion_finset_le _ _).trans_lt (ENNReal.sum_lt_top.mpr fun x _ => ?_)
  exact adelicGLHaar_mul_right_centreCutSiegelSet_lt_top F X.hc X.u X.hd₁ X.d₂ x

def realizationOfConv (f : AdelicGL2 (𝓞 F) F → ℂ) (hf : IsFactorizableTestFn F f)
    (hfs : ∀ x, f x ≠ 0 → ∃ a u : AdelicGL2 (𝓞 F) F, glFin (𝓞 F) F a = 1 ∧ u ∈ X.U ∧ x = a * u)
    (hne : ∃ g, rightConv F X.R'.toFun f g ≠ 0) :
    SmoothCuspRealizationAt F X.pins X.Θ'.toRawCentral := by
  have hbk := AutomorphicForm.isCuspidalFn_isKfSmooth_levelInvariant_isHeckeCosetEigenfunctionAt_rightConv_of_isFactorizableTestFn_of_support_subset
    F X.c X.u X.d₁ X.d₂ X.T X.Θ'.toRawCentral X.R' X.hR' f hf hfs
  exact
  { toFun := rightConv F X.R'.toFun f
    exists_ne_zero := hne
    centralChar := X.R'.centralChar
    smoothCusp := by
      refine ⟨⟨?_, hbk.1⟩, hbk.2.1⟩

      letI : MeasurableSpace (AdelicGL2 (𝓞 F) F) := AdelicHaar.glBorel (Fin 2) (𝓞 F) F
      haveI : BorelSpace (AdelicGL2 (𝓞 F) F) := AdelicHaar.borelSpace_glBorel (Fin 2) (𝓞 F) F
      have hmem₀ := (lsXiMemberAt_iff (𝓞 F) F (AdelicHaar.adelicGLHaar (Fin 2) (𝓞 F) F) ⊤ X.R'.centralChar
        X.D X.R'.toFun).mp X.R'.smoothCusp.1.1
      refine (lsXiMemberAt_iff (𝓞 F) F (AdelicHaar.adelicGLHaar (Fin 2) (𝓞 F) F) ⊤ X.R'.centralChar
        X.D (rightConv F X.R'.toFun f)).mpr ⟨⟨fun γ g => ?_, fun z g => ?_⟩, ?_⟩
      · rw [← rightConv_comp_mul_left]
        simp_rw [hmem₀.1.left_invariant γ]
      · rw [← rightConv_comp_mul_left]
        simp_rw [hmem₀.1.central_transform z]
        exact rightConv_const_mul_left _ _ _ _
      ·
        have hcont : Continuous (rightConv F X.R'.toFun f) :=
          (AutomorphicForm.continuous_rightConv_and_contDiff_of_isFactorizableTestFn F X.R'.toFun X.hR' f hf).1
        have hB := AutomorphicForm.isBoundedOnSiegelWindows_rightConv_of_isCuspAutomorphicFnAt_of_coversModCentre
          F X.c X.u X.d₁ X.d₂ X.T X.hd X.hcov X.R'.centralChar X.R'.toFun X.R'.smoothCusp.1 X.hR' f hf
        obtain ⟨C, hC⟩ := hB X.c X.u X.d₁ X.d₂ X.T X.hc X.hd₁
        haveI : IsFiniteMeasure ((AdelicHaar.adelicGLHaar (Fin 2) (𝓞 F) F).restrict X.D) :=
          isFiniteMeasure_restrict.mpr X.measure_D_lt_top.ne
        have htop : MemLp (rightConv F X.R'.toFun f) ⊤ ((AdelicHaar.adelicGLHaar (Fin 2) (𝓞 F) F).restrict X.D) :=
          memLp_top_of_bound hcont.aestronglyMeasurable C
            ((ae_restrict_iff' X.measurableSet_D).mpr (Filter.Eventually.of_forall hC))
        exact htop.mono_exponent le_top
    level_invariant := hbk.2.2.1
    exceptionalSet := X.R'.exceptionalSet
    hecke_eigen := hbk.2.2.2
    central_eigen := fun v hv g => by
      show rightConv F X.R'.toFun f (centralScalar (𝓞 F) F _ * g) = _
      rw [← rightConv_comp_mul_left]
      simp_rw [X.R'.central_eigen v hv]
      exact rightConv_const_mul_left _ _ _ _ }

@[scoped simp] theorem realizationOfConv_toFun (f : AdelicGL2 (𝓞 F) F → ℂ) (hf : IsFactorizableTestFn F f)
    (hfs : ∀ x, f x ≠ 0 → ∃ a u : AdelicGL2 (𝓞 F) F, glFin (𝓞 F) F a = 1 ∧ u ∈ X.U ∧ x = a * u)
    (hne : ∃ g, rightConv F X.R'.toFun f g ≠ 0) :
    (X.realizationOfConv f hf hfs hne).toFun = rightConv F X.R'.toFun f := rfl

theorem continuous_realizationOfConv (f : AdelicGL2 (𝓞 F) F → ℂ) (hf : IsFactorizableTestFn F f)
    (hfs : ∀ x, f x ≠ 0 → ∃ a u : AdelicGL2 (𝓞 F) F, glFin (𝓞 F) F a = 1 ∧ u ∈ X.U ∧ x = a * u)
    (hne : ∃ g, rightConv F X.R'.toFun f g ≠ 0) :
    IsGenuineCuspRealizationAt F X.pins X.Θ'.toRawCentral (X.realizationOfConv f hf hfs hne) :=
  (AutomorphicForm.continuous_rightConv_and_contDiff_of_isFactorizableTestFn F X.R'.toFun X.hR' f hf).1

end Setup
p2m_reactivate "P2MW.S_AutomorphicForm_archOccursInClassOf_isArchLoweringAnnihilatedAt_of_not_archOccursInClassOf_archWeightChar_sub_two_of_coversModCentre_of_pos.AutomorphicForm.LowerEdgePos.Setup"

end Witness
p2m_reactivate "P2MW.S_AutomorphicForm_archOccursInClassOf_isArchLoweringAnnihilatedAt_of_not_archOccursInClassOf_archWeightChar_sub_two_of_coversModCentre_of_pos.AutomorphicForm.LowerEdgePos.Setup"

end LowerEdgePos
p2m_reactivate "P2MW.S_AutomorphicForm_archOccursInClassOf_isArchLoweringAnnihilatedAt_of_not_archOccursInClassOf_archWeightChar_sub_two_of_coversModCentre_of_pos.AutomorphicForm.LowerEdgePos.Setup P2MW.S_AutomorphicForm_archOccursInClassOf_isArchLoweringAnnihilatedAt_of_not_archOccursInClassOf_archWeightChar_sub_two_of_coversModCentre_of_pos.AutomorphicForm.LowerEdgePos"

end AutomorphicForm
p2m_reactivate "P2MW.S_AutomorphicForm_archOccursInClassOf_isArchLoweringAnnihilatedAt_of_not_archOccursInClassOf_archWeightChar_sub_two_of_coversModCentre_of_pos.AutomorphicForm.LowerEdgePos.Setup P2MW.S_AutomorphicForm_archOccursInClassOf_isArchLoweringAnnihilatedAt_of_not_archOccursInClassOf_archWeightChar_sub_two_of_coversModCentre_of_pos.AutomorphicForm.LowerEdgePos P2MW.S_AutomorphicForm_archOccursInClassOf_isArchLoweringAnnihilatedAt_of_not_archOccursInClassOf_archWeightChar_sub_two_of_coversModCentre_of_pos.AutomorphicForm"

end
p2m_reactivate "P2MW.S_AutomorphicForm_archOccursInClassOf_isArchLoweringAnnihilatedAt_of_not_archOccursInClassOf_archWeightChar_sub_two_of_coversModCentre_of_pos.AutomorphicForm.LowerEdgePos.Setup P2MW.S_AutomorphicForm_archOccursInClassOf_isArchLoweringAnnihilatedAt_of_not_archOccursInClassOf_archWeightChar_sub_two_of_coversModCentre_of_pos.AutomorphicForm.LowerEdgePos P2MW.S_AutomorphicForm_archOccursInClassOf_isArchLoweringAnnihilatedAt_of_not_archOccursInClassOf_archWeightChar_sub_two_of_coversModCentre_of_pos.AutomorphicForm"

open AutomorphicForm.LowerEdgePos in
theorem solution
    (F : Type) [Field F] [NumberField F] (c u d₁ d₂ : ℝ) (T : Finset (AdelicGL2 (𝓞 F) F))
    (hd : d₁ < d₂)
    (hc : 0 < c) (hd₁ : 0 < d₁)
    (hcov : CoversModCentre F (⋃ x ∈ T, (· * x) '' centreCutSiegelSet F c u d₁ d₂))
    (Θ : HeckeEigensystem F ℂ)
    (w : InfinitePlace F) (hw : w.IsReal) (k : ℤ)
    (hk :
      ArchOccursInClassOf F (⋃ x ∈ T, (· * x) '' centreCutSiegelSet F c u d₁ d₂) Θ
        (fun φ => HasArchCharacterAt₀ F w
          ((archWeightCharℝ k).comp (rowIsometrySubgroup₀Map (ringEquivRealOfIsReal hw)
            (norm_ringEquivRealOfIsReal hw))) φ))
    (hk2 : ¬
      ArchOccursInClassOf F (⋃ x ∈ T, (· * x) '' centreCutSiegelSet F c u d₁ d₂) Θ
        (fun φ => HasArchCharacterAt₀ F w
          ((archWeightCharℝ (k - 2)).comp (rowIsometrySubgroup₀Map (ringEquivRealOfIsReal hw)
            (norm_ringEquivRealOfIsReal hw))) φ)) :
    ArchOccursInClassOf F (⋃ x ∈ T, (· * x) '' centreCutSiegelSet F c u d₁ d₂) Θ
      (fun φ => HasArchCharacterAt₀ F w
          ((archWeightCharℝ k).comp (rowIsometrySubgroup₀Map (ringEquivRealOfIsReal hw)
            (norm_ringEquivRealOfIsReal hw))) φ ∧
        IsArchLoweringAnnihilatedAt w hw φ) := by
  obtain ⟨Θ', hΘ', R', hR', hRk⟩ := hk

  let X : Setup F :=
    { c := c, u := u, d₁ := d₁, d₂ := d₂, T := T, hd := hd, hc := hc, hd₁ := hd₁, hcov := hcov,
      Θ' := Θ', R' := R', hR' := hR' }

  obtain ⟨α, hα, -, hαs, hαk, hαne⟩ :=
    AutomorphicForm.exists_isFactorizableTestFn_hasArchCharacterAt_rightConv_ne_zero_of_hasArchCharacterAt
      F Θ'.toRawCentral.level Θ'.toRawCentral.level_ne_bot w hw k R'.toFun hR' R'.exists_ne_zero
      R'.level_invariant hRk
  set φ := rightConv F R'.toFun α with hφdef

  have hsmooth : IsArchSmoothAt hw φ :=
    ((AutomorphicForm.archDerivAt_rightConv_eq_rightConv_deriv_of_isFactorizableTestFn F hw .H).1
      R'.toFun α hR' hα).1

  set αd : ArchDir → AdelicGL2 (𝓞 F) F → ℂ := fun d y => deriv (fun t : ℝ => α (archFlowAt hw d (-t) * y)) 0
    with hαd_def
  have hαd : ∀ d, αd d = fun y => deriv (fun t : ℝ => α (archFlowAt hw d (-t) * y)) 0 := fun d => rfl
  obtain ⟨hβ, hαdf⟩ := isFactorizableTestFn_beta hw hα αd hαd
  set β : AdelicGL2 (𝓞 F) F → ℂ := fun y => (αd .H y - Complex.I * αd .E y - Complex.I * αd .Fm y) / 2 with hβdef
  have hψ : lowerFn hw φ = rightConv F R'.toFun β :=
    lowerFn_rightConv hw hR' hα αd hαd fun d =>
      AutomorphicForm.continuous_and_hasCompactSupport_of_isFactorizableTestFn F (αd d) (hαdf d)
  have hβs : ∀ x, β x ≠ 0 → ∃ a u' : AdelicGL2 (𝓞 F) F, glFin (𝓞 F) F a = 1 ∧ u' ∈ X.U ∧ x = a * u' :=
    fun x hx => support_adapted_of_deriv hw X.U hαs αd hαd x hx

  have hψk := hasArchCharacterAt₀_lowerFn hw k hsmooth hαk
  have hψ0 : ∀ g, lowerFn hw φ g = 0 := by
    by_contra hcon
    push Not at hcon
    have hne : ∃ g, rightConv F R'.toFun β g ≠ 0 := by rwa [← hψ]
    apply hk2
    refine ⟨Θ', hΘ', X.realizationOfConv β hβ hβs hne, X.continuous_realizationOfConv β hβ hβs hne, ?_⟩
    show HasArchCharacterAt₀ F w _ (rightConv F R'.toFun β)
    rw [← hψ]
    exact hψk

  refine ⟨Θ', hΘ', X.realizationOfConv α hα hαs hαne, X.continuous_realizationOfConv α hα hαs hαne, ?_, ?_⟩
  · exact hαk
  · exact isArchLoweringAnnihilatedAt_of_lowerFn_eq_zero hw hsmooth hψ0

end S_AutomorphicForm_archOccursInClassOf_isArchLoweringAnnihilatedAt_of_not_archOccursInClassOf_archWeightChar_sub_two_of_coversModCentre_of_pos
end P2MW
export P2MW.S_AutomorphicForm_archOccursInClassOf_isArchLoweringAnnihilatedAt_of_not_archOccursInClassOf_archWeightChar_sub_two_of_coversModCentre_of_pos (solution)
