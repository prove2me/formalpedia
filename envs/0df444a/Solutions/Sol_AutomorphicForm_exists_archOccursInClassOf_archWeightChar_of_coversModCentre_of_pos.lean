-- Prove2me | solution 1 for AutomorphicForm.exists_archOccursInClassOf_archWeightChar_of_coversModCentre_of_pos
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.961684+00:00
-- url     : https://prove2.me/submissions/046367ac-e680-5691-9552-c9dada564838

import Mathlib
import Definitions.Def_AutomorphicForm_TranslateSpanOccurrence
import Definitions.Def_AutomorphicForm_ArchLoweringAnnihilated
import Definitions.Def_AutomorphicForm_RightConvolution
import Definitions.Def_AutomorphicForm_FactorizableTestFn
import Definitions.Def_NumberField_TateGlobalZeta
import Theorems.Thm_AutomorphicForm_exists_isFactorizableTestFn_rightConv_ne_zero_of_levelOne_invariant
import Theorems.Thm_AutomorphicForm_isCuspidalFn_isKfSmooth_levelInvariant_isHeckeCosetEigenfunctionAt_rightConv_of_isFactorizableTestFn_of_support_subset
import Theorems.Thm_AutomorphicForm_continuous_rightConv_and_contDiff_of_isFactorizableTestFn
import Theorems.Thm_AutomorphicForm_exists_forall_norm_rightConv_le_mul_eLpNorm_of_isSmoothCuspAutomorphicFnAt_of_coversModCentre
import Theorems.Thm_AutomorphicForm_exists_finset_globalPoints_mul_mul_centralScalar_mem_of_coversModCentre_of_ideleNorm_det_mem_Icc
import Theorems.Thm_NumberField_TateGlobal_ideleNorm_det_eq_prod_archDetNorm_pow_mult
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AutomorphicForm_exists_archOccursInClassOf_archWeightChar_of_coversModCentre_of_pos
p2m_attr_erase "instance" "RestrictedProduct.SecondCountableTopology_of_principal instCountableElemSetSetsCofinite_definitions instCountableOfNumberField_definitions instFiniteResidueFieldAdicCompletionRingOfIntegersWithZeroMultiplicativeInt_definitions NumberField.instCompactSpaceAdicCompletionIntegers Rat.adicCompletion.locallyCompactSpace NumberField.instFiniteResidueFieldAdicCompletionIntegers instWeaklyLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions"
p2m_attr_erase "simp" "ContinuousAddEquiv.restrictedProductPi_apply RestrictedProduct.flatten_homeomorph_apply RestrictedProduct.flatten_homeomorph'_symm_apply ContinuousMulEquiv.restrictedProductPi_symm_apply RestrictedProduct.flatten_homeomorph'_apply RestrictedProduct.flatten_homeomorph_symm_apply ContinuousMulEquiv.restrictedProductPi_apply ContinuousAddEquiv.restrictedProductPi_symm_apply RingEquiv.restrictedProductCongr_symm_apply RingEquiv.restrictedProductCongrRight_apply MulEquiv.restrictedProductCongrRight_apply Equiv.restrictedProductProd_symm_apply_coe Equiv.restrictedProductCongrRight_apply AddEquiv.restrictedProductCongr_apply Equiv.restrictedProductCongrLeft'_symm_apply_apply Equiv.restrictedProductCongr_apply_apply Equiv.restrictedProductCongrLeft_apply_apply RestrictedProduct.flatten_equiv'_apply AddEquiv.restrictedProductCongrRight_apply Equiv.restrictedProductCongr_symm_apply Equiv.restrictedProductCongrRight_symm_apply RestrictedProduct.flatten_equiv'_symm_apply AddEquiv.restrictedProductCongrLeft'_apply Equiv.restrictedProductCongrLeft'_apply RestrictedProduct.flatten_apply RingEquiv.restrictedProductCongr_apply_apply RingEquiv.restrictedProductCongrLeft'_apply Equiv.restrictedProductProd_apply RestrictedProduct.flatten_equiv_apply RestrictedProduct.flatten_equiv_symm_apply LinearEquiv.restrictedProductCongrLeft'_apply RestrictedProduct.not_mem_support RestrictedProduct.mem_structureSubring_iff RestrictedProduct.not_mem_mulSupport RestrictedProduct.support_neg RestrictedProduct.mem_indexSupport_iff RestrictedProduct.mulSupport_inv RestrictedProduct.mapAlongLinearMap_apply AutomorphicForm.whittakerCoefficient_zero NumberField.StandardAddChar.ratArchLine_apply"
p2m_attr_erase "simp" "NumberField.StandardAddChar.AdelicTraceData.mk.sizeOf_spec NumberField.StandardAddChar.AdelicTraceData.mk.injEq NumberField.AdelicTrace.traceDiag_apply NumberField.AdelicTrace.diag_apply M4aHerbrand.IdeleGaloisDescent.mk.sizeOf_spec M4aHerbrand.IdeleGaloisDescent.mk.injEq"

set_option autoImplicit false

p2m_open "NumberField NumberField.AdelicLevel NumberField.AdelicBox NumberField.AdelicHaar MeasureTheory AutomorphicForm~continuous_unipotentGL2 P2MW.S_AutomorphicForm_exists_archOccursInClassOf_archWeightChar_of_coversModCentre_of_pos.AutomorphicForm AutomorphicForm.WindowedSiegel AutomorphicForm.SiegelCovering NumberField.InfinitePlace NumberField.InfinitePlace.Completion"

open scoped Classical

noncomputable section

namespace AutomorphicForm
p2m_export "AutomorphicForm" "ArchOccursInClassOf SmoothCusp.heckeCosetSum SmoothCusp.IsHeckeCosetEigenfunctionAt SmoothCuspRealizationAt finiteAdelicGL2Subgroup IsKfSmooth isKfSmooth_iff lsXiMemberAt_iff productionPinsOf AdelicGL2 globalPoints centralScalar IsLsXiFunction unipotentGL2 unipotentGL2_coe constantTermIntegrand constantTerm IsCuspidalFn HeckeEigensystem rowIsometrySubgroup₀Map norm_ringEquivRealOfIsReal rowIsometrySubgroup₀ mem_rowIsometrySubgroup₀_iff entries_of_mem_rowIsometrySubgroup₀ archWeightOneℝ archWeightCharℝ HasArchCharacterAt₀ adelicArchGLInclAt adelicGLHaar_mul_right_centreCutSiegelSet_lt_top rightConv rightConv_apply rightConv_comp_mul_left exists_isFactorizableTestFn_rightConv_ne_zero_of_levelOne_invariant isCuspidalFn_isKfSmooth_levelInvariant_isHeckeCosetEigenfunctionAt_rightConv_of_isFactorizableTestFn_of_support_subset continuous_rightConv_and_contDiff_of_isFactorizableTestFn exists_forall_norm_rightConv_le_mul_eLpNorm_of_isSmoothCuspAutomorphicFnAt_of_coversModCentre exists_finset_globalPoints_mul_mul_centralScalar_mem_of_coversModCentre_of_ideleNorm_det_mem_Icc"
p2m_open "AutomorphicForm~continuous_unipotentGL2"

namespace ArchTypeFourier

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

theorem rotSO_add (θ θ' : ℝ) : rotSO (θ + θ') = rotSO θ * rotSO θ' := by
  apply Subtype.ext
  apply Units.ext
  show rotMat (θ + θ') = rotMat θ * rotMat θ'
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [rotMat, Matrix.mul_apply, Fin.sum_univ_two, Real.cos_add, Real.sin_add] <;> ring

theorem rotSO_zero : rotSO 0 = 1 := by
  apply Subtype.ext
  apply Units.ext
  show rotMat 0 = 1
  ext i j
  fin_cases i <;> fin_cases j <;> simp [rotMat]

theorem rotSO_periodic : Function.Periodic rotSO (2 * Real.pi) := by
  intro θ
  apply Subtype.ext
  apply Units.ext
  show rotMat (θ + 2 * Real.pi) = rotMat θ
  ext i j
  fin_cases i <;> fin_cases j <;> simp [rotMat]

theorem exists_rotSO_eq (k : rowIsometrySubgroup₀ ℝ) : ∃ θ : ℝ, rotSO θ = k := by
  obtain ⟨h10, h11, hab⟩ := entries_of_mem_rowIsometrySubgroup₀ k.2
  set a := ((k : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) 0 0 with ha
  set b := ((k : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) 0 1 with hb
  set z : ℂ := ⟨a, b⟩ with hz
  have hz1 : ‖z‖ = 1 := by
    have : Complex.normSq z = 1 := by rw [Complex.normSq_mk]; nlinarith [hab]
    rw [Complex.norm_def, this, Real.sqrt_one]
  have hz0 : z ≠ 0 := by
    intro h; rw [h, norm_zero] at hz1; exact zero_ne_one hz1
  refine ⟨Complex.arg z, ?_⟩
  have hcos : Real.cos (Complex.arg z) = a := by
    rw [Complex.cos_arg hz0, hz1, div_one]
  have hsin : Real.sin (Complex.arg z) = b := by
    rw [Complex.sin_arg, hz1, div_one]
  apply Subtype.ext
  apply Units.ext
  show rotMat (Complex.arg z) = ((k : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ)
  ext i j
  fin_cases i <;> fin_cases j
  · simpa [rotMat] using hcos
  · simpa [rotMat] using hsin
  · simp [rotMat, hsin]; exact h10.symm
  · simp [rotMat, hcos]; exact h11.symm

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

theorem map_rotGL_eq_rotAt {w : InfinitePlace F} (hw : w.IsReal)
    (he : ∀ x : ℝ, ‖(ringEquivRealOfIsReal hw).symm x‖ = ‖x‖) (θ : ℝ) :
    Matrix.GeneralLinearGroup.map (ringEquivRealOfIsReal hw).symm.toRingHom (rotGL θ) =
      ((rotAt F hw he θ : rowIsometrySubgroup₀ w.Completion) : GL (Fin 2) w.Completion) := by
  apply Units.ext
  ext i j
  rfl

omit [NumberField F] in
theorem rotAt_coe_apply {w : InfinitePlace F} (hw : w.IsReal)
    (he : ∀ x : ℝ, ‖(ringEquivRealOfIsReal hw).symm x‖ = ‖x‖) (θ : ℝ) (i j : Fin 2) :
    (((rotAt F hw he θ : rowIsometrySubgroup₀ w.Completion) : GL (Fin 2) w.Completion) :
      Matrix (Fin 2) (Fin 2) w.Completion) i j = (ringEquivRealOfIsReal hw).symm (rotMat θ i j) := rfl

omit [NumberField F] in
theorem rotAt_add {w : InfinitePlace F} (hw : w.IsReal)
    (he : ∀ x : ℝ, ‖(ringEquivRealOfIsReal hw).symm x‖ = ‖x‖) (θ θ' : ℝ) :
    rotAt F hw he (θ + θ') = rotAt F hw he θ * rotAt F hw he θ' := by
  unfold rotAt; rw [rotSO_add, map_mul]

omit [NumberField F] in
theorem rotAt_zero {w : InfinitePlace F} (hw : w.IsReal)
    (he : ∀ x : ℝ, ‖(ringEquivRealOfIsReal hw).symm x‖ = ‖x‖) : rotAt F hw he 0 = 1 := by
  unfold rotAt; rw [rotSO_zero, map_one]

omit [NumberField F] in
theorem rotAt_periodic {w : InfinitePlace F} (hw : w.IsReal)
    (he : ∀ x : ℝ, ‖(ringEquivRealOfIsReal hw).symm x‖ = ‖x‖) :
    Function.Periodic (rotAt F hw he) (2 * Real.pi) := fun θ => by
  unfold rotAt; rw [rotSO_periodic]

omit [NumberField F] in

theorem exists_rotAt_eq {w : InfinitePlace F} (hw : w.IsReal)
    (he : ∀ x : ℝ, ‖(ringEquivRealOfIsReal hw).symm x‖ = ‖x‖) (k : rowIsometrySubgroup₀ w.Completion) :
    ∃ θ : ℝ, rotAt F hw he θ = k := by
  obtain ⟨θ, hθ⟩ := exists_rotSO_eq
    (rowIsometrySubgroup₀Map (ringEquivRealOfIsReal hw) (norm_ringEquivRealOfIsReal hw) k)
  refine ⟨θ, ?_⟩
  apply Subtype.ext
  apply Units.ext
  ext i j
  rw [rotAt_coe_apply]
  have hij : rotMat θ i j =
      (ringEquivRealOfIsReal hw) (((k : GL (Fin 2) w.Completion) : Matrix (Fin 2) (Fin 2) w.Completion) i j) := by
    have := congrArg (fun m : rowIsometrySubgroup₀ ℝ =>
      ((m : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) i j) hθ
    exact this
  rw [hij, RingEquiv.symm_apply_apply]

end Transport

section Adelic

variable {F : Type} [Field F] [NumberField F]

theorem adelicArchGLInclAt_coe_apply (w : InfinitePlace F) (kk : GL (Fin 2) w.Completion) (i j : Fin 2) :
    ((adelicArchGLInclAt F w kk : AdelicGL2 (𝓞 F) F) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 F) F)) i j =
      ((fun v : InfinitePlace F =>
          (Function.update (1 : ∀ v : InfinitePlace F, Matrix (Fin 2) (Fin 2) v.Completion) w
            (kk : Matrix (Fin 2) (Fin 2) w.Completion) v) i j : InfiniteAdeleRing F),
        (1 : Matrix (Fin 2) (Fin 2) (IsDedekindDomain.FiniteAdeleRing (𝓞 F) F)) i j) :=
  rfl

def archRot (w : InfinitePlace F) (hw : w.IsReal) (θ : ℝ) : AdelicGL2 (𝓞 F) F :=
  adelicArchGLInclAt F w
    ((rotAt F hw (norm_symm_ringEquivRealOfIsReal F hw) θ : rowIsometrySubgroup₀ w.Completion) :
      GL (Fin 2) w.Completion)

theorem archRot_add (w : InfinitePlace F) (hw : w.IsReal) (θ θ' : ℝ) :
    archRot w hw (θ + θ') = archRot w hw θ * archRot w hw θ' := by
  unfold archRot; rw [rotAt_add, Subgroup.coe_mul, map_mul]

theorem archRot_zero (w : InfinitePlace F) (hw : w.IsReal) : archRot w hw 0 = 1 := by
  unfold archRot; rw [rotAt_zero, Subgroup.coe_one, map_one]

theorem archRot_periodic (w : InfinitePlace F) (hw : w.IsReal) :
    Function.Periodic (archRot w hw) (2 * Real.pi) := fun θ => by
  unfold archRot; rw [rotAt_periodic]

theorem archRot_neg_mul (w : InfinitePlace F) (hw : w.IsReal) (θ : ℝ) :
    archRot w hw (-θ) * archRot w hw θ = 1 := by
  rw [← archRot_add, neg_add_cancel, archRot_zero]

theorem archRot_inv (w : InfinitePlace F) (hw : w.IsReal) (θ : ℝ) :
    (archRot w hw θ)⁻¹ = archRot w hw (-θ) :=
  inv_eq_of_mul_eq_one_left (archRot_neg_mul w hw θ)

theorem glFin_archRot (w : InfinitePlace F) (hw : w.IsReal) (θ : ℝ) :
    glFin (𝓞 F) F (archRot w hw θ) = 1 := by
  apply Units.ext; ext i j; rfl

theorem continuous_rotMat_apply (i j : Fin 2) : Continuous fun θ : ℝ => rotMat θ i j := by
  fin_cases i <;> fin_cases j
  · exact Real.continuous_cos
  · exact Real.continuous_sin
  · exact Real.continuous_sin.neg
  · exact Real.continuous_cos

omit [NumberField F] in
theorem continuous_symm_ringEquivRealOfIsReal {w : InfinitePlace F} (hw : w.IsReal) :
    Continuous (ringEquivRealOfIsReal hw).symm := by
  have hiso : Isometry ((ringEquivRealOfIsReal hw).symm.toRingHom.toAddMonoidHom) :=
    AddMonoidHomClass.isometry_of_norm _ (norm_symm_ringEquivRealOfIsReal F hw)
  exact hiso.continuous

theorem continuous_archRot_val (w : InfinitePlace F) (hw : w.IsReal) :
    Continuous fun θ : ℝ =>
      ((archRot w hw θ : AdelicGL2 (𝓞 F) F) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 F) F)) := by
  refine continuous_pi fun i => continuous_pi fun j => ?_
  simp only [archRot, adelicArchGLInclAt_coe_apply]
  refine Continuous.prodMk ?_ continuous_const
  refine continuous_pi fun v => ?_
  by_cases hv : v = w
  · subst hv
    simp only [Function.update_self]
    show Continuous fun θ : ℝ =>
      (((rotAt F hw (norm_symm_ringEquivRealOfIsReal F hw) θ : rowIsometrySubgroup₀ v.Completion) :
        GL (Fin 2) v.Completion) : Matrix (Fin 2) (Fin 2) v.Completion) i j
    simp only [rotAt_coe_apply]
    exact (continuous_symm_ringEquivRealOfIsReal hw).comp (continuous_rotMat_apply i j)
  · simp only [Function.update_of_ne hv]
    exact continuous_const

theorem continuous_archRot (w : InfinitePlace F) (hw : w.IsReal) :
    Continuous fun θ : ℝ => (archRot w hw θ : AdelicGL2 (𝓞 F) F) := by
  rw [Units.continuous_iff]
  refine ⟨continuous_archRot_val w hw, ?_⟩
  have : (fun θ : ℝ => ((archRot w hw θ)⁻¹ : AdelicGL2 (𝓞 F) F).val) =
      fun θ => (archRot w hw (-θ) : AdelicGL2 (𝓞 F) F).val := by
    funext θ; rw [archRot_inv]
  show Continuous fun θ : ℝ => ((archRot w hw θ)⁻¹ : AdelicGL2 (𝓞 F) F).val
  rw [this]
  exact (continuous_archRot_val w hw).comp continuous_neg

theorem det_archRot (w : InfinitePlace F) (hw : w.IsReal) (θ : ℝ) :
    Matrix.GeneralLinearGroup.det (archRot w hw θ) = 1 := by
  apply Units.ext
  rw [Matrix.GeneralLinearGroup.val_det_apply, Units.val_one, Matrix.det_fin_two]
  simp only [archRot, adelicArchGLInclAt_coe_apply]
  refine Prod.ext ?_ ?_
  · show (fun v : InfinitePlace F => _) = (1 : InfiniteAdeleRing F)
    funext v
    show (Function.update (1 : ∀ v : InfinitePlace F, Matrix (Fin 2) (Fin 2) v.Completion) w _ v) 0 0 *
        (Function.update (1 : ∀ v : InfinitePlace F, Matrix (Fin 2) (Fin 2) v.Completion) w _ v) 1 1 -
      (Function.update (1 : ∀ v : InfinitePlace F, Matrix (Fin 2) (Fin 2) v.Completion) w _ v) 0 1 *
        (Function.update (1 : ∀ v : InfinitePlace F, Matrix (Fin 2) (Fin 2) v.Completion) w _ v) 1 0 = 1
    by_cases hv : v = w
    · subst hv
      simp only [Function.update_self, rotAt_coe_apply, ← map_mul, ← map_sub]
      rw [← (ringEquivRealOfIsReal hw).symm.map_one]
      congr 1
      have := det_rotMat θ
      rw [Matrix.det_fin_two] at this
      exact this
    · simp [Function.update_of_ne hv]
  · show (1 : Matrix (Fin 2) (Fin 2) (IsDedekindDomain.FiniteAdeleRing (𝓞 F) F)) 0 0 *
        (1 : Matrix (Fin 2) (Fin 2) (IsDedekindDomain.FiniteAdeleRing (𝓞 F) F)) 1 1 -
      (1 : Matrix (Fin 2) (Fin 2) (IsDedekindDomain.FiniteAdeleRing (𝓞 F) F)) 0 1 *
        (1 : Matrix (Fin 2) (Fin 2) (IsDedekindDomain.FiniteAdeleRing (𝓞 F) F)) 1 0 =
      (1 : IsDedekindDomain.FiniteAdeleRing (𝓞 F) F)
    simp

end Adelic

section Commute

variable {F : Type} [Field F] [NumberField F]

theorem glArch_adelicArchGLInclAt (w : InfinitePlace F) (k : GL (Fin 2) w.Completion) :
    glFin (𝓞 F) F (adelicArchGLInclAt F w k) = 1 := by
  apply Units.ext; ext i j; rfl

theorem AdeleRing.fst_add (a b : AdeleRing (𝓞 F) F) : (a + b).1 = a.1 + b.1 := rfl
theorem AdeleRing.fst_mul (a b : AdeleRing (𝓞 F) F) : (a * b).1 = a.1 * b.1 := rfl
theorem AdeleRing.snd_add (a b : AdeleRing (𝓞 F) F) : (a + b).2 = a.2 + b.2 := rfl
theorem AdeleRing.snd_mul (a b : AdeleRing (𝓞 F) F) : (a * b).2 = a.2 * b.2 := rfl

theorem commute_of_glArch_eq_one_of_glFin_eq_one {a b : AdelicGL2 (𝓞 F) F}
    (ha : glArch (𝓞 F) F a = 1) (hb : glFin (𝓞 F) F b = 1) : a * b = b * a := by
  have ha' : ∀ i j : Fin 2, ((a : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 F) F)) i j).1 =
      (1 : Matrix (Fin 2) (Fin 2) (InfiniteAdeleRing F)) i j := fun i j => by
    have := congrArg (fun m : GL (Fin 2) (InfiniteAdeleRing F) =>
      (m : Matrix (Fin 2) (Fin 2) (InfiniteAdeleRing F)) i j) ha
    exact this
  have hb' : ∀ i j : Fin 2, ((b : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 F) F)) i j).2 =
      (1 : Matrix (Fin 2) (Fin 2) (IsDedekindDomain.FiniteAdeleRing (𝓞 F) F)) i j := fun i j => by
    have := congrArg (fun m : GL (Fin 2) (IsDedekindDomain.FiniteAdeleRing (𝓞 F) F) =>
      (m : Matrix (Fin 2) (Fin 2) (IsDedekindDomain.FiniteAdeleRing (𝓞 F) F)) i j) hb
    exact this
  apply Units.ext
  rw [Units.val_mul, Units.val_mul]
  ext i j
  rw [Matrix.mul_apply, Matrix.mul_apply, Fin.sum_univ_two, Fin.sum_univ_two]
  obtain rfl | rfl : i = 0 ∨ i = 1 := by fin_cases i <;> simp
  all_goals obtain rfl | rfl : j = 0 ∨ j = 1 := by fin_cases j <;> simp
  all_goals
    refine Prod.ext ?_ ?_
    · rw [AdeleRing.fst_add, AdeleRing.fst_add, AdeleRing.fst_mul, AdeleRing.fst_mul,
        AdeleRing.fst_mul, AdeleRing.fst_mul]
      simp only [ha']
      simp
    · rw [AdeleRing.snd_add, AdeleRing.snd_add, AdeleRing.snd_mul, AdeleRing.snd_mul,
        AdeleRing.snd_mul, AdeleRing.snd_mul]
      simp only [hb']
      simp

theorem glArch_eq_one_of_mem_finiteAdelicGL2Subgroup {u : AdelicGL2 (𝓞 F) F}
    (hu : u ∈ finiteAdelicGL2Subgroup F) : glArch (𝓞 F) F u = 1 := hu

theorem heckeGen_mem_finiteAdelicGL2Subgroup (v : IsDedekindDomain.HeightOneSpectrum (𝓞 F)) :
    heckeGen (𝓞 F) F v ∈ finiteAdelicGL2Subgroup F := by
  show glArch (𝓞 F) F (heckeGen (𝓞 F) F v) = 1
  apply Units.ext
  rw [Units.val_one]
  ext i j
  rw [glArch_apply]
  unfold heckeGen
  exact heckeGenAt_fst (uniformizerUnit F v) i j

end Commute

section FourierUniqueness

theorem periodic_eq_zero_of_forall_integral_eq_zero (h : ℝ → ℂ) (hc : Continuous h)
    (hp : Function.Periodic h (2 * Real.pi))
    (hz : ∀ n : ℤ, ∫ θ in (0 : ℝ)..2 * Real.pi,
      Complex.exp (-(Complex.I * n * θ)) * h θ = 0) :
    h = 0 := by
  haveI : Fact (0 < 2 * Real.pi) := ⟨by positivity⟩

  set H : C(AddCircle (2 * Real.pi), ℂ) :=
    ⟨hp.lift, (continuous_coinduced_dom.mpr hc : Continuous hp.lift)⟩ with hH
  have hHapply : ∀ x : ℝ, H (x : AddCircle (2 * Real.pi)) = h x := fun x => rfl
  have hz' : ∀ n : ℤ, ∫ θ in (0 : ℝ)..(0 + 2 * Real.pi),
      (@fourier (2 * Real.pi) (-n)) (θ : AddCircle (2 * Real.pi)) • h θ = 0 := by
    intro n
    rw [zero_add, ← hz n]
    apply intervalIntegral.integral_congr
    intro θ _
    simp only [fourier_coe_apply, smul_eq_mul]
    congr 1
    congr 1
    have hπ : (2 * Real.pi : ℂ) ≠ 0 := by exact_mod_cast (ne_of_gt (by positivity : (0:ℝ) < 2 * Real.pi))
    push_cast
    field_simp
  have hcoef : ∀ n : ℤ, fourierCoeff (H : AddCircle (2 * Real.pi) → ℂ) n = 0 := by
    intro n
    rw [fourierCoeff_eq_intervalIntegral _ n 0]
    simp only [hHapply]
    rw [hz' n, smul_zero]

  set HL := ContinuousMap.toLp (E := ℂ) 2 (@AddCircle.haarAddCircle (2 * Real.pi) _) ℂ H with hHL
  have hcoefL : ∀ n : ℤ, fourierCoeff (HL : AddCircle (2 * Real.pi) → ℂ) n = 0 := by
    intro n
    have hae : (HL : AddCircle (2 * Real.pi) → ℂ) =ᵐ[AddCircle.haarAddCircle] H :=
      ContinuousMap.coeFn_toLp (E := ℂ) (p := 2) (μ := AddCircle.haarAddCircle) (𝕜 := ℂ) H
    rw [← hcoef n]
    unfold fourierCoeff
    exact integral_congr_ae (hae.mono fun x hx => by simp only [hx])
  have hrepr : fourierBasis.repr HL = 0 := by
    apply lp.ext
    funext n
    rw [fourierBasis_repr]
    exact hcoefL n
  have hHL0 : HL = 0 := (fourierBasis (T := 2 * Real.pi)).repr.map_eq_zero_iff.mp hrepr
  have hH0 : H = 0 := by
    have hinj := ContinuousMap.toLp_injective (E := ℂ) (p := 2) (μ := @AddCircle.haarAddCircle (2 * Real.pi) _)
      (𝕜 := ℂ)
    apply hinj
    rw [← hHL, hHL0, map_zero]
  funext x
  have := congrArg (fun G : C(AddCircle (2 * Real.pi), ℂ) => G (x : AddCircle (2 * Real.pi))) hH0
  simpa [hHapply] using this

end FourierUniqueness

section FourierAverage

variable {F : Type} [Field F] [NumberField F] (w : InfinitePlace F) (hw : w.IsReal)

def four (n : ℤ) (ψ : AdelicGL2 (𝓞 F) F → ℂ) (g : AdelicGL2 (𝓞 F) F) : ℂ :=
  ∫ θ in (0 : ℝ)..2 * Real.pi, Complex.exp (-(Complex.I * n * θ)) * ψ (g * archRot w hw θ)

theorem four_apply (n : ℤ) (ψ : AdelicGL2 (𝓞 F) F → ℂ) (g : AdelicGL2 (𝓞 F) F) :
    four w hw n ψ g =
      ∫ θ in (0 : ℝ)..2 * Real.pi, Complex.exp (-(Complex.I * n * θ)) * ψ (g * archRot w hw θ) := rfl

theorem continuous_expChar (n : ℤ) : Continuous fun θ : ℝ => Complex.exp (-(Complex.I * n * θ)) := by
  fun_prop

theorem expChar_periodic (n : ℤ) :
    Function.Periodic (fun θ : ℝ => Complex.exp (-(Complex.I * n * θ))) (2 * Real.pi) := by
  intro θ
  simp only
  have : -(Complex.I * n * ((θ + 2 * Real.pi : ℝ) : ℂ)) = -(Complex.I * n * θ) + (-n : ℤ) * (2 * Real.pi * Complex.I) := by
    push_cast; ring
  rw [this, Complex.exp_add, Complex.exp_int_mul_two_pi_mul_I, mul_one]

variable {w hw}

theorem hasArchCharacterAt₀_four (n : ℤ) (ψ : AdelicGL2 (𝓞 F) F → ℂ) :
    HasArchCharacterAt₀ F w
      ((archWeightCharℝ n).comp (rowIsometrySubgroup₀Map (ringEquivRealOfIsReal hw)
        (norm_ringEquivRealOfIsReal hw))) (four w hw n ψ) := by
  intro k g
  obtain ⟨α, rfl⟩ := exists_rotAt_eq hw (norm_symm_ringEquivRealOfIsReal F hw) k
  rw [MonoidHom.comp_apply, rowIsometrySubgroup₀Map_rotAt, archWeightCharℝ_rotSO_eq_exp]
  show four w hw n ψ (g * archRot w hw α) = _
  rw [four_apply, four_apply]
  have hP : Function.Periodic
      (fun θ : ℝ => Complex.exp (-(Complex.I * n * θ)) * ψ (g * archRot w hw θ)) (2 * Real.pi) := by
    intro θ
    have h1 := expChar_periodic n θ
    simp only at h1 ⊢
    rw [h1, archRot_periodic]
  calc (∫ θ in (0 : ℝ)..2 * Real.pi,
          Complex.exp (-(Complex.I * n * θ)) * ψ (g * archRot w hw α * archRot w hw θ))
      = ∫ θ in (0 : ℝ)..2 * Real.pi, Complex.exp (Complex.I * n * α) *
          (fun t : ℝ => Complex.exp (-(Complex.I * n * t)) * ψ (g * archRot w hw t)) (α + θ) := by
        apply intervalIntegral.integral_congr
        intro θ _
        simp only [mul_assoc, ← archRot_add]
        rw [← mul_assoc (Complex.exp _), ← Complex.exp_add]
        congr 2
        push_cast; ring
    _ = Complex.exp (Complex.I * n * α) *
          ∫ θ in (0 : ℝ)..2 * Real.pi,
            (fun t : ℝ => Complex.exp (-(Complex.I * n * t)) * ψ (g * archRot w hw t)) (α + θ) := by
        rw [intervalIntegral.integral_const_mul]
    _ = Complex.exp (Complex.I * n * α) *
          ∫ θ in (0 : ℝ)..2 * Real.pi, Complex.exp (-(Complex.I * n * θ)) * ψ (g * archRot w hw θ) := by
        congr 1
        rw [intervalIntegral.integral_comp_add_left
          (fun t : ℝ => Complex.exp (-(Complex.I * n * t)) * ψ (g * archRot w hw t)) α, add_zero]
        have := hP.intervalIntegral_add_eq α 0
        rw [zero_add] at this
        exact this

theorem continuous_four (n : ℤ) {ψ : AdelicGL2 (𝓞 F) F → ℂ} (hψ : Continuous ψ) :
    Continuous (four w hw n ψ) := by
  unfold four
  apply intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'
  exact ((continuous_expChar n).comp continuous_snd).mul
    (hψ.comp (continuous_fst.mul ((continuous_archRot w hw).comp continuous_snd)))

theorem exists_four_ne_zero {ψ : AdelicGL2 (𝓞 F) F → ℂ} (hψ : Continuous ψ) {g₁ : AdelicGL2 (𝓞 F) F}
    (h₁ : ψ g₁ ≠ 0) : ∃ n : ℤ, four w hw n ψ g₁ ≠ 0 := by
  by_contra hcon
  push Not at hcon
  set h : ℝ → ℂ := fun θ => ψ (g₁ * archRot w hw θ) with hh
  have hc : Continuous h := hψ.comp (continuous_const.mul (continuous_archRot w hw))
  have hp : Function.Periodic h (2 * Real.pi) := fun θ => by
    simp only [hh]; rw [archRot_periodic]
  have h0 := periodic_eq_zero_of_forall_integral_eq_zero h hc hp hcon
  have : h 0 = ψ g₁ := by simp only [hh]; rw [archRot_zero, mul_one]
  rw [h0] at this
  exact h₁ this.symm

theorem four_mul_left_of_forall (n : ℤ) {ψ : AdelicGL2 (𝓞 F) F → ℂ} {a : AdelicGL2 (𝓞 F) F}
    (h : ∀ x, ψ (a * x) = ψ x) (g : AdelicGL2 (𝓞 F) F) :
    four w hw n ψ (a * g) = four w hw n ψ g := by
  simp only [four_apply, mul_assoc, h]

theorem four_mul_left_of_forall_mul (n : ℤ) {ψ : AdelicGL2 (𝓞 F) F → ℂ} {a : AdelicGL2 (𝓞 F) F}
    {c : ℂ} (h : ∀ x, ψ (a * x) = c * ψ x) (g : AdelicGL2 (𝓞 F) F) :
    four w hw n ψ (a * g) = c * four w hw n ψ g := by
  simp only [four_apply, mul_assoc, h]
  rw [← intervalIntegral.integral_const_mul]
  apply intervalIntegral.integral_congr
  intro θ _
  simp only
  ring

theorem four_mul_right_of_glArch_eq_one (n : ℤ) {ψ : AdelicGL2 (𝓞 F) F → ℂ} {u : AdelicGL2 (𝓞 F) F}
    (hu : glArch (𝓞 F) F u = 1) (h : ∀ x, ψ (x * u) = ψ x) (g : AdelicGL2 (𝓞 F) F) :
    four w hw n ψ (g * u) = four w hw n ψ g := by
  simp only [four_apply]
  apply intervalIntegral.integral_congr
  intro θ _
  simp only
  rw [mul_assoc g u (archRot w hw θ), commute_of_glArch_eq_one_of_glFin_eq_one hu (glFin_archRot w hw θ),
    ← mul_assoc g, h]

theorem sum_four_mul_right (n : ℤ) {ψ : AdelicGL2 (𝓞 F) F → ℂ} (hψ : Continuous ψ)
    {m : ℕ} (reps : Fin m → AdelicGL2 (𝓞 F) F) (hreps : ∀ i, glArch (𝓞 F) F (reps i) = 1)
    (g : AdelicGL2 (𝓞 F) F) :
    ∑ i, four w hw n ψ (g * reps i) =
      ∫ θ in (0 : ℝ)..2 * Real.pi,
        Complex.exp (-(Complex.I * n * θ)) * ∑ i, ψ (g * archRot w hw θ * reps i) := by
  simp only [four_apply]
  rw [← intervalIntegral.integral_finsetSum]
  · apply intervalIntegral.integral_congr
    intro θ _
    simp only [Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [mul_assoc g (reps i) (archRot w hw θ),
      commute_of_glArch_eq_one_of_glFin_eq_one (hreps i) (glFin_archRot w hw θ), ← mul_assoc g]
  · intro i _
    apply Continuous.intervalIntegrable
    have h1 : Continuous fun θ : ℝ => g * reps i * archRot w hw θ :=
      continuous_const.mul (continuous_archRot w hw)
    exact (continuous_expChar n).mul (hψ.comp h1)

end FourierAverage

section Bookkeeping

variable {F : Type} [Field F] [NumberField F] {w : InfinitePlace F} {hw : w.IsReal}

theorem norm_expChar (n : ℤ) (θ : ℝ) : ‖Complex.exp (-(Complex.I * n * θ))‖ = 1 := by
  rw [Complex.norm_exp]
  simp

theorem norm_four_le (n : ℤ) (ψ : AdelicGL2 (𝓞 F) F → ℂ) {g : AdelicGL2 (𝓞 F) F} {M : ℝ}
    (hM : ∀ θ : ℝ, ‖ψ (g * archRot w hw θ)‖ ≤ M) :
    ‖four w hw n ψ g‖ ≤ M * |2 * Real.pi - 0| := by
  rw [four_apply]
  apply intervalIntegral.norm_integral_le_of_norm_le_const
  intro θ _
  rw [norm_mul, norm_expChar, one_mul]
  exact hM θ

theorem continuous_unipotentGL2 :
    Continuous fun q : AdeleRing (𝓞 F) F => (unipotentGL2 q : AdelicGL2 (𝓞 F) F) := by
  rw [Units.continuous_iff]
  constructor
  · show Continuous fun q : AdeleRing (𝓞 F) F => ((unipotentGL2 q : AdelicGL2 (𝓞 F) F) :
      Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 F) F))
    refine continuous_pi fun i => continuous_pi fun j => ?_
    simp only [unipotentGL2_coe]
    obtain rfl | rfl : i = 0 ∨ i = 1 := by fin_cases i <;> simp
    all_goals obtain rfl | rfl : j = 0 ∨ j = 1 := by fin_cases j <;> simp
    all_goals simp
    all_goals fun_prop
  · show Continuous fun q : AdeleRing (𝓞 F) F => ((unipotentGL2 q : AdelicGL2 (𝓞 F) F).inv :
      Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 F) F))
    refine continuous_pi fun i => continuous_pi fun j => ?_
    simp only [unipotentGL2]
    obtain rfl | rfl : i = 0 ∨ i = 1 := by fin_cases i <;> simp
    all_goals obtain rfl | rfl : j = 0 ∨ j = 1 := by fin_cases j <;> simp
    all_goals simp
    all_goals fun_prop

theorem det_unipotentGL2 (q : AdeleRing (𝓞 F) F) :
    Matrix.GeneralLinearGroup.det (unipotentGL2 q : AdelicGL2 (𝓞 F) F) = 1 := by
  apply Units.ext
  rw [Matrix.GeneralLinearGroup.val_det_apply, unipotentGL2_coe, Matrix.det_fin_two_of]
  simp

theorem isCuspidalFn_four (n : ℤ) {ψ : AdelicGL2 (𝓞 F) F → ℂ} (hψ : Continuous ψ)
    (hcusp : @IsCuspidalFn _ (adeleBorel (𝓞 F) F) _ _
      (@ProbabilityTheory.cond _ (adeleBorel (𝓞 F) F) (adelicAddHaar (𝓞 F) F) (adelicBox F))
      unipotentGL2 ψ)
    (hbdd : ∀ g : AdelicGL2 (𝓞 F) F, ∃ M : ℝ, ∀ (q : AdeleRing (𝓞 F) F) (θ : ℝ),
      ‖ψ (unipotentGL2 q * g * archRot w hw θ)‖ ≤ M) :
    @IsCuspidalFn _ (adeleBorel (𝓞 F) F) _ _
      (@ProbabilityTheory.cond _ (adeleBorel (𝓞 F) F) (adelicAddHaar (𝓞 F) F) (adelicBox F))
      unipotentGL2 (four w hw n ψ) := by
  letI : MeasurableSpace (AdeleRing (𝓞 F) F) := adeleBorel (𝓞 F) F
  haveI : BorelSpace (AdeleRing (𝓞 F) F) := borelSpace_adeleBorel (𝓞 F) F
  set ν : Measure (AdeleRing (𝓞 F) F) := ProbabilityTheory.cond (adelicAddHaar (𝓞 F) F) (adelicBox F)
    with hν
  intro g
  obtain ⟨M, hM⟩ := hbdd g
  have hle : (0 : ℝ) ≤ 2 * Real.pi := by positivity
  haveI : Fact (volume (Set.Ioc (0 : ℝ) (2 * Real.pi)) < ⊤) := ⟨measure_Ioc_lt_top⟩

  set G : AdeleRing (𝓞 F) F → ℝ → ℂ := fun q θ =>
    Complex.exp (-(Complex.I * n * θ)) * ψ (unipotentGL2 q * g * archRot w hw θ) with hG
  have hGc : Continuous (Function.uncurry G) := by
    refine ((continuous_expChar n).comp continuous_snd).mul (hψ.comp ?_)
    exact ((continuous_unipotentGL2.comp continuous_fst).mul continuous_const).mul
      ((continuous_archRot w hw).comp continuous_snd)
  have hint : Integrable (Function.uncurry G)
      (ν.prod ((volume : Measure ℝ).restrict (Set.Ioc 0 (2 * Real.pi)))) := by
    refine Integrable.of_bound hGc.aestronglyMeasurable M (Filter.Eventually.of_forall ?_)
    rintro ⟨q, θ⟩
    simp only [Function.uncurry_apply_pair, hG, norm_mul, norm_expChar, one_mul]
    exact hM q θ
  unfold constantTerm constantTermIntegrand
  simp only [four_apply]
  simp_rw [intervalIntegral.integral_of_le hle]
  change ∫ q, (∫ θ in Set.Ioc 0 (2 * Real.pi), G q θ) ∂ν = 0
  rw [MeasureTheory.integral_integral_swap hint]
  have hin : ∀ θ : ℝ, ∫ q, G q θ ∂ν =
      Complex.exp (-(Complex.I * n * θ)) * constantTerm ν unipotentGL2 ψ (g * archRot w hw θ) := by
    intro θ
    unfold constantTerm constantTermIntegrand
    rw [← integral_const_mul]
    congr 1
    funext q
    simp only [hG, mul_assoc]
  simp_rw [hin]
  have h0 : ∀ θ : ℝ, constantTerm ν unipotentGL2 ψ (g * archRot w hw θ) = 0 := fun θ => hcusp _
  simp_rw [h0, mul_zero]
  exact integral_zero _ _

theorem isKfSmooth_four (n : ℤ) {ψ : AdelicGL2 (𝓞 F) F → ℂ} (hψ : IsKfSmooth F ψ) :
    IsKfSmooth F (four w hw n ψ) := by
  rw [isKfSmooth_iff, FLT.SmoothVectors.isSmoothVector_iff_exists_isOpen_subgroup] at hψ ⊢
  obtain ⟨U, hUo, hU⟩ := hψ
  refine ⟨U, hUo, fun u hu => ?_⟩
  have hux : ∀ y, ψ (y * ((u : finiteAdelicGL2Subgroup F) : AdelicGL2 (𝓞 F) F)) = ψ y := fun y => by
    have := congrArg (fun f => FLT.SmoothVectors.RightTranslationFn.toFun f y) (hU u hu)
    exact this
  apply FLT.SmoothVectors.RightTranslationFn.ext
  intro x
  show four w hw n ψ (x * ((u : finiteAdelicGL2Subgroup F) : AdelicGL2 (𝓞 F) F)) = four w hw n ψ x
  exact four_mul_right_of_glArch_eq_one n u.2 hux x

theorem isHeckeCosetEigenfunctionAt_four (n : ℤ) {ψ : AdelicGL2 (𝓞 F) F → ℂ} (hψ : Continuous ψ)
    {N : Ideal (𝓞 F)} {v : IsDedekindDomain.HeightOneSpectrum (𝓞 F)} {c : ℂ}
    (h : SmoothCusp.IsHeckeCosetEigenfunctionAt F (levelOne (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F)
      (heckeGen (𝓞 F) F v) v ψ c) :
    SmoothCusp.IsHeckeCosetEigenfunctionAt F (levelOne (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F)
      (heckeGen (𝓞 F) F v) v (four w hw n ψ) c := by
  obtain ⟨reps, hsys, heig⟩ := h
  refine ⟨reps, hsys, fun g => ?_⟩
  have hreps : ∀ i, glArch (𝓞 F) F (reps i) = 1 := fun i => by
    obtain ⟨u, hu, u', hu', hx⟩ := HeckePair.mem_doubleCoset_iff.mp (hsys.mem_doubleCoset i)
    rw [← hx, map_mul, map_mul, glArch_eq_one_of_mem_finiteAdelicGL2Subgroup hu.2,
      glArch_eq_one_of_mem_finiteAdelicGL2Subgroup (heckeGen_mem_finiteAdelicGL2Subgroup v),
      glArch_eq_one_of_mem_finiteAdelicGL2Subgroup hu'.2, one_mul, one_mul]
  unfold SmoothCusp.heckeCosetSum
  rw [sum_four_mul_right n hψ reps hreps g, four_apply, ← intervalIntegral.integral_const_mul]
  apply intervalIntegral.integral_congr
  intro θ _
  have := heig (g * archRot w hw θ)
  unfold SmoothCusp.heckeCosetSum at this
  simp only
  rw [this]
  ring

theorem memLp_two_restrict_of_bound (D : Set (AdelicGL2 (𝓞 F) F))
    (hD : adelicGLHaar (Fin 2) (𝓞 F) F D < ⊤)
    (v : AdelicGL2 (𝓞 F) F → ℂ) (hv : Continuous v) (C : ℝ) (hC : ∀ g ∈ D, ‖v g‖ ≤ C) :
    letI : MeasurableSpace (AdelicGL2 (𝓞 F) F) := glBorel (Fin 2) (𝓞 F) F
    MemLp v 2 ((adelicGLHaar (Fin 2) (𝓞 F) F).restrict D) := by
  letI : MeasurableSpace (AdelicGL2 (𝓞 F) F) := glBorel (Fin 2) (𝓞 F) F
  haveI : BorelSpace (AdelicGL2 (𝓞 F) F) := borelSpace_glBorel (Fin 2) (𝓞 F) F
  haveI : IsFiniteMeasure ((adelicGLHaar (Fin 2) (𝓞 F) F).restrict D) :=
    ⟨by rw [Measure.restrict_apply_univ]; exact hD⟩
  refine MemLp.of_bound hv.aestronglyMeasurable C ?_
  rw [ae_restrict_iff (isClosed_le hv.norm continuous_const).measurableSet]
  exact ae_of_all _ hC

end Bookkeeping

section Modulus

variable {F : Type} [Field F] [NumberField F]

open NumberField.TateGlobal NumberField.AdelicVolume

theorem ideleNorm_det_mul (g h : AdelicGL2 (𝓞 F) F) :
    ideleNorm F (Matrix.GeneralLinearGroup.det (g * h)) =
      ideleNorm F (Matrix.GeneralLinearGroup.det g) * ideleNorm F (Matrix.GeneralLinearGroup.det h) := by
  rw [map_mul, ideleNorm_mul]

theorem ideleNorm_det_mul_archRot (w : InfinitePlace F) (hw : w.IsReal) (g : AdelicGL2 (𝓞 F) F) (θ : ℝ) :
    ideleNorm F (Matrix.GeneralLinearGroup.det (g * archRot w hw θ)) =
      ideleNorm F (Matrix.GeneralLinearGroup.det g) := by
  rw [map_mul, det_archRot, mul_one]

theorem ideleNorm_det_unipotentGL2_mul (q : AdeleRing (𝓞 F) F) (g : AdelicGL2 (𝓞 F) F) :
    ideleNorm F (Matrix.GeneralLinearGroup.det (unipotentGL2 q * g)) =
      ideleNorm F (Matrix.GeneralLinearGroup.det g) := by
  rw [map_mul, det_unipotentGL2, one_mul]

theorem prod_pow_mult_le {a b : InfinitePlace F → ℝ} (h0 : ∀ v, 0 ≤ a v) (h : ∀ v, a v ≤ b v) :
    ∏ v : InfinitePlace F, a v ^ v.mult ≤ ∏ v : InfinitePlace F, b v ^ v.mult :=
  Finset.prod_le_prod (fun v _ => pow_nonneg (h0 v) _) (fun v _ => pow_le_pow_left₀ (h0 v) (h v) _)

theorem ideleNorm_det_siegel {c u d₁ d₂ : ℝ} (hd₁ : 0 < d₁) {s : AdelicGL2 (𝓞 F) F}
    (hs : s ∈ centreCutSiegelSet F c u d₁ d₂) :
    d₁ ^ (∑ v : InfinitePlace F, v.mult) ≤ ideleNorm F (Matrix.GeneralLinearGroup.det s) ∧
      ideleNorm F (Matrix.GeneralLinearGroup.det s) ≤ d₂ ^ (∑ v : InfinitePlace F, v.mult) := by
  have hint := (mem_centreCutSiegelSet_iff.mp hs).1
  have hdet := (mem_centreCutSiegelSet_iff.mp hs).2.2.2
  rw [NumberField.TateGlobal.ideleNorm_det_eq_prod_archDetNorm_pow_mult F s hint,
    ← Finset.prod_pow_eq_pow_sum, ← Finset.prod_pow_eq_pow_sum]
  exact ⟨prod_pow_mult_le (fun _ => hd₁.le) fun v => (hdet v).1,
    prod_pow_mult_le (fun v => (archDetNorm_pos v s).le) fun v => (hdet v).2⟩

theorem exists_ideleNorm_det_mem_Icc {c u d₁ d₂ : ℝ} (hd₁ : 0 < d₁) (T : Finset (AdelicGL2 (𝓞 F) F))
    (hT : T.Nonempty) :
    ∃ e₁ e₂ : ℝ, 0 < e₁ ∧ e₁ ≤ e₂ ∧
      ∀ g ∈ (⋃ x ∈ T, (· * x) '' centreCutSiegelSet F c u d₁ d₂),
        ideleNorm F (Matrix.GeneralLinearGroup.det g) ∈ Set.Icc e₁ e₂ := by
  set m := T.inf' hT (fun x => ideleNorm F (Matrix.GeneralLinearGroup.det x)) with hm
  set M := T.sup' hT (fun x => ideleNorm F (Matrix.GeneralLinearGroup.det x)) with hM
  have hm0 : 0 < m := by
    rw [hm, Finset.lt_inf'_iff]
    intro x _; exact ideleNorm_pos _
  have hmM : m ≤ M := by
    obtain ⟨x, hx⟩ := hT
    exact (Finset.inf'_le _ hx).trans (Finset.le_sup' (fun x => ideleNorm F (Matrix.GeneralLinearGroup.det x)) hx)
  by_cases hd : d₁ ≤ d₂
  · refine ⟨d₁ ^ (∑ v : InfinitePlace F, v.mult) * m, d₂ ^ (∑ v : InfinitePlace F, v.mult) * M,
      mul_pos (pow_pos hd₁ _) hm0,
      mul_le_mul (pow_le_pow_left₀ hd₁.le hd _) hmM hm0.le (pow_nonneg (hd₁.le.trans hd) _), ?_⟩
    intro g hg
    simp only [Set.mem_iUnion, Set.mem_image] at hg
    obtain ⟨x, hx, s, hs, rfl⟩ := hg
    have h1 := ideleNorm_det_siegel hd₁ hs
    rw [Set.mem_Icc, ideleNorm_det_mul]
    have hmx : m ≤ ideleNorm F (Matrix.GeneralLinearGroup.det x) := Finset.inf'_le _ hx
    have hxM : ideleNorm F (Matrix.GeneralLinearGroup.det x) ≤ M :=
      Finset.le_sup' (fun x => ideleNorm F (Matrix.GeneralLinearGroup.det x)) hx
    constructor
    · exact mul_le_mul h1.1 hmx hm0.le (ideleNorm_pos _).le
    · exact mul_le_mul h1.2 hxM (ideleNorm_pos _).le (pow_nonneg (hd₁.le.trans hd) _)
  ·
    refine ⟨1, 1, one_pos, le_rfl, ?_⟩
    intro g hg
    simp only [Set.mem_iUnion, Set.mem_image] at hg
    obtain ⟨x, _, s, hs, rfl⟩ := hg
    obtain ⟨v₀⟩ := (inferInstance : Nonempty (InfinitePlace F))
    have h4 := (mem_centreCutSiegelSet_iff.mp hs).2.2.2 v₀
    exact absurd (h4.1.trans h4.2) hd

end Modulus

section Realization

variable {F : Type} [Field F] [NumberField F]

open NumberField.TateGlobal

theorem rightConv_mul_left_of_forall {φ f : AdelicGL2 (𝓞 F) F → ℂ} {h : AdelicGL2 (𝓞 F) F}
    (hφ : ∀ x, φ (h * x) = φ x) (g : AdelicGL2 (𝓞 F) F) :
    rightConv F φ f (h * g) = rightConv F φ f g := by
  rw [← rightConv_comp_mul_left]
  simp only [hφ]

theorem rightConv_mul_left_of_forall_mul {φ f : AdelicGL2 (𝓞 F) F → ℂ} {h : AdelicGL2 (𝓞 F) F} {c : ℂ}
    (hφ : ∀ x, φ (h * x) = c * φ x) (g : AdelicGL2 (𝓞 F) F) :
    rightConv F φ f (h * g) = c * rightConv F φ f g := by
  letI : MeasurableSpace (AdelicGL2 (𝓞 F) F) := glBorel (Fin 2) (𝓞 F) F
  rw [← rightConv_comp_mul_left, rightConv_apply, rightConv_apply]
  simp only [hφ, mul_assoc]
  exact MeasureTheory.integral_const_mul _ _

theorem isLsXiFunction_rightConv {ξ : (⊤ : Subgroup (AdeleRing (𝓞 F) F)ˣ) →* ℂˣ}
    {φ : AdelicGL2 (𝓞 F) F → ℂ} (hφ : IsLsXiFunction (𝓞 F) F ⊤ ξ φ) (f : AdelicGL2 (𝓞 F) F → ℂ) :
    IsLsXiFunction (𝓞 F) F ⊤ ξ (rightConv F φ f) where
  left_invariant γ g := rightConv_mul_left_of_forall (fun x => hφ.left_invariant γ x) g
  central_transform z g := rightConv_mul_left_of_forall_mul (fun x => hφ.central_transform z x) g

theorem centralScalar_mul_comm (z : (AdeleRing (𝓞 F) F)ˣ) (g : AdelicGL2 (𝓞 F) F) :
    centralScalar (𝓞 F) F z * g = g * centralScalar (𝓞 F) F z := by
  apply Units.ext
  rw [Units.val_mul, Units.val_mul]
  show (Matrix.scalar (Fin 2) (z : AdeleRing (𝓞 F) F)) * (g : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 F) F)) =
    (g : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 F) F)) * Matrix.scalar (Fin 2) (z : AdeleRing (𝓞 F) F)
  exact (Matrix.scalar_commute _ (fun r' => Commute.all _ r') _).eq

theorem isLsXiFunction_four {w : InfinitePlace F} {hw : w.IsReal} (n : ℤ)
    {ξ : (⊤ : Subgroup (AdeleRing (𝓞 F) F)ˣ) →* ℂˣ}
    {ψ : AdelicGL2 (𝓞 F) F → ℂ} (hψ : IsLsXiFunction (𝓞 F) F ⊤ ξ ψ) :
    IsLsXiFunction (𝓞 F) F ⊤ ξ (four w hw n ψ) where
  left_invariant γ g := four_mul_left_of_forall n (fun x => hψ.left_invariant γ x) g
  central_transform z g := four_mul_left_of_forall_mul n (fun x => hψ.central_transform z x) g

theorem exists_bound_of_ideleNorm_det_mem_Icc {c u d₁ d₂ : ℝ} {T : Finset (AdelicGL2 (𝓞 F) F)}
    (hd₁ : 0 < d₁) (hd : d₁ < d₂)
    (hcov : CoversModCentre F (⋃ x ∈ T, (· * x) '' centreCutSiegelSet F c u d₁ d₂))
    {ξ : (⊤ : Subgroup (AdeleRing (𝓞 F) F)ˣ) →* ℂˣ} {ψ : AdelicGL2 (𝓞 F) F → ℂ}
    (hψ : IsLsXiFunction (𝓞 F) F ⊤ ξ ψ) {B : ℝ}
    (hB : ∀ g ∈ (⋃ x ∈ T, (· * x) '' centreCutSiegelSet F c u d₁ d₂), ‖ψ g‖ ≤ B)
    (e₁ e₂ : ℝ) (he₁ : 0 < e₁) (he : e₁ ≤ e₂) :
    ∃ M : ℝ, ∀ y : AdelicGL2 (𝓞 F) F,
      ideleNorm F (Matrix.GeneralLinearGroup.det y) ∈ Set.Icc e₁ e₂ → ‖ψ y‖ ≤ M := by
  obtain ⟨Z, hZ⟩ :=
    AutomorphicForm.exists_finset_globalPoints_mul_mul_centralScalar_mem_of_coversModCentre_of_ideleNorm_det_mem_Icc
      F c u d₁ d₂ T hd₁ hd hcov e₁ e₂ he₁ he
  refine ⟨(∑ z ∈ Z, ‖(((ξ ⟨z, Subgroup.mem_top z⟩)⁻¹ : ℂˣ) : ℂ)‖) * max B 0, fun y hy => ?_⟩
  obtain ⟨γ, z, hz, hmem⟩ := hZ y hy
  have h1 : ‖ψ (globalPoints (𝓞 F) F γ * y * centralScalar (𝓞 F) F z)‖ ≤ max B 0 :=
    (hB _ hmem).trans (le_max_left _ _)
  have h2 : ψ (globalPoints (𝓞 F) F γ * y * centralScalar (𝓞 F) F z) =
      ((ξ ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ) * ψ y := by
    rw [mul_assoc, hψ.left_invariant, ← centralScalar_mul_comm]
    exact hψ.central_transform ⟨z, Subgroup.mem_top z⟩ y
  have h3 : ψ y = (((ξ ⟨z, Subgroup.mem_top z⟩)⁻¹ : ℂˣ) : ℂ) *
      ψ (globalPoints (𝓞 F) F γ * y * centralScalar (𝓞 F) F z) := by
    rw [h2, ← mul_assoc, ← Units.val_mul, inv_mul_cancel, Units.val_one, one_mul]
  rw [h3, norm_mul]
  have h4 : ‖(((ξ ⟨z, Subgroup.mem_top z⟩)⁻¹ : ℂˣ) : ℂ)‖ ≤
      ∑ z ∈ Z, ‖(((ξ ⟨z, Subgroup.mem_top z⟩)⁻¹ : ℂˣ) : ℂ)‖ :=
    Finset.single_le_sum (f := fun z => ‖(((ξ ⟨z, Subgroup.mem_top z⟩)⁻¹ : ℂˣ) : ℂ)‖)
      (fun _ _ => norm_nonneg _) hz
  exact mul_le_mul h4 h1 (norm_nonneg _) (Finset.sum_nonneg fun _ _ => norm_nonneg _)

theorem nonempty_of_coversModCentre {c u d₁ d₂ : ℝ} {T : Finset (AdelicGL2 (𝓞 F) F)}
    (hcov : CoversModCentre F (⋃ x ∈ T, (· * x) '' centreCutSiegelSet F c u d₁ d₂)) : T.Nonempty := by
  obtain ⟨γ, z, hmem⟩ := hcov 1
  simp only [Set.mem_iUnion] at hmem
  obtain ⟨x, hx, _⟩ := hmem
  exact ⟨x, hx⟩

end Realization

end ArchTypeFourier

end AutomorphicForm

end

open AutomorphicForm.ArchTypeFourier NumberField.TateGlobal in
theorem solution
    (F : Type) [Field F] [NumberField F] (c u d₁ d₂ : ℝ) (T : Finset (AdelicGL2 (𝓞 F) F))
    (hd : d₁ < d₂)
    (hc : 0 < c) (hd₁ : 0 < d₁)
    (hcov : CoversModCentre F (⋃ x ∈ T, (· * x) '' centreCutSiegelSet F c u d₁ d₂))
    (Θ : HeckeEigensystem F ℂ)
    (hΘ : ArchOccursInClassOf F (⋃ x ∈ T, (· * x) '' centreCutSiegelSet F c u d₁ d₂) Θ (fun _ => True))
    (w : InfinitePlace F) (hw : w.IsReal) :
    ∃ n : ℤ,
      ArchOccursInClassOf F (⋃ x ∈ T, (· * x) '' centreCutSiegelSet F c u d₁ d₂) Θ
        (fun φ => HasArchCharacterAt₀ F w
          ((archWeightCharℝ n).comp (rowIsometrySubgroup₀Map (ringEquivRealOfIsReal hw)
            (norm_ringEquivRealOfIsReal hw))) φ) := by
  classical
  letI : MeasurableSpace (AdelicGL2 (𝓞 F) F) := glBorel (Fin 2) (𝓞 F) F
  set D : Set (AdelicGL2 (𝓞 F) F) := ⋃ x ∈ T, (· * x) '' centreCutSiegelSet F c u d₁ d₂ with hDdef
  obtain ⟨Θ', hΘ', R', hR', -⟩ := hΘ
  have hR'c : Continuous R'.toFun := hR'

  obtain ⟨f, hf, -, hfs, g₁, hg₁⟩ :=
    AutomorphicForm.exists_isFactorizableTestFn_rightConv_ne_zero_of_levelOne_invariant F
      Θ'.toRawCentral.level Θ'.toRawCentral.level_ne_bot R'.toFun hR'c R'.exists_ne_zero R'.level_invariant
  set ψ : AdelicGL2 (𝓞 F) F → ℂ := rightConv F R'.toFun f with hψdef

  obtain ⟨hcuspψ, hKfψ, hlevψ, hHeckeψ⟩ :=
    AutomorphicForm.isCuspidalFn_isKfSmooth_levelInvariant_isHeckeCosetEigenfunctionAt_rightConv_of_isFactorizableTestFn_of_support_subset
      F c u d₁ d₂ T Θ'.toRawCentral R' hR'c f hf hfs
  have hψc : Continuous ψ :=
    (AutomorphicForm.continuous_rightConv_and_contDiff_of_isFactorizableTestFn F R'.toFun hR'c f hf).1
  have hLs : IsLsXiFunction (𝓞 F) F ⊤ R'.centralChar R'.toFun :=
    ((AutomorphicForm.lsXiMemberAt_iff (𝓞 F) F (adelicGLHaar (Fin 2) (𝓞 F) F) ⊤ R'.centralChar D
      R'.toFun).mp R'.smoothCusp.1.1).1
  have hLsψ : IsLsXiFunction (𝓞 F) F ⊤ R'.centralChar ψ := isLsXiFunction_rightConv hLs f
  have hceψ : ∀ v, v ∉ R'.exceptionalSet → ∀ g,
      ψ (centralScalar (𝓞 F) F (Matrix.GeneralLinearGroup.det (heckeGen (𝓞 F) F v)) * g) =
        Θ'.toRawCentral.b v * ψ g := fun v hv g =>
    rightConv_mul_left_of_forall_mul (fun x => R'.central_eigen v hv x) g

  obtain ⟨C, hC⟩ :=
    AutomorphicForm.exists_forall_norm_rightConv_le_mul_eLpNorm_of_isSmoothCuspAutomorphicFnAt_of_coversModCentre
      F c u d₁ d₂ T hc hd₁ hd hcov R'.centralChar f hf
  have hBD : ∀ g ∈ D, ‖ψ g‖ ≤ C * (eLpNorm R'.toFun 2 ((adelicGLHaar (Fin 2) (𝓞 F) F).restrict D)).toReal :=
    hC R'.toFun R'.smoothCusp hR'c
  have hslab := fun e₁ e₂ (he₁ : 0 < e₁) (he : e₁ ≤ e₂) =>
    exists_bound_of_ideleNorm_det_mem_Icc hd₁ hd hcov hLsψ hBD e₁ e₂ he₁ he

  have hbdd_cusp : ∀ g : AdelicGL2 (𝓞 F) F, ∃ M : ℝ, ∀ (q : AdeleRing (𝓞 F) F) (θ : ℝ),
      ‖ψ (unipotentGL2 q * g * archRot w hw θ)‖ ≤ M := by
    intro g
    obtain ⟨M, hM⟩ := hslab _ _ (ideleNorm_pos (Matrix.GeneralLinearGroup.det g)) le_rfl
    refine ⟨M, fun q θ => hM _ ?_⟩
    rw [ideleNorm_det_mul_archRot, ideleNorm_det_unipotentGL2_mul]
    exact ⟨le_rfl, le_rfl⟩
  obtain ⟨e₁, e₂, he₁, he, hDe⟩ :=
    exists_ideleNorm_det_mem_Icc (c := c) (u := u) (d₂ := d₂) hd₁ T (nonempty_of_coversModCentre hcov)
  obtain ⟨MD, hMD⟩ := hslab e₁ e₂ he₁ he
  have hbdd_D : ∀ g ∈ D, ∀ θ : ℝ, ‖ψ (g * archRot w hw θ)‖ ≤ MD := fun g hg θ =>
    hMD _ (by rw [ideleNorm_det_mul_archRot]; exact hDe g hg)
  have hDfin : adelicGLHaar (Fin 2) (𝓞 F) F D < ⊤ :=
    measure_biUnion_lt_top T.finite_toSet
      (fun x _ => AutomorphicForm.adelicGLHaar_mul_right_centreCutSiegelSet_lt_top F hc u hd₁ d₂ x)

  obtain ⟨n, hn⟩ := exists_four_ne_zero (w := w) (hw := hw) hψc hg₁

  let Rn : SmoothCuspRealizationAt F
      (productionPinsOf F D (fun N => levelOne (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F)
        (fun v => heckeGen (𝓞 F) F v) (adelicBox F)) Θ'.toRawCentral :=
    { toFun := four w hw n ψ
      exists_ne_zero := ⟨g₁, hn⟩
      centralChar := R'.centralChar
      smoothCusp := by
        refine ⟨⟨?_, isCuspidalFn_four n hψc hcuspψ hbdd_cusp⟩, isKfSmooth_four n hKfψ⟩
        exact (AutomorphicForm.lsXiMemberAt_iff (𝓞 F) F (adelicGLHaar (Fin 2) (𝓞 F) F) ⊤ R'.centralChar D
          (four w hw n ψ)).mpr
          ⟨isLsXiFunction_four n hLsψ,
            memLp_two_restrict_of_bound D hDfin (four w hw n ψ) (continuous_four n hψc) _
              fun g hg => norm_four_le n ψ (hbdd_D g hg)⟩
      level_invariant := fun g u' hu' =>
        four_mul_right_of_glArch_eq_one n hu'.2 (fun x => hlevψ x u' hu') g
      exceptionalSet := R'.exceptionalSet
      hecke_eigen := fun v hv => isHeckeCosetEigenfunctionAt_four n hψc (hHeckeψ v hv)
      central_eigen := fun v hv g => four_mul_left_of_forall_mul n (hceψ v hv) g }
  refine ⟨n, Θ', hΘ', Rn, ?_, hasArchCharacterAt₀_four n ψ⟩
  exact continuous_four n hψc

end S_AutomorphicForm_exists_archOccursInClassOf_archWeightChar_of_coversModCentre_of_pos
end P2MW
export P2MW.S_AutomorphicForm_exists_archOccursInClassOf_archWeightChar_of_coversModCentre_of_pos (solution)
