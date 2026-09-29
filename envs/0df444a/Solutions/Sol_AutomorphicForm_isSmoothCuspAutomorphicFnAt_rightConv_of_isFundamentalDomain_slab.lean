-- Prove2me | solution 1 for AutomorphicForm.isSmoothCuspAutomorphicFnAt_rightConv_of_isFundamentalDomain_slab
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:05.340288+00:00
-- url     : https://prove2.me/submissions/39b1db2c-ac0f-5029-9001-3ca7c35bcef7

import Definitions.Def_AutomorphicForm_UnitFactorizableOfType
import Definitions.Def_NumberField_TateGlobalZeta
import Theorems.Thm_NumberField_AdeleRing_secondCountableTopology
import Theorems.Thm_NumberField_AdeleRing_secondCountableTopology_generalLinearGroup_finTwo
import Theorems.Thm_NumberField_TateGlobal_exists_continuous_monoidHom_ideleNorm_apply_eq
import Theorems.Thm_NumberField_TateGlobal_continuous_ideleNorm_det
import Theorems.Thm_AutomorphicForm_ideleNorm_det_globalPoints
import Theorems.Thm_NumberField_AdelicHaar_isMulRightInvariant_adelicGLHaar
import Theorems.Thm_AutomorphicForm_rightConv_apply_mul_eq_rightConv_comp_inv_mul_apply
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AutomorphicForm_isSmoothCuspAutomorphicFnAt_rightConv_of_isFundamentalDomain_slab
p2m_attr_erase "instance" "instCountableOfNumberField_definitions RestrictedProduct.SecondCountableTopology_of_principal instCountableElemSetSetsCofinite_definitions instFiniteResidueFieldAdicCompletionRingOfIntegersWithZeroMultiplicativeInt_definitions NumberField.instCompactSpaceAdicCompletionIntegers Rat.adicCompletion.locallyCompactSpace NumberField.instFiniteResidueFieldAdicCompletionIntegers instWeaklyLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions"
p2m_attr_erase "simp" "ContinuousAddEquiv.restrictedProductPi_apply RestrictedProduct.flatten_homeomorph_apply RestrictedProduct.flatten_homeomorph'_symm_apply ContinuousMulEquiv.restrictedProductPi_symm_apply RestrictedProduct.flatten_homeomorph'_apply RestrictedProduct.flatten_homeomorph_symm_apply ContinuousMulEquiv.restrictedProductPi_apply ContinuousAddEquiv.restrictedProductPi_symm_apply RingEquiv.restrictedProductCongr_symm_apply RingEquiv.restrictedProductCongrRight_apply MulEquiv.restrictedProductCongrRight_apply Equiv.restrictedProductProd_symm_apply_coe Equiv.restrictedProductCongrRight_apply AddEquiv.restrictedProductCongr_apply Equiv.restrictedProductCongrLeft'_symm_apply_apply Equiv.restrictedProductCongr_apply_apply Equiv.restrictedProductCongrLeft_apply_apply RestrictedProduct.flatten_equiv'_apply AddEquiv.restrictedProductCongrRight_apply Equiv.restrictedProductCongr_symm_apply Equiv.restrictedProductCongrRight_symm_apply RestrictedProduct.flatten_equiv'_symm_apply AddEquiv.restrictedProductCongrLeft'_apply Equiv.restrictedProductCongrLeft'_apply RestrictedProduct.flatten_apply RingEquiv.restrictedProductCongr_apply_apply RingEquiv.restrictedProductCongrLeft'_apply Equiv.restrictedProductProd_apply RestrictedProduct.flatten_equiv_apply RestrictedProduct.flatten_equiv_symm_apply LinearEquiv.restrictedProductCongrLeft'_apply RestrictedProduct.not_mem_support RestrictedProduct.mem_structureSubring_iff RestrictedProduct.not_mem_mulSupport RestrictedProduct.support_neg RestrictedProduct.mem_indexSupport_iff RestrictedProduct.mulSupport_inv RestrictedProduct.mapAlongLinearMap_apply LanglandsTunnell.TateLocal.charExt_coe_units LanglandsTunnell.TateLocal.modulus_one"
p2m_attr_erase "simp" "LanglandsTunnell.TateLocal.modulus_zero LanglandsTunnell.TateLocal.modulus_coe_units LanglandsTunnell.TateLocal.charExt_zero"

set_option autoImplicit false

open MeasureTheory NumberField NumberField.AdelicHaar NumberField.AdelicLevel NumberField.AdelicBox
open IsDedekindDomain AutomorphicForm
open scoped ENNReal NNReal Topology

attribute [local instance] NumberField.AdelicHaar.glBorel NumberField.AdelicHaar.borelSpace_glBorel
attribute [local instance] NumberField.AdelicHaar.adeleBorel NumberField.AdelicHaar.borelSpace_adeleBorel
attribute [local instance] NumberField.AdelicHaar.isAddHaarMeasure_adelicAddHaar

noncomputable section

namespace P2mConvCusp

variable {L : Type} [Field L] [NumberField L]

theorem isHaar : (adelicGLHaar (Fin 2) (𝓞 L) L).IsHaarMeasure := isHaarMeasure_adelicGLHaar (Fin 2) (𝓞 L) L

attribute [local instance] isHaar

scoped instance secondCountable_gl : SecondCountableTopology (AdelicGL2 (𝓞 L) L) :=
  NumberField.AdeleRing.secondCountableTopology_generalLinearGroup_finTwo L

scoped instance secondCountable_adele : SecondCountableTopology (AdeleRing (𝓞 L) L) :=
  NumberField.AdeleRing.secondCountableTopology L

scoped instance isMulRightInvariant : (adelicGLHaar (Fin 2) (𝓞 L) L).IsMulRightInvariant :=
  NumberField.AdelicHaar.isMulRightInvariant_adelicGLHaar L

variable (L)

theorem isLsXi_rightConv {Z : Subgroup (AdeleRing (𝓞 L) L)ˣ} {ξ : Z →* ℂˣ} (v φ : AdelicGL2 (𝓞 L) L → ℂ)
    (hv : IsLsXiFunction (𝓞 L) L Z ξ v) : IsLsXiFunction (𝓞 L) L Z ξ (rightConv L v φ) := by
  refine ⟨fun γ g => ?_, fun z g => ?_⟩
  · rw [← rightConv_comp_mul_left]
    congr 1
    funext x
    exact hv.left_invariant γ x
  · rw [← rightConv_comp_mul_left, rightConv_apply, rightConv_apply, ← integral_const_mul]
    congr 1
    funext x
    rw [hv.central_transform z (g * x), mul_assoc]

theorem rightConv_apply_mul_of_left_invariant (v φ : AdelicGL2 (𝓞 L) L → ℂ) {u : AdelicGL2 (𝓞 L) L}
    (hφu : ∀ g, φ (u * g) = φ g) (g : AdelicGL2 (𝓞 L) L) : rightConv L v φ (g * u) = rightConv L v φ g := by
  rw [AutomorphicForm.rightConv_apply_mul_eq_rightConv_comp_inv_mul_apply]
  congr 1
  funext y
  have := hφu (u⁻¹ * y)
  rw [mul_inv_cancel_left] at this
  exact this.symm

theorem isKfSmooth_of_invariant {N : Ideal (𝓞 L)} (hN : N ≠ ⊥) (w : AdelicGL2 (𝓞 L) L → ℂ)
    (hw : ∀ g, ∀ u ∈ levelOne (𝓞 L) L N ⊓ finiteAdelicGL2Subgroup L, w (g * u) = w g) : IsKfSmooth L w := by
  rw [isKfSmooth_iff, FLT.SmoothVectors.isSmoothVector_iff_isOpen_stabilizer]
  refine Subgroup.isOpen_mono (H₁ := (levelOne (𝓞 L) L N).comap (finiteAdelicGL2Subgroup L).subtype) ?_
    ((isOpen_levelOne (𝓞 L) L hN).preimage continuous_subtype_val)
  intro k hk
  rw [Subgroup.mem_comap] at hk
  rw [MulAction.mem_stabilizer_iff]
  refine FLT.SmoothVectors.RightTranslationFn.ext fun x => ?_
  simp only [Subgroup.smul_def, FLT.SmoothVectors.RightTranslationFn.toFun_smul,
    FLT.SmoothVectors.RightTranslationFn.toFun_mk]
  exact hw x _ (Subgroup.mem_inf.mpr ⟨hk, k.2⟩)

theorem integrable_mul_of_continuous (F φ : AdelicGL2 (𝓞 L) L → ℂ) (hF : Continuous F) (hφ : Continuous φ)
    (hφc : HasCompactSupport φ) : Integrable (fun x => F x * φ x) (adelicGLHaar (Fin 2) (𝓞 L) L) :=
  (hF.mul hφ).integrable_of_hasCompactSupport hφc.mul_left

theorem continuous_rightConv (v φ : AdelicGL2 (𝓞 L) L → ℂ) (hv : Continuous v) (hφ : Continuous φ)
    (hφc : HasCompactSupport φ) : Continuous (rightConv L v φ) := by
  have h : rightConv L v φ = fun g => ∫ x in tsupport φ, v (g * x) * φ x ∂adelicGLHaar (Fin 2) (𝓞 L) L := by
    funext g
    rw [rightConv_apply, setIntegral_eq_integral_of_forall_compl_eq_zero]
    intro x hx
    rw [image_eq_zero_of_notMem_tsupport hx, mul_zero]
  rw [h]
  exact continuous_parametric_integral_of_continuous
    (by fun_prop : Continuous (Function.uncurry fun (g x : AdelicGL2 (𝓞 L) L) => v (g * x) * φ x)) hφc

theorem continuous_unipotentGL2 :
    Continuous fun q : AdeleRing (𝓞 L) L => (unipotentGL2 q : AdelicGL2 (𝓞 L) L) := by
  refine Units.continuous_iff.2 ⟨?_, ?_⟩
  · refine continuous_matrix fun i j => ?_
    fin_cases i <;> fin_cases j <;>
      simp [unipotentGL2] <;> first | exact continuous_const | exact continuous_id
  · have h : ∀ q : AdeleRing (𝓞 L) L,
        (((unipotentGL2 q)⁻¹ : AdelicGL2 (𝓞 L) L) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 L) L)) = !![1, -q; 0, 1] :=
      fun q => rfl
    simp_rw [h]
    refine continuous_matrix fun i j => ?_
    fin_cases i <;> fin_cases j <;>
      simp <;> first | exact continuous_const | exact continuous_id | exact continuous_neg

theorem isCuspidalFn_rightConv (v φ : AdelicGL2 (𝓞 L) L → ℂ) (hv : Continuous v) (hφ : Continuous φ)
    (hφc : HasCompactSupport φ)
    (hcusp : IsCuspidalFn (ProbabilityTheory.cond (adelicAddHaar (𝓞 L) L) (adelicBox L)) unipotentGL2 v) :
    IsCuspidalFn (ProbabilityTheory.cond (adelicAddHaar (𝓞 L) L) (adelicBox L)) unipotentGL2 (rightConv L v φ) := by
  set ν : Measure (AdeleRing (𝓞 L) L) := ProbabilityTheory.cond (adelicAddHaar (𝓞 L) L) (adelicBox L) with hν
  set μ : Measure (AdelicGL2 (𝓞 L) L) := adelicGLHaar (Fin 2) (𝓞 L) L with hμ
  haveI : IsProbabilityMeasure ν := isProbabilityMeasure_cond_adelicBox L
  intro g
  show ∫ q, rightConv L v φ (unipotentGL2 q * g) ∂ν = 0
  simp_rw [rightConv_apply]

  set F : AdeleRing (𝓞 L) L → AdelicGL2 (𝓞 L) L → ℂ := fun q x => v (unipotentGL2 q * g * x) * φ x with hF
  have hcont : Continuous fun p : AdeleRing (𝓞 L) L × AdelicGL2 (𝓞 L) L =>
      v ((unipotentGL2 p.1 : AdelicGL2 (𝓞 L) L) * g * p.2) :=
    hv.comp ((((continuous_unipotentGL2 L).comp continuous_fst).mul continuous_const).mul continuous_snd)
  have hFc : Continuous (Function.uncurry F) := hcont.mul (hφ.comp continuous_snd)

  obtain ⟨C, hCc, hBC⟩ := exists_isCompact_adelicBox_subset L
  obtain ⟨M, hM⟩ := (hCc.prod hφc).exists_bound_of_continuousOn hcont.continuousOn

  have h1 : ν (adelicBox L)ᶜ = 0 := by
    have := ProbabilityTheory.ae_cond_mem (μ := adelicAddHaar (𝓞 L) L) (measurableSet_adelicBox L)
    rw [ae_iff] at this
    exact this
  have hae : ∀ᵐ p ∂(ν.prod μ), p.1 ∈ adelicBox L := by
    rw [ae_iff]
    refine measure_mono_null (t := (adelicBox L)ᶜ ×ˢ Set.univ) (fun p hp => ⟨hp, Set.mem_univ _⟩) ?_
    rw [Measure.prod_prod, h1, zero_mul]

  have hint : Integrable (Function.uncurry F) (ν.prod μ) := by
    refine Integrable.mono' (g := fun p => max M 0 * ‖φ p.2‖) ?_ hFc.aestronglyMeasurable ?_
    · exact (integrable_const (max M 0)).mul_prod (hφ.integrable_of_hasCompactSupport hφc).norm
    · filter_upwards [hae] with p hp
      simp only [Function.uncurry, hF, norm_mul]
      by_cases hx : p.2 ∈ tsupport φ
      · exact mul_le_mul_of_nonneg_right ((hM ⟨p.1, p.2⟩ ⟨hBC hp, hx⟩).trans (le_max_left _ _)) (norm_nonneg _)
      · rw [image_eq_zero_of_notMem_tsupport hx, norm_zero, mul_zero, mul_zero]
  rw [integral_integral_swap hint]
  have h2 : ∀ x, ∫ q, F q x ∂ν = 0 := fun x => by
    show ∫ q, v (unipotentGL2 q * g * x) * φ x ∂ν = 0
    rw [integral_mul_const]
    have := hcusp (g * x)
    change ∫ q, v (unipotentGL2 q * (g * x)) ∂ν = 0 at this
    simp_rw [mul_assoc]
    rw [this, zero_mul]
  simp_rw [h2, integral_zero]

section Slab

def slab (α β : ℝ) : Set (AdelicGL2 (𝓞 L) L) :=
  {g | NumberField.TateGlobal.ideleNorm L (Matrix.GeneralLinearGroup.det g) ∈ Set.Icc α β}

theorem measurableSet_slab (α β : ℝ) : MeasurableSet (slab L α β) :=
  measurableSet_Icc.preimage (NumberField.TateGlobal.continuous_ideleNorm_det L).measurable

variable {L}

theorem countable_numberField : Countable L :=
  (Module.Free.chooseBasis ℚ L).equivFun.toEquiv.countable_iff.2 inferInstance

theorem countable_gl2 : Countable (GL (Fin 2) L) := by
  haveI := countable_numberField (L := L)
  haveI : Countable (Matrix (Fin 2) (Fin 2) L) := inferInstanceAs (Countable (Fin 2 → Fin 2 → L))
  exact Function.Injective.countable (f := (Units.val : GL (Fin 2) L → _)) Units.val_injective

scoped instance countable_range : Countable (globalPoints (𝓞 L) L).range := by
  haveI := countable_gl2 (L := L)
  exact Function.Surjective.countable (MonoidHom.rangeRestrict_surjective (globalPoints (𝓞 L) L))

variable (L)

theorem centralScalar_comm (z : (AdeleRing (𝓞 L) L)ˣ) (g : AdelicGL2 (𝓞 L) L) :
    centralScalar (𝓞 L) L z * g = g * centralScalar (𝓞 L) L z := by
  apply Units.ext
  show Matrix.scalar (Fin 2) (z : AdeleRing (𝓞 L) L) * (g : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 L) L)) =
    (g : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 L) L)) * Matrix.scalar (Fin 2) (z : AdeleRing (𝓞 L) L)
  exact (Matrix.scalar_commute (z : AdeleRing (𝓞 L) L) (Commute.all _) _).eq

theorem det_centralScalar (z : (AdeleRing (𝓞 L) L)ˣ) :
    Matrix.GeneralLinearGroup.det (centralScalar (𝓞 L) L z) = z * z := by
  apply Units.ext
  rw [Matrix.GeneralLinearGroup.val_det_apply, Units.val_mul]
  show Matrix.det (Matrix.scalar (Fin 2) (z : AdeleRing (𝓞 L) L)) = z * z
  rw [Matrix.scalar_apply, Matrix.det_diagonal, Fin.prod_univ_two]

theorem ideleNorm_one : NumberField.TateGlobal.ideleNorm L 1 = 1 := by
  have h := NumberField.TateGlobal.ideleNorm_mul (1 : (AdeleRing (𝓞 L) L)ˣ) 1
  rw [one_mul] at h
  have hp := NumberField.TateGlobal.ideleNorm_pos (1 : (AdeleRing (𝓞 L) L)ˣ)
  nlinarith [h]

theorem ideleNorm_inv (x : (AdeleRing (𝓞 L) L)ˣ) :
    NumberField.TateGlobal.ideleNorm L x⁻¹ = (NumberField.TateGlobal.ideleNorm L x)⁻¹ :=
  eq_inv_of_mul_eq_one_left (by rw [← NumberField.TateGlobal.ideleNorm_mul, inv_mul_cancel, ideleNorm_one])

theorem preimage_slab_eq {α β : ℝ} (z : (AdeleRing (𝓞 L) L)ˣ) (y : AdelicGL2 (𝓞 L) L)
    (hz : NumberField.TateGlobal.ideleNorm L z * NumberField.TateGlobal.ideleNorm L z =
      NumberField.TateGlobal.ideleNorm L (Matrix.GeneralLinearGroup.det y)) :
    (fun g => (centralScalar (𝓞 L) L z)⁻¹ * g) ⁻¹' slab L α β = (fun g => g * y⁻¹) ⁻¹' slab L α β := by
  ext g
  simp only [Set.mem_preimage, slab, Set.mem_setOf_eq, map_mul, map_inv, NumberField.TateGlobal.ideleNorm_mul,
    ideleNorm_inv, det_centralScalar, hz]
  rw [mul_comm]

theorem isFundamentalDomain_mulRight {α β : ℝ} {Φ : Set (AdelicGL2 (𝓞 L) L)}
    (hΦ : IsFundamentalDomain (globalPoints (𝓞 L) L).range Φ ((adelicGLHaar (Fin 2) (𝓞 L) L).restrict (slab L α β)))
    (y : AdelicGL2 (𝓞 L) L) :
    IsFundamentalDomain (globalPoints (𝓞 L) L).range ((fun g => g * y⁻¹) ⁻¹' Φ)
      ((adelicGLHaar (Fin 2) (𝓞 L) L).restrict ((fun g => g * y⁻¹) ⁻¹' slab L α β)) := by
  set μ := adelicGLHaar (Fin 2) (𝓞 L) L with hμ
  have hmp : MeasurePreserving (fun g : AdelicGL2 (𝓞 L) L => g * y⁻¹)
      (μ.restrict ((fun g => g * y⁻¹) ⁻¹' slab L α β)) (μ.restrict (slab L α β)) :=
    (measurePreserving_mul_right μ y⁻¹).restrict_preimage (measurableSet_slab L α β)
  have himg : ((MeasurableEquiv.mulRight y).toEquiv : AdelicGL2 (𝓞 L) L → AdelicGL2 (𝓞 L) L) '' Φ =
      (fun g => g * y⁻¹) ⁻¹' Φ := by
    ext g
    simp only [Set.mem_image, Set.mem_preimage, MeasurableEquiv.coe_toEquiv, MeasurableEquiv.coe_mulRight]
    constructor
    · rintro ⟨x, hx, rfl⟩; rwa [mul_inv_cancel_right]
    · intro h; exact ⟨g * y⁻¹, h, by rw [inv_mul_cancel_right]⟩
  rw [← himg]
  refine hΦ.image_of_equiv (MeasurableEquiv.mulRight y).toEquiv ?_ (Equiv.refl _) fun γ x => ?_
  · have hsymm : ((MeasurableEquiv.mulRight y).toEquiv.symm : AdelicGL2 (𝓞 L) L → AdelicGL2 (𝓞 L) L) =
        fun g => g * y⁻¹ := by
      funext g
      rw [Equiv.symm_apply_eq]
      simp
    rw [hsymm]
    exact hmp.quasiMeasurePreserving
  · show ((γ : AdelicGL2 (𝓞 L) L) * x) * y = (γ : AdelicGL2 (𝓞 L) L) * (x * y)
    rw [mul_assoc]

theorem isFundamentalDomain_mulLeft_central {α β : ℝ} {Φ : Set (AdelicGL2 (𝓞 L) L)}
    (hΦ : IsFundamentalDomain (globalPoints (𝓞 L) L).range Φ ((adelicGLHaar (Fin 2) (𝓞 L) L).restrict (slab L α β)))
    (z : (AdeleRing (𝓞 L) L)ˣ) :
    IsFundamentalDomain (globalPoints (𝓞 L) L).range ((fun g => (centralScalar (𝓞 L) L z)⁻¹ * g) ⁻¹' Φ)
      ((adelicGLHaar (Fin 2) (𝓞 L) L).restrict ((fun g => (centralScalar (𝓞 L) L z)⁻¹ * g) ⁻¹' slab L α β)) := by
  set μ := adelicGLHaar (Fin 2) (𝓞 L) L with hμ
  set c := centralScalar (𝓞 L) L z with hc
  have hmp : MeasurePreserving (fun g : AdelicGL2 (𝓞 L) L => c⁻¹ * g)
      (μ.restrict ((fun g => c⁻¹ * g) ⁻¹' slab L α β)) (μ.restrict (slab L α β)) :=
    (measurePreserving_mul_left μ c⁻¹).restrict_preimage (measurableSet_slab L α β)
  have himg : ((MeasurableEquiv.mulLeft c).toEquiv : AdelicGL2 (𝓞 L) L → AdelicGL2 (𝓞 L) L) '' Φ =
      (fun g => c⁻¹ * g) ⁻¹' Φ := by
    ext g
    simp only [Set.mem_image, Set.mem_preimage, MeasurableEquiv.coe_toEquiv, MeasurableEquiv.coe_mulLeft]
    constructor
    · rintro ⟨x, hx, rfl⟩; rwa [inv_mul_cancel_left]
    · intro h; exact ⟨c⁻¹ * g, h, by rw [mul_inv_cancel_left]⟩
  rw [← himg]
  refine hΦ.image_of_equiv (MeasurableEquiv.mulLeft c).toEquiv ?_ (Equiv.refl _) fun γ x => ?_
  · have hsymm : ((MeasurableEquiv.mulLeft c).toEquiv.symm : AdelicGL2 (𝓞 L) L → AdelicGL2 (𝓞 L) L) =
        fun g => c⁻¹ * g := by
      funext g
      rw [Equiv.symm_apply_eq]
      simp
    rw [hsymm]
    exact hmp.quasiMeasurePreserving
  · show c * ((γ : AdelicGL2 (𝓞 L) L) * x) = (γ : AdelicGL2 (𝓞 L) L) * (c * x)
    rw [← mul_assoc, hc, centralScalar_comm, mul_assoc]

theorem globalPoints_mul_mem_slab_iff {α β : ℝ} (γ : GL (Fin 2) L) (x : AdelicGL2 (𝓞 L) L) :
    globalPoints (𝓞 L) L γ * x ∈ slab L α β ↔ x ∈ slab L α β := by
  simp only [slab, Set.mem_setOf_eq, map_mul, NumberField.TateGlobal.ideleNorm_mul,
    AutomorphicForm.ideleNorm_det_globalPoints, one_mul]

theorem smulInvariantMeasure_restrict {T : Set (AdelicGL2 (𝓞 L) L)}
    (hinv : ∀ (γ : GL (Fin 2) L) (x : AdelicGL2 (𝓞 L) L), globalPoints (𝓞 L) L γ * x ∈ T ↔ x ∈ T) :
    SMulInvariantMeasure (globalPoints (𝓞 L) L).range (AdelicGL2 (𝓞 L) L)
      ((adelicGLHaar (Fin 2) (𝓞 L) L).restrict T) := by
  refine ⟨fun γ s hs => ?_⟩
  obtain ⟨g, γ₀, rfl⟩ := γ
  have hpre : (fun x : AdelicGL2 (𝓞 L) L =>
      (⟨globalPoints (𝓞 L) L γ₀, γ₀, rfl⟩ : (globalPoints (𝓞 L) L).range) • x) ⁻¹' s =
      (fun x => globalPoints (𝓞 L) L γ₀ * x) ⁻¹' s := rfl
  rw [hpre, Measure.restrict_apply ((measurable_const_mul _) hs), Measure.restrict_apply hs]
  have hset : (fun x => globalPoints (𝓞 L) L γ₀ * x) ⁻¹' s ∩ T =
      (fun x => globalPoints (𝓞 L) L γ₀ * x) ⁻¹' (s ∩ T) := by
    ext x
    simp only [Set.mem_inter_iff, Set.mem_preimage, hinv]
  rw [hset, measure_preimage_mul]

theorem lintegral_translate_eq {α β : ℝ} {Φ : Set (AdelicGL2 (𝓞 L) L)} (hΦs : Φ ⊆ slab L α β)
    (hΦ : IsFundamentalDomain (globalPoints (𝓞 L) L).range Φ ((adelicGLHaar (Fin 2) (𝓞 L) L).restrict (slab L α β)))
    (u : AdelicGL2 (𝓞 L) L → ℂ) (hul : ∀ (γ : GL (Fin 2) L) (x), u (globalPoints (𝓞 L) L γ * x) = u x)
    (ξ' : (AdeleRing (𝓞 L) L)ˣ → ℂ) (hcen : ∀ z x, u (centralScalar (𝓞 L) L z * x) = ξ' z * u x)
    (z : (AdeleRing (𝓞 L) L)ˣ) (y : AdelicGL2 (𝓞 L) L)
    (hz : NumberField.TateGlobal.ideleNorm L z * NumberField.TateGlobal.ideleNorm L z =
      NumberField.TateGlobal.ideleNorm L (Matrix.GeneralLinearGroup.det y)) :
    ∫⁻ g in Φ, ‖u (g * y)‖ₑ ^ (2 : ℝ) ∂adelicGLHaar (Fin 2) (𝓞 L) L =
      ‖ξ' z‖ₑ ^ (2 : ℝ) * ∫⁻ g in Φ, ‖u g‖ₑ ^ (2 : ℝ) ∂adelicGLHaar (Fin 2) (𝓞 L) L := by
  set μ := adelicGLHaar (Fin 2) (𝓞 L) L with hμ
  set c := centralScalar (𝓞 L) L z with hc
  set f : AdelicGL2 (𝓞 L) L → ℝ≥0∞ := fun g => ‖u g‖ₑ ^ (2 : ℝ) with hf
  have hfinv : ∀ (γ : (globalPoints (𝓞 L) L).range) (x : AdelicGL2 (𝓞 L) L), f (γ • x) = f x := by
    rintro ⟨_, γ₀, rfl⟩ x
    show ‖u (globalPoints (𝓞 L) L γ₀ * x)‖ₑ ^ (2 : ℝ) = ‖u x‖ₑ ^ (2 : ℝ)
    rw [hul]
  set S := slab L α β with hS
  set Sy := (fun g => g * y⁻¹) ⁻¹' S with hSy
  set Φy := (fun g => g * y⁻¹) ⁻¹' Φ with hΦy
  set zΦ := (fun g => c⁻¹ * g) ⁻¹' Φ with hzΦ
  haveI : SMulInvariantMeasure (globalPoints (𝓞 L) L).range (AdelicGL2 (𝓞 L) L) (μ.restrict Sy) :=
    smulInvariantMeasure_restrict L fun γ x => by
      simp only [hSy, Set.mem_preimage, mul_assoc]
      exact globalPoints_mul_mem_slab_iff L γ _
  have h1 : IsFundamentalDomain (globalPoints (𝓞 L) L).range Φy (μ.restrict Sy) := isFundamentalDomain_mulRight L hΦ y
  have h2 : IsFundamentalDomain (globalPoints (𝓞 L) L).range zΦ (μ.restrict Sy) := by
    have := isFundamentalDomain_mulLeft_central L hΦ z
    rwa [preimage_slab_eq L z y hz] at this
  have key := h1.setLIntegral_eq h2 f hfinv
  have hsub1 : Φy ⊆ Sy := fun g hg => hΦs hg
  have hsub2 : zΦ ⊆ Sy := by
    rw [hSy, ← preimage_slab_eq L z y hz]
    exact fun g hg => hΦs hg
  rw [Measure.restrict_restrict_of_subset hsub1, Measure.restrict_restrict_of_subset hsub2] at key

  have hpreR : (fun x => x * y) ⁻¹' Φy = Φ := by
    ext g; simp [hΦy]
  have eR : μ.restrict Φy = (μ.restrict Φ).map (fun x => x * y) := by
    have h := (MeasurableEquiv.mulRight y).restrict_map μ Φy
    rw [MeasurableEquiv.coe_mulRight, map_mul_right_eq_self, hpreR] at h
    exact h
  have hpreL : (fun x => c * x) ⁻¹' zΦ = Φ := by
    ext g; simp [hzΦ]
  have eL : μ.restrict zΦ = (μ.restrict Φ).map (fun x => c * x) := by
    have h := (MeasurableEquiv.mulLeft c).restrict_map μ zΦ
    rw [MeasurableEquiv.coe_mulLeft, map_mul_left_eq_self, hpreL] at h
    exact h
  have lhs : ∫⁻ g in Φy, f g ∂μ = ∫⁻ g in Φ, f (g * y) ∂μ := by
    rw [eR, ← MeasurableEquiv.coe_mulRight y, lintegral_map_equiv]
    rfl
  have rhs : ∫⁻ g in zΦ, f g ∂μ = ‖ξ' z‖ₑ ^ (2 : ℝ) * ∫⁻ g in Φ, f g ∂μ := by
    rw [eL, ← MeasurableEquiv.coe_mulLeft c, lintegral_map_equiv]
    have hpt : ∀ g, f ((MeasurableEquiv.mulLeft c) g) = ‖ξ' z‖ₑ ^ (2 : ℝ) * f g := fun g => by
      rw [MeasurableEquiv.coe_mulLeft]
      show ‖u (c * g)‖ₑ ^ (2 : ℝ) = ‖ξ' z‖ₑ ^ (2 : ℝ) * ‖u g‖ₑ ^ (2 : ℝ)
      rw [hc, hcen, enorm_mul, ENNReal.mul_rpow_of_nonneg _ _ (by norm_num)]
    simp_rw [hpt]
    rw [lintegral_const_mul' _ _ (ENNReal.rpow_ne_top_of_nonneg (by norm_num) enorm_ne_top)]
  rw [← lhs, key, rhs]

end Slab

theorem continuous_centralScalar :
    Continuous (centralScalar (𝓞 L) L : (AdeleRing (𝓞 L) L)ˣ → AdelicGL2 (𝓞 L) L) := by
  have hsc : Continuous (Matrix.scalar (Fin 2) : AdeleRing (𝓞 L) L → Matrix (Fin 2) (Fin 2) _) := by
    refine continuous_matrix fun i j => ?_
    by_cases hij : i = j
    · subst hij; (simp [Matrix.scalar_apply]; exact continuous_id)
    · simpa [Matrix.scalar_apply, hij] using continuous_const
  exact Continuous.units_map _ hsc

theorem exists_bound_lintegral_translate {α β : ℝ} {Φ : Set (AdelicGL2 (𝓞 L) L)} (hΦs : Φ ⊆ slab L α β)
    (hΦ : IsFundamentalDomain (globalPoints (𝓞 L) L).range Φ ((adelicGLHaar (Fin 2) (𝓞 L) L).restrict (slab L α β)))
    (u : AdelicGL2 (𝓞 L) L → ℂ) (huc : Continuous u)
    (hul : ∀ (γ : GL (Fin 2) L) (x), u (globalPoints (𝓞 L) L γ * x) = u x)
    (ξ' : (AdeleRing (𝓞 L) L)ˣ → ℂ) (hcen : ∀ z x, u (centralScalar (𝓞 L) L z * x) = ξ' z * u x)
    (hu2 : ∫⁻ g in Φ, ‖u g‖ₑ ^ (2 : ℝ) ∂adelicGLHaar (Fin 2) (𝓞 L) L < ⊤)
    {C : Set (AdelicGL2 (𝓞 L) L)} (hC : IsCompact C) :
    ∃ M : ℝ≥0∞, M < ⊤ ∧ ∀ y ∈ C, ∫⁻ g in Φ, ‖u (g * y)‖ₑ ^ (2 : ℝ) ∂adelicGLHaar (Fin 2) (𝓞 L) L ≤ M := by

  obtain ⟨s, hsc, hsn, -⟩ := NumberField.TateGlobal.exists_continuous_monoidHom_ideleNorm_apply_eq L

  set t : AdelicGL2 (𝓞 L) L → ℝ := fun y => NumberField.TateGlobal.ideleNorm L (Matrix.GeneralLinearGroup.det y) with ht
  have htc : Continuous t := NumberField.TateGlobal.continuous_ideleNorm_det L
  have htp : ∀ y, 0 < t y := fun y => NumberField.TateGlobal.ideleNorm_pos _
  have hsq0 : ∀ y, NNReal.sqrt (Real.toNNReal (t y)) ≠ 0 := fun y h => by
    rw [NNReal.sqrt_eq_zero, Real.toNNReal_eq_zero] at h
    exact absurd h (not_le.2 (htp y))
  set r : AdelicGL2 (𝓞 L) L → ℝ≥0ˣ := fun y => Units.mk0 (NNReal.sqrt (Real.toNNReal (t y))) (hsq0 y) with hr
  have hrc : Continuous r := by
    have h0 : Continuous fun y => NNReal.sqrt (Real.toNNReal (t y)) :=
      NNReal.continuous_sqrt.comp (continuous_real_toNNReal.comp htc)
    refine Units.continuous_iff.2 ⟨h0, ?_⟩
    show Continuous fun y => ((r y)⁻¹ : ℝ≥0ˣ).1
    have : (fun y => ((r y)⁻¹ : ℝ≥0ˣ).1) = fun y => (NNReal.sqrt (Real.toNNReal (t y)))⁻¹ := by
      funext y; rfl
    rw [this]
    exact h0.inv₀ hsq0
  have hrval : ∀ y, (((r y : ℝ≥0ˣ) : ℝ≥0) : ℝ) = Real.sqrt (t y) := fun y => by
    show ((NNReal.sqrt (Real.toNNReal (t y)) : ℝ≥0) : ℝ) = Real.sqrt (t y)
    rw [Real.sqrt]
  have hz : ∀ y, NumberField.TateGlobal.ideleNorm L (s (r y)) * NumberField.TateGlobal.ideleNorm L (s (r y)) = t y := by
    intro y
    rw [hsn, hrval]
    exact Real.mul_self_sqrt (htp y).le
  have hkey : ∀ y, ∫⁻ g in Φ, ‖u (g * y)‖ₑ ^ (2 : ℝ) ∂adelicGLHaar (Fin 2) (𝓞 L) L =
      ‖ξ' (s (r y))‖ₑ ^ (2 : ℝ) * ∫⁻ g in Φ, ‖u g‖ₑ ^ (2 : ℝ) ∂adelicGLHaar (Fin 2) (𝓞 L) L :=
    fun y => lintegral_translate_eq L hΦs hΦ u hul ξ' hcen (s (r y)) y (hz y)
  by_cases hu0 : ∀ g, u g = 0
  · refine ⟨0, ENNReal.zero_lt_top, fun y _ => ?_⟩
    simp [hu0]
  · push Not at hu0
    obtain ⟨g₀, hg₀⟩ := hu0

    have hξ : ∀ y, ξ' (s (r y)) = u (centralScalar (𝓞 L) L (s (r y)) * g₀) / u g₀ := fun y => by
      rw [hcen, mul_div_assoc, div_self hg₀, mul_one]
    have hξc : Continuous fun y => ξ' (s (r y)) := by
      simp_rw [hξ]
      exact ((huc.comp ((((continuous_centralScalar L).comp (hsc.comp hrc))).mul continuous_const))).div_const _
    obtain ⟨B, hB⟩ := hC.exists_bound_of_continuousOn hξc.continuousOn
    refine ⟨(ENNReal.ofReal (max B 0)) ^ (2 : ℝ) * ∫⁻ g in Φ, ‖u g‖ₑ ^ (2 : ℝ) ∂adelicGLHaar (Fin 2) (𝓞 L) L,
      ENNReal.mul_lt_top (ENNReal.rpow_lt_top_of_nonneg (by norm_num) ENNReal.ofReal_ne_top) hu2, fun y hy => ?_⟩
    rw [hkey y]
    gcongr

    rw [← ofReal_norm]
    exact ENNReal.ofReal_le_ofReal ((hB y hy).trans (le_max_left _ _))

theorem indicator_rpow_two {X : Type*} (C : Set X) (h : X → ℝ≥0∞) (x : X) :
    (C.indicator h x) ^ (2 : ℝ) = C.indicator (fun x => h x ^ (2 : ℝ)) x := by
  by_cases hx : x ∈ C
  · simp [hx]
  · simp [hx]

theorem enorm_rightConv_sq_le (v φ : AdelicGL2 (𝓞 L) L → ℂ) (hv : Continuous v) (hφ : Continuous φ)
    (g : AdelicGL2 (𝓞 L) L) :
    ‖rightConv L v φ g‖ₑ ^ (2 : ℝ) ≤
      (∫⁻ x in tsupport φ, ‖v (g * x)‖ₑ ^ (2 : ℝ) ∂adelicGLHaar (Fin 2) (𝓞 L) L) *
        ∫⁻ x, ‖φ x‖ₑ ^ (2 : ℝ) ∂adelicGLHaar (Fin 2) (𝓞 L) L := by
  set μ := adelicGLHaar (Fin 2) (𝓞 L) L with hμ
  set C := tsupport φ with hC
  have hCm : MeasurableSet C := (isClosed_tsupport φ).measurableSet
  set F : AdelicGL2 (𝓞 L) L → ℝ≥0∞ := C.indicator fun x => ‖v (g * x)‖ₑ with hF
  set G : AdelicGL2 (𝓞 L) L → ℝ≥0∞ := fun x => ‖φ x‖ₑ with hG
  have hFm : AEMeasurable F μ :=
    ((hv.comp (continuous_const.mul continuous_id)).enorm.measurable.indicator hCm).aemeasurable
  have hGm : AEMeasurable G μ := hφ.enorm.measurable.aemeasurable

  have h1 : ‖rightConv L v φ g‖ₑ ≤ ∫⁻ x, (F * G) x ∂μ := by
    rw [rightConv_apply]
    refine (enorm_integral_le_lintegral_enorm _).trans (le_of_eq ?_)
    congr 1
    funext x
    rw [Pi.mul_apply, enorm_mul, hF, hG]
    by_cases hx : x ∈ C
    · rw [Set.indicator_of_mem hx]
    · rw [Set.indicator_of_notMem hx, image_eq_zero_of_notMem_tsupport hx, enorm_zero, mul_zero, zero_mul]

  have h2 := ENNReal.lintegral_mul_le_Lp_mul_Lq μ Real.HolderConjugate.two_two hFm hGm
  have h3 : ‖rightConv L v φ g‖ₑ ^ (2 : ℝ) ≤
      ((∫⁻ x, F x ^ (2 : ℝ) ∂μ) ^ (1 / (2 : ℝ)) * (∫⁻ x, G x ^ (2 : ℝ) ∂μ) ^ (1 / (2 : ℝ))) ^ (2 : ℝ) :=
    ENNReal.rpow_le_rpow (h1.trans h2) (by norm_num)
  refine h3.trans (le_of_eq ?_)
  rw [ENNReal.mul_rpow_of_nonneg _ _ (by norm_num), ← ENNReal.rpow_mul, ← ENNReal.rpow_mul,
    show (1 / (2 : ℝ)) * 2 = 1 by norm_num, ENNReal.rpow_one, ENNReal.rpow_one]
  congr 1
  simp_rw [hF, indicator_rpow_two]
  rw [lintegral_indicator hCm]

theorem lintegral_sq_rightConv_lt_top {α β : ℝ} {Φ : Set (AdelicGL2 (𝓞 L) L)} (hΦs : Φ ⊆ slab L α β)
    (hΦ : IsFundamentalDomain (globalPoints (𝓞 L) L).range Φ ((adelicGLHaar (Fin 2) (𝓞 L) L).restrict (slab L α β)))
    (u : AdelicGL2 (𝓞 L) L → ℂ) (huc : Continuous u)
    (hul : ∀ (γ : GL (Fin 2) L) (x), u (globalPoints (𝓞 L) L γ * x) = u x)
    (ξ' : (AdeleRing (𝓞 L) L)ˣ → ℂ) (hcen : ∀ z x, u (centralScalar (𝓞 L) L z * x) = ξ' z * u x)
    (hu2 : ∫⁻ g in Φ, ‖u g‖ₑ ^ (2 : ℝ) ∂adelicGLHaar (Fin 2) (𝓞 L) L < ⊤)
    (φ : AdelicGL2 (𝓞 L) L → ℂ) (hφ : Continuous φ) (hφc : HasCompactSupport φ) :
    ∫⁻ g in Φ, ‖rightConv L u φ g‖ₑ ^ (2 : ℝ) ∂adelicGLHaar (Fin 2) (𝓞 L) L < ⊤ := by
  set μ := adelicGLHaar (Fin 2) (𝓞 L) L with hμ
  set C := tsupport φ with hC
  have hCc : IsCompact C := hφc
  have hCm : MeasurableSet C := (isClosed_tsupport φ).measurableSet
  obtain ⟨M, hMtop, hM⟩ := exists_bound_lintegral_translate L hΦs hΦ u huc hul ξ' hcen hu2 hCc
  set B := ∫⁻ x, ‖φ x‖ₑ ^ (2 : ℝ) ∂μ with hB
  have hBtop : B < ⊤ := by
    have h := (hφ.memLp_of_hasCompactSupport (μ := μ) (p := 2) hφc).eLpNorm_lt_top
    rw [eLpNorm_lt_top_iff_lintegral_rpow_enorm_lt_top two_ne_zero ENNReal.ofNat_ne_top] at h
    simp only [ENNReal.toReal_ofNat] at h
    exact h

  have hmeas : AEMeasurable (Function.uncurry fun (g x : AdelicGL2 (𝓞 L) L) => ‖u (g * x)‖ₑ ^ (2 : ℝ))
      ((μ.restrict Φ).prod (μ.restrict C)) :=
    ((huc.comp continuous_mul).enorm.measurable.pow_const _).aemeasurable
  have hswap := lintegral_lintegral_swap (μ := μ.restrict Φ) (ν := μ.restrict C) hmeas
  calc ∫⁻ g in Φ, ‖rightConv L u φ g‖ₑ ^ (2 : ℝ) ∂μ
      ≤ ∫⁻ g in Φ, (∫⁻ x in C, ‖u (g * x)‖ₑ ^ (2 : ℝ) ∂μ) * B ∂μ :=
        lintegral_mono fun g => enorm_rightConv_sq_le L u φ huc hφ g
    _ = (∫⁻ g in Φ, ∫⁻ x in C, ‖u (g * x)‖ₑ ^ (2 : ℝ) ∂μ ∂μ) * B := lintegral_mul_const' _ _ hBtop.ne
    _ = (∫⁻ x in C, ∫⁻ g in Φ, ‖u (g * x)‖ₑ ^ (2 : ℝ) ∂μ ∂μ) * B := by rw [hswap]
    _ ≤ (∫⁻ x in C, M ∂μ) * B := by
        refine mul_le_mul' (lintegral_mono_ae ?_) le_rfl
        filter_upwards [ae_restrict_mem hCm] with x hx
        exact hM x hx
    _ < ⊤ := by
        rw [lintegral_const, Measure.restrict_apply MeasurableSet.univ, Set.univ_inter]
        exact ENNReal.mul_lt_top (ENNReal.mul_lt_top hMtop hCc.measure_lt_top) hBtop

theorem mainA
    (α β : ℝ) (ΦL : Set (AdelicGL2 (𝓞 L) L))
    (hΦs : ΦL ⊆ {g | NumberField.TateGlobal.ideleNorm L (Matrix.GeneralLinearGroup.det g) ∈ Set.Icc α β})
    (hΦ : IsFundamentalDomain (globalPoints (𝓞 L) L).range ΦL
      ((adelicGLHaar (Fin 2) (𝓞 L) L).restrict
        {g | NumberField.TateGlobal.ideleNorm L (Matrix.GeneralLinearGroup.det g) ∈ Set.Icc α β}))
    (ξL : (⊤ : Subgroup (AdeleRing (𝓞 L) L)ˣ) →* ℂˣ)
    (N : Ideal (𝓞 L)) (hN : N ≠ ⊥)
    (φ : AdelicGL2 (𝓞 L) L → ℂ) (hφ : Continuous φ) (hφc : HasCompactSupport φ)
    (hφN : ∀ u ∈ levelOne (𝓞 L) L N ⊓ finiteAdelicGL2Subgroup L, ∀ g : AdelicGL2 (𝓞 L) L, φ (u * g) = φ g)
    (v : AdelicGL2 (𝓞 L) L → ℂ) (hvc : Continuous v)
    (hv : IsCuspAutomorphicFnAt L
      (productionPinsOf L ΦL (fun M => levelOne (𝓞 L) L M ⊓ finiteAdelicGL2Subgroup L)
        (fun w => heckeGen (𝓞 L) L w) (adelicBox L)) ξL v) :
    IsSmoothCuspAutomorphicFnAt L
        (productionPinsOf L ΦL (fun M => levelOne (𝓞 L) L M ⊓ finiteAdelicGL2Subgroup L)
          (fun w => heckeGen (𝓞 L) L w) (adelicBox L)) ξL (rightConv L v φ) ∧
      Continuous (rightConv L v φ) ∧
      ∀ g : AdelicGL2 (𝓞 L) L, ∀ u ∈ levelOne (𝓞 L) L N ⊓ finiteAdelicGL2Subgroup L,
        rightConv L v φ (g * u) = rightConv L v φ g := by
  set μ := adelicGLHaar (Fin 2) (𝓞 L) L with hμ
  obtain ⟨hauto, hcuspv⟩ := hv
  have h1 : LsXiMemberAt (𝓞 L) L μ ⊤ ξL ΦL v := hauto
  obtain ⟨hlsxi, hmem⟩ := (lsXiMemberAt_iff (𝓞 L) L _ ⊤ ξL ΦL v).1 h1
  have hul : ∀ (γ : GL (Fin 2) L) (x : AdelicGL2 (𝓞 L) L), v (globalPoints (𝓞 L) L γ * x) = v x :=
    hlsxi.left_invariant
  set ξ' : (AdeleRing (𝓞 L) L)ˣ → ℂ := fun z => ((ξL ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ) with hξ'
  have hcen : ∀ (z : (AdeleRing (𝓞 L) L)ˣ) (x : AdelicGL2 (𝓞 L) L), v (centralScalar (𝓞 L) L z * x) = ξ' z * v x :=
    fun z x => hlsxi.central_transform ⟨z, Subgroup.mem_top z⟩ x

  have hwc : Continuous (rightConv L v φ) := continuous_rightConv L v φ hvc hφ hφc
  have hinv : ∀ g : AdelicGL2 (𝓞 L) L, ∀ u ∈ levelOne (𝓞 L) L N ⊓ finiteAdelicGL2Subgroup L,
      rightConv L v φ (g * u) = rightConv L v φ g :=
    fun g u hu => rightConv_apply_mul_of_left_invariant L v φ (hφN u hu) g
  have hKf : IsKfSmooth L (rightConv L v φ) := isKfSmooth_of_invariant L hN _ hinv

  have hlsxi' : IsLsXiFunction (𝓞 L) L ⊤ ξL (rightConv L v φ) := isLsXi_rightConv L v φ hlsxi

  have hv2 : ∫⁻ g in ΦL, ‖v g‖ₑ ^ (2 : ℝ) ∂μ < ⊤ := by
    have h := hmem.eLpNorm_lt_top
    rw [eLpNorm_lt_top_iff_lintegral_rpow_enorm_lt_top two_ne_zero ENNReal.ofNat_ne_top] at h
    simpa using h
  have hmem' : MemLp (rightConv L v φ) 2 (μ.restrict ΦL) := by
    refine ⟨hwc.aestronglyMeasurable, ?_⟩
    rw [eLpNorm_lt_top_iff_lintegral_rpow_enorm_lt_top two_ne_zero ENNReal.ofNat_ne_top]
    simpa using lintegral_sq_rightConv_lt_top L hΦs hΦ v hvc hul ξ' hcen hv2 φ hφ hφc

  have hcusp' : IsCuspidalFn (ProbabilityTheory.cond (adelicAddHaar (𝓞 L) L) (adelicBox L)) unipotentGL2
      (rightConv L v φ) := isCuspidalFn_rightConv L v φ hvc hφ hφc hcuspv
  exact ⟨⟨⟨(lsXiMemberAt_iff (𝓞 L) L _ ⊤ ξL ΦL _).2 ⟨hlsxi', hmem'⟩, hcusp'⟩, hKf⟩, hwc, hinv⟩

end P2mConvCusp
p2m_reactivate "P2MW.S_AutomorphicForm_isSmoothCuspAutomorphicFnAt_rightConv_of_isFundamentalDomain_slab.P2mConvCusp"

end
p2m_reactivate "P2MW.S_AutomorphicForm_isSmoothCuspAutomorphicFnAt_rightConv_of_isFundamentalDomain_slab.P2mConvCusp"

open MeasureTheory NumberField NumberField.AdelicHaar NumberField.AdelicLevel NumberField.AdelicBox
open IsDedekindDomain AutomorphicForm

attribute [local instance] NumberField.AdelicHaar.glBorel

theorem solution
    (L : Type) [Field L] [NumberField L]
    (α β : ℝ) (ΦL : Set (AdelicGL2 (𝓞 L) L))
    (hΦs : ΦL ⊆ {g | NumberField.TateGlobal.ideleNorm L (Matrix.GeneralLinearGroup.det g) ∈ Set.Icc α β})
    (hΦ : IsFundamentalDomain (globalPoints (𝓞 L) L).range ΦL
      ((adelicGLHaar (Fin 2) (𝓞 L) L).restrict
        {g | NumberField.TateGlobal.ideleNorm L (Matrix.GeneralLinearGroup.det g) ∈ Set.Icc α β}))
    (ξL : (⊤ : Subgroup (AdeleRing (𝓞 L) L)ˣ) →* ℂˣ)
    (N : Ideal (𝓞 L)) (hN : N ≠ ⊥)
    (φ : AdelicGL2 (𝓞 L) L → ℂ) (hφ : Continuous φ) (hφc : HasCompactSupport φ)
    (hφN : ∀ u ∈ levelOne (𝓞 L) L N ⊓ finiteAdelicGL2Subgroup L, ∀ g : AdelicGL2 (𝓞 L) L, φ (u * g) = φ g)
    (v : AdelicGL2 (𝓞 L) L → ℂ) (hvc : Continuous v)
    (hv : IsCuspAutomorphicFnAt L
      (productionPinsOf L ΦL (fun M => levelOne (𝓞 L) L M ⊓ finiteAdelicGL2Subgroup L)
        (fun w => heckeGen (𝓞 L) L w) (adelicBox L)) ξL v) :
    IsSmoothCuspAutomorphicFnAt L
        (productionPinsOf L ΦL (fun M => levelOne (𝓞 L) L M ⊓ finiteAdelicGL2Subgroup L)
          (fun w => heckeGen (𝓞 L) L w) (adelicBox L)) ξL (rightConv L v φ) ∧
      Continuous (rightConv L v φ) ∧
      ∀ g : AdelicGL2 (𝓞 L) L, ∀ u ∈ levelOne (𝓞 L) L N ⊓ finiteAdelicGL2Subgroup L,
        rightConv L v φ (g * u) = rightConv L v φ g :=
  P2mConvCusp.mainA L α β ΦL hΦs hΦ ξL N hN φ hφ hφc hφN v hvc hv

end S_AutomorphicForm_isSmoothCuspAutomorphicFnAt_rightConv_of_isFundamentalDomain_slab
end P2MW
export P2MW.S_AutomorphicForm_isSmoothCuspAutomorphicFnAt_rightConv_of_isFundamentalDomain_slab (solution)
