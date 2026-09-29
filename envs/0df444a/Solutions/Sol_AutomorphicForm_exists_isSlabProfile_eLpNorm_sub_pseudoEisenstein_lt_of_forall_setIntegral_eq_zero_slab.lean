-- Prove2me | solution 1 for AutomorphicForm.exists_isSlabProfile_eLpNorm_sub_pseudoEisenstein_lt_of_forall_setIntegral_eq_zero_slab
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.961684+00:00
-- url     : https://prove2.me/submissions/cff876e0-ec76-5492-a9e2-25e40b2878bd

import Definitions.Def_AutomorphicForm_AutomorphicFnAt
import Definitions.Def_AutomorphicForm_SlabProfile
import Definitions.Def_NumberField_AdelicBox
import Definitions.Def_NumberField_TateGlobalZeta
import Theorems.Thm_AutomorphicForm_finite_support_pseudoEisenstein_summand
import Theorems.Thm_AutomorphicForm_isAutomorphicFnAt_pseudoEisenstein_slab
import Theorems.Thm_AutomorphicForm_aestronglyMeasurable_adelicGLHaar_of_isAutomorphicFnAt_slab
import Theorems.Thm_AutomorphicForm_setIntegral_pseudoEisenstein_mul_conj_eq_setIntegral_rationalTorusUnipotentQuotient_slab
import Definitions.Def_AutomorphicForm_AdelicLsXi
import Definitions.Def_AutomorphicForm_AdelicMaximalCompact
import Definitions.Def_AutomorphicForm_BorelSubgroup
import Definitions.Def_AutomorphicForm_ConstantTerm
import Definitions.Def_AutomorphicForm_RationalTorusUnipotentQuotient
import Definitions.Def_AutomorphicForm_UnipotentQuotient
import Definitions.Def_AutomorphicForm_WeylIntertwining
import Definitions.Def_HaarQuotient
import Definitions.Def_M4aHerbrand_IdeleClassVocab
import Definitions.Def_NumberField_AdelicHaar
import Definitions.Def_NumberField_AdelicHeight
import Definitions.Def_NumberField_AdelicLevel
import Definitions.Def_NumberField_IdeleProductMeasure
import Mathlib.MeasureTheory.Group.FundamentalDomain
import Theorems.Thm_AutomorphicForm_constantTerm_adelicBox_globalPoints_mul_of_mem_borelSubgroup
import Theorems.Thm_AutomorphicForm_constantTerm_adelicBox_unipotentGL2_mul
import Theorems.Thm_AutomorphicForm_continuous_unipotentGL2
import Theorems.Thm_AutomorphicForm_exists_isFundamentalDomain_globalPoints_range
import Theorems.Thm_AutomorphicForm_exists_lintegral_rationalTorusUnipotentQuotientMeasure_eq_mul_setLIntegral_iwasawa
import Theorems.Thm_AutomorphicForm_ideleNorm_det_globalPoints
import Theorems.Thm_AutomorphicForm_isClosed_rationalTorusUnipotent
import Theorems.Thm_AutomorphicForm_isFundamentalDomain_boxSheet_rationalTorusUnipotent
import Theorems.Thm_AutomorphicForm_isHaarMeasure_rationalTorusUnipotentHaar_and_isMulRightInvariant
import Theorems.Thm_HaarQuotient_integrable_setIntegral_mul_out_and_setIntegral_eq_integral_setIntegral_mul_out
import Theorems.Thm_HaarQuotient_setLIntegral_eq_lintegral_setLIntegral_mul_out
import Theorems.Thm_MeasureTheory_IsFundamentalDomain_iUnion_inv_smul_of_leftCosetRepresentatives
import Theorems.Thm_NumberField_AdeleRing_distribHaarChar_algebraMap
import Theorems.Thm_NumberField_AdeleRing_secondCountableTopology
import Theorems.Thm_NumberField_AdeleRing_secondCountableTopology_generalLinearGroup_finTwo
import Theorems.Thm_NumberField_AdelicHaar_isMulRightInvariant_adelicGLHaar
import Theorems.Thm_NumberField_AdelicHeight_adelicHeight_diagOne_mul
import Theorems.Thm_NumberField_AdelicHeight_adelicHeight_globalPoints_mul_of_apply_one_zero_eq_zero
import Theorems.Thm_NumberField_AdelicHeight_continuous_adelicHeight
import Theorems.Thm_NumberField_AdelicHeight_exists_forall_mul_adelicHeight_le_adelicHeight_mul_of_isCompact
import Theorems.Thm_NumberField_Idele_idelicHaar_inter_setOf_ideleNorm_mem_Icc_pos_and_lt_top
import Theorems.Thm_NumberField_TateGlobal_continuous_ideleNorm
import Theorems.Thm_NumberField_TateGlobal_continuous_ideleNorm_det
import Theorems.Thm_NumberField_TateGlobal_exists_continuous_monoidHom_ideleNorm_apply_eq
import Theorems.Thm_NumberField_TateGlobal_exists_isCompact_subset_normOneIdeles_forall_mem_exists_eq_map_algebraMap_mul
import Theorems.Thm_NumberField_TateGlobal_exists_isFundamentalDomain_principalIdeles_forall_exists_integrableOn_min_ideleNorm_pow
import Theorems.Thm_NumberField_TateGlobal_measurableSet_setOf_ideleNorm_det_mem_Icc
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AutomorphicForm_exists_isSlabProfile_eLpNorm_sub_pseudoEisenstein_lt_of_forall_setIntegral_eq_zero_slab
p2m_attr_erase "instance" "instCountableOfNumberField_definitions instFiniteResidueFieldAdicCompletionRingOfIntegersWithZeroMultiplicativeInt_definitions NumberField.instCompactSpaceAdicCompletionIntegers Rat.adicCompletion.locallyCompactSpace NumberField.instFiniteResidueFieldAdicCompletionIntegers instWeaklyLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions RestrictedProduct.SecondCountableTopology_of_principal instCountableElemSetSetsCofinite_definitions"
p2m_attr_erase "simp" "AutomorphicForm.mem_inducedSectionSubmodule_iff AutomorphicForm.cpowChar_apply_val LanglandsTunnell.TateLocal.charExt_coe_units LanglandsTunnell.TateLocal.modulus_one LanglandsTunnell.TateLocal.modulus_zero LanglandsTunnell.TateLocal.modulus_coe_units LanglandsTunnell.TateLocal.charExt_zero ContinuousAddEquiv.restrictedProductPi_apply RestrictedProduct.flatten_homeomorph_apply RestrictedProduct.flatten_homeomorph'_symm_apply ContinuousMulEquiv.restrictedProductPi_symm_apply RestrictedProduct.flatten_homeomorph'_apply RestrictedProduct.flatten_homeomorph_symm_apply ContinuousMulEquiv.restrictedProductPi_apply ContinuousAddEquiv.restrictedProductPi_symm_apply RingEquiv.restrictedProductCongr_symm_apply RingEquiv.restrictedProductCongrRight_apply MulEquiv.restrictedProductCongrRight_apply Equiv.restrictedProductProd_symm_apply_coe Equiv.restrictedProductCongrRight_apply AddEquiv.restrictedProductCongr_apply Equiv.restrictedProductCongrLeft'_symm_apply_apply Equiv.restrictedProductCongr_apply_apply Equiv.restrictedProductCongrLeft_apply_apply RestrictedProduct.flatten_equiv'_apply AddEquiv.restrictedProductCongrRight_apply Equiv.restrictedProductCongr_symm_apply Equiv.restrictedProductCongrRight_symm_apply RestrictedProduct.flatten_equiv'_symm_apply AddEquiv.restrictedProductCongrLeft'_apply Equiv.restrictedProductCongrLeft'_apply RestrictedProduct.flatten_apply RingEquiv.restrictedProductCongr_apply_apply RingEquiv.restrictedProductCongrLeft'_apply Equiv.restrictedProductProd_apply RestrictedProduct.flatten_equiv_apply RestrictedProduct.flatten_equiv_symm_apply LinearEquiv.restrictedProductCongrLeft'_apply RestrictedProduct.not_mem_support RestrictedProduct.mem_structureSubring_iff"
p2m_attr_erase "simp" "RestrictedProduct.not_mem_mulSupport RestrictedProduct.support_neg RestrictedProduct.mem_indexSupport_iff RestrictedProduct.mulSupport_inv RestrictedProduct.mapAlongLinearMap_apply LocalGL2.coe_localRepSome LocalGL2.coe_diagPi LocalGL2.coe_localRepInf LocalGL2.coe_localRepSome_inv LocalGL2.coe_unipotentInt LocalGL2.coe_weylInt LocalGL2.coe_diagPi_inv LocalGL2.transposeGL_val LocalGL2.transposeGL_one LocalGL2.swapUnit_val"

set_option autoImplicit false

section

set_option autoImplicit false

open MeasureTheory NumberField
p2m_open "AutomorphicForm P2MW.S_AutomorphicForm_exists_isSlabProfile_eLpNorm_sub_pseudoEisenstein_lt_of_forall_setIntegral_eq_zero_slab.AutomorphicForm"
open NumberField.AdelicHaar NumberField.AdelicLevel NumberField.AdelicBox
open scoped Pointwise ENNReal

attribute [local instance] NumberField.AdelicHaar.glBorel NumberField.AdelicHaar.borelSpace_glBorel
  NumberField.AdelicHaar.adeleBorel NumberField.AdelicHaar.borelSpace_adeleBorel
attribute [local instance] NumberField.AdelicHaar.isHaarMeasure_adelicGLHaar
  NumberField.AdeleRing.secondCountableTopology_generalLinearGroup_finTwo

noncomputable section

namespace SlabPairingDescent

variable (F : Type) [Field F] [NumberField F]

variable {G : Type*} [Group G]

private theorem preimage_mk_image_of_invariant (H : Subgroup G) (Z : Set G)
    (hZinv : ∀ (h : H) (g : G), h • g ∈ Z ↔ g ∈ Z) :
    (Quotient.mk'' : G → MulAction.orbitRel.Quotient H G) ⁻¹' (Quotient.mk'' '' Z) = Z := by
  ext g
  constructor
  · rintro ⟨z, hz, hzg⟩
    have hrel : (MulAction.orbitRel H G) z g := Quotient.eq''.1 hzg
    obtain ⟨h, rfl⟩ := MulAction.orbitRel_apply.1 hrel
    exact (hZinv h g).1 hz
  · intro hg
    exact ⟨g, hg, rfl⟩

variable [TopologicalSpace G] [MeasurableSpace G]

private theorem ae_out_notMem_of_invariant_of_null (μ : Measure G) (H : Subgroup G) (μH : Measure H) (Z : Set G)
    (hZm : MeasurableSet Z) (hZ0 : μ Z = 0) (hZinv : ∀ (h : H) (g : G), h • g ∈ Z ↔ g ∈ Z) :
    ∀ᵐ q ∂(HaarQuotient.measure μ H μH), (q.out : G) ∉ Z := by
  have hpre := preimage_mk_image_of_invariant H Z hZinv
  have himg : MeasurableSet ((Quotient.mk'' : G → MulAction.orbitRel.Quotient H G) '' Z) := by
    rw [measurableSet_quotient]
    simpa only [hpre] using hZm
  have hnull : HaarQuotient.measure μ H μH ((Quotient.mk'' : G → MulAction.orbitRel.Quotient H G) '' Z) = 0 := by
    rw [HaarQuotient.measure, Measure.map_apply measurable_quotient_mk'' himg, hpre]
    exact withDensity_absolutelyContinuous μ _ hZ0
  have hae : ∀ᵐ q ∂(HaarQuotient.measure μ H μH),
      q ∉ (Quotient.mk'' : G → MulAction.orbitRel.Quotient H G) '' Z := measure_eq_zero_iff_ae_notMem.1 hnull
  filter_upwards [hae] with q hq hout
  exact hq ⟨q.out, hout, Quotient.out_eq' q⟩

private abbrev slab (d₁ d₂ : ℝ) : Set (AdelicGL2 (𝓞 F) F) :=
  {g | NumberField.TateGlobal.ideleNorm F (Matrix.GeneralLinearGroup.det g) ∈ Set.Icc d₁ d₂}

private theorem det_unipotentGL2_eq_one (q : AdeleRing (𝓞 F) F) :
    Matrix.GeneralLinearGroup.det (unipotentGL2 q) = 1 := by
  ext
  simp [unipotentGL2, Matrix.det_fin_two_of]

private def normDet : AdelicGL2 (𝓞 F) F →* ℝ where
  toFun g := NumberField.TateGlobal.ideleNorm F (Matrix.GeneralLinearGroup.det g)
  map_one' := by
    have h := NumberField.TateGlobal.ideleNorm_mul (F := F) 1 1
    rw [one_mul] at h
    have h' : NumberField.TateGlobal.ideleNorm F 1 * 1
        = NumberField.TateGlobal.ideleNorm F 1 * NumberField.TateGlobal.ideleNorm F 1 := by
      rw [mul_one]
      exact h
    rw [map_one]
    exact (mul_left_cancel₀ (NumberField.TateGlobal.ideleNorm_pos (F := F) 1).ne' h').symm
  map_mul' x y := by
    show NumberField.TateGlobal.ideleNorm F (Matrix.GeneralLinearGroup.det (x * y))
      = NumberField.TateGlobal.ideleNorm F (Matrix.GeneralLinearGroup.det x)
          * NumberField.TateGlobal.ideleNorm F (Matrix.GeneralLinearGroup.det y)
    rw [map_mul, NumberField.TateGlobal.ideleNorm_mul]

private theorem normDet_apply (g : AdelicGL2 (𝓞 F) F) :
    normDet F g = NumberField.TateGlobal.ideleNorm F (Matrix.GeneralLinearGroup.det g) :=
  rfl

private theorem normDet_eq_one_of_mem
    (hpf : ∀ x : Matrix.GeneralLinearGroup (Fin 2) F,
      NumberField.TateGlobal.ideleNorm F (Matrix.GeneralLinearGroup.det (globalPoints (𝓞 F) F x)) = 1)
    {p : AdelicGL2 (𝓞 F) F} (hp : p ∈ rationalTorusUnipotent F) : normDet F p = 1 := by
  have hle : rationalTorusUnipotent F ≤ (normDet F).ker := by
    refine sup_le (sup_le ?_ ?_) ?_
    · rintro _ ⟨a, rfl⟩
      exact MonoidHom.mem_ker.mpr (hpf _)
    · rintro _ ⟨a, rfl⟩
      exact MonoidHom.mem_ker.mpr (hpf _)
    · rintro _ ⟨x, rfl⟩
      refine MonoidHom.mem_ker.mpr ?_
      show NumberField.TateGlobal.ideleNorm F
        (Matrix.GeneralLinearGroup.det (unipotentGL2 (Multiplicative.toAdd x))) = 1
      rw [det_unipotentGL2_eq_one]
      have h1 := (normDet F).map_one
      rwa [normDet_apply, map_one] at h1
  exact MonoidHom.mem_ker.mp (hle hp)

private def normDetQuot
    (hpf : ∀ x : Matrix.GeneralLinearGroup (Fin 2) F,
      NumberField.TateGlobal.ideleNorm F (Matrix.GeneralLinearGroup.det (globalPoints (𝓞 F) F x)) = 1) :
    RationalTorusUnipotentQuotient F → ℝ :=
  Quotient.lift (normDet F) fun a b hab => by
    obtain ⟨p, rfl⟩ := hab
    show normDet F ((p : AdelicGL2 (𝓞 F) F) * b) = normDet F b
    rw [map_mul, normDet_eq_one_of_mem F hpf p.2, one_mul]

private theorem normDetQuot_mk
    (hpf : ∀ x : Matrix.GeneralLinearGroup (Fin 2) F,
      NumberField.TateGlobal.ideleNorm F (Matrix.GeneralLinearGroup.det (globalPoints (𝓞 F) F x)) = 1)
    (g : AdelicGL2 (𝓞 F) F) :
    normDetQuot F hpf (Quotient.mk'' g) = NumberField.TateGlobal.ideleNorm F (Matrix.GeneralLinearGroup.det g) :=
  rfl

private def slabQuot
    (hpf : ∀ x : Matrix.GeneralLinearGroup (Fin 2) F,
      NumberField.TateGlobal.ideleNorm F (Matrix.GeneralLinearGroup.det (globalPoints (𝓞 F) F x)) = 1)
    (d₁ d₂ : ℝ) : Set (RationalTorusUnipotentQuotient F) :=
  normDetQuot F hpf ⁻¹' Set.Icc d₁ d₂

private theorem preimage_mk_slabQuot
    (hpf : ∀ x : Matrix.GeneralLinearGroup (Fin 2) F,
      NumberField.TateGlobal.ideleNorm F (Matrix.GeneralLinearGroup.det (globalPoints (𝓞 F) F x)) = 1)
    (d₁ d₂ : ℝ) :
    (Quotient.mk'' : AdelicGL2 (𝓞 F) F → RationalTorusUnipotentQuotient F) ⁻¹' slabQuot F hpf d₁ d₂ = slab F d₁ d₂ :=
  rfl

private theorem measurableSet_slabQuot
    (hpf : ∀ x : Matrix.GeneralLinearGroup (Fin 2) F,
      NumberField.TateGlobal.ideleNorm F (Matrix.GeneralLinearGroup.det (globalPoints (𝓞 F) F x)) = 1)
    (d₁ d₂ : ℝ) (hslab : MeasurableSet (slab F d₁ d₂)) : MeasurableSet (slabQuot F hpf d₁ d₂) := by
  rw [measurableSet_quotient, preimage_mk_slabQuot]
  exact hslab

private theorem out_mem_slab_iff_mem_slabQuot
    (hpf : ∀ x : Matrix.GeneralLinearGroup (Fin 2) F,
      NumberField.TateGlobal.ideleNorm F (Matrix.GeneralLinearGroup.det (globalPoints (𝓞 F) F x)) = 1)
    (d₁ d₂ : ℝ) (q : RationalTorusUnipotentQuotient F) :
    q.out ∈ slab F d₁ d₂ ↔ q ∈ slabQuot F hpf d₁ d₂ := by
  rw [← preimage_mk_slabQuot F hpf d₁ d₂, Set.mem_preimage, Quotient.out_eq']

private theorem globalPoints_unipotentGL2 (β : F) :
    globalPoints (𝓞 F) F (unipotentGL2 β) = unipotentGL2 (algebraMap F (AdeleRing (𝓞 F) F) β) := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [globalPoints, unipotentGL2]

private theorem adelicWeyl_mem_range : adelicWeyl (𝓞 F) F ∈ (globalPoints (𝓞 F) F).range :=
  ⟨gl2Weyl, rfl⟩

private theorem adelicWeyl_mul_unipotentGL2_mem_range (β : F) :
    adelicWeyl (𝓞 F) F * unipotentGL2 (algebraMap F (AdeleRing (𝓞 F) F) β) ∈ (globalPoints (𝓞 F) F).range :=
  ⟨gl2Weyl * unipotentGL2 β, by rw [map_mul, globalPoints_unipotentGL2]; rfl⟩

private def bruhatSummand : Option F → (globalPoints (𝓞 F) F).range
  | none => 1
  | some β => ⟨_, adelicWeyl_mul_unipotentGL2_mem_range F β⟩

private def bruhatRep (i : Option F) : (globalPoints (𝓞 F) F).range :=
  (bruhatSummand F i)⁻¹

@[scoped simp]
private theorem bruhatRep_inv (i : Option F) : (bruhatRep F i)⁻¹ = bruhatSummand F i :=
  inv_inv _

private theorem bruhatRep_none_inv_smul (g : AdelicGL2 (𝓞 F) F) :
    ((bruhatRep F none : AdelicGL2 (𝓞 F) F)⁻¹) • g = g := by
  simp [bruhatRep, bruhatSummand]

private theorem bruhatRep_some_inv_smul (β : F) (g : AdelicGL2 (𝓞 F) F) :
    ((bruhatRep F (some β) : AdelicGL2 (𝓞 F) F)⁻¹) • g
      = adelicWeyl (𝓞 F) F * unipotentGL2 (algebraMap F (AdeleRing (𝓞 F) F) β) * g := by
  simp [bruhatRep, bruhatSummand, smul_eq_mul]

private theorem borel_map_le_range : (borelSubgroup F).map (globalPoints (𝓞 F) F) ≤ (globalPoints (𝓞 F) F).range :=
  Subgroup.map_le_range _ _

omit [NumberField F] in

private theorem summand_mul_entry (γ₀ : GL (Fin 2) F) :
    (((1 : GL (Fin 2) F) * γ₀ : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) 1 0 = (γ₀ : Matrix (Fin 2) (Fin 2) F) 1 0 ∧
    ∀ β : F, ((gl2Weyl * unipotentGL2 β * γ₀ : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) 1 0
      = (γ₀ : Matrix (Fin 2) (Fin 2) F) 0 0 + β * (γ₀ : Matrix (Fin 2) (Fin 2) F) 1 0 := by
  refine ⟨by simp, fun β => ?_⟩
  simp [Matrix.mul_apply, Fin.sum_univ_two]

private theorem bruhatSummand_eq_globalPoints :
    ((bruhatSummand F none : AdelicGL2 (𝓞 F) F) = globalPoints (𝓞 F) F 1) ∧
    ∀ β : F, (bruhatSummand F (some β) : AdelicGL2 (𝓞 F) F) = globalPoints (𝓞 F) F (gl2Weyl * unipotentGL2 β) := by
  refine ⟨by simp [bruhatSummand], fun β => ?_⟩
  simp only [bruhatSummand, map_mul, globalPoints_unipotentGL2]
  rfl

private theorem globalPoints_mem_borel_map_iff (x₀ : GL (Fin 2) F) :
    globalPoints (𝓞 F) F x₀ ∈ (borelSubgroup F).map (globalPoints (𝓞 F) F)
      ↔ (x₀ : Matrix (Fin 2) (Fin 2) F) 1 0 = 0 := by
  constructor
  · rintro ⟨b, hb, hbx⟩
    have hb' : (b : Matrix (Fin 2) (Fin 2) F) 1 0 = 0 := hb
    have hentry := congrArg (fun y : AdelicGL2 (𝓞 F) F => (y : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 F) F)) 1 0) hbx
    simp only [globalPoints_apply, hb', map_zero] at hentry
    exact NumberField.AdeleRing.algebraMap_injective (𝓞 F) F (by simpa using hentry.symm)
  · intro h
    exact ⟨x₀, h, rfl⟩

private theorem bruhatRep_spec (γ : (globalPoints (𝓞 F) F).range) :
    ∃! i : Option F, ((bruhatRep F i)⁻¹ * γ : AdelicGL2 (𝓞 F) F) ∈ (borelSubgroup F).map (globalPoints (𝓞 F) F) := by
  obtain ⟨γ₀, hγ₀⟩ := γ.2
  obtain ⟨h1, hw⟩ := summand_mul_entry F γ₀
  obtain ⟨s1, sw⟩ := bruhatSummand_eq_globalPoints F
  have key : ∀ i : Option F,
      (((bruhatRep F i)⁻¹ * γ : AdelicGL2 (𝓞 F) F) ∈ (borelSubgroup F).map (globalPoints (𝓞 F) F)) ↔
      (match i with
        | none => (γ₀ : Matrix (Fin 2) (Fin 2) F) 1 0 = 0
        | some β => (γ₀ : Matrix (Fin 2) (Fin 2) F) 0 0 + β * (γ₀ : Matrix (Fin 2) (Fin 2) F) 1 0 = 0) := by
    intro i
    rw [bruhatRep_inv, ← hγ₀]
    cases i with
    | none => rw [s1, ← map_mul, globalPoints_mem_borel_map_iff, h1]
    | some β => rw [sw β, ← map_mul, globalPoints_mem_borel_map_iff, hw β]
  have hdet : (γ₀ : Matrix (Fin 2) (Fin 2) F) 0 0 * (γ₀ : Matrix (Fin 2) (Fin 2) F) 1 1
      - (γ₀ : Matrix (Fin 2) (Fin 2) F) 0 1 * (γ₀ : Matrix (Fin 2) (Fin 2) F) 1 0 ≠ 0 := by
    have := (Matrix.isUnits_det_units γ₀).ne_zero
    rwa [Matrix.det_fin_two] at this
  by_cases hc : (γ₀ : Matrix (Fin 2) (Fin 2) F) 1 0 = 0
  ·
    have ha : (γ₀ : Matrix (Fin 2) (Fin 2) F) 0 0 ≠ 0 := by
      intro ha; apply hdet; rw [ha, hc]; ring
    refine ⟨none, (key none).2 hc, fun i hi => ?_⟩
    cases i with
    | none => rfl
    | some β =>
      exfalso
      have := (key (some β)).1 hi
      simp only [hc, mul_zero, add_zero] at this
      exact ha this
  ·
    refine ⟨some (-(γ₀ : Matrix (Fin 2) (Fin 2) F) 0 0 / (γ₀ : Matrix (Fin 2) (Fin 2) F) 1 0), ?_, fun i hi => ?_⟩
    · refine (key _).2 ?_
      simp only [div_mul_cancel₀ _ hc, add_neg_cancel]
    · cases i with
      | none => exact absurd ((key none).1 hi) hc
      | some β =>
        have hβ := (key (some β)).1 hi
        congr 1
        field_simp
        linear_combination hβ

private theorem isFundamentalDomain_iUnion_bruhatRep (μ : Measure (AdelicGL2 (𝓞 F) F))
    [SMulInvariantMeasure (AdelicGL2 (𝓞 F) F) (AdelicGL2 (𝓞 F) F) μ]
    [Countable F] [Countable (globalPoints (𝓞 F) F).range] (Φ : Set (AdelicGL2 (𝓞 F) F))
    (hΦ : IsFundamentalDomain (globalPoints (𝓞 F) F).range Φ μ) :
    IsFundamentalDomain ((borelSubgroup F).map (globalPoints (𝓞 F) F))
      (⋃ i : Option F, ((bruhatRep F i : AdelicGL2 (𝓞 F) F)⁻¹) • Φ) μ :=
  hΦ.iUnion_inv_smul_of_leftCosetRepresentatives μ _ _ (borel_map_le_range F) Φ (bruhatRep F) (bruhatRep_spec F)

private abbrev boxMap : AdeleRing (𝓞 F) F → rationalTorusUnipotent F :=
  fun u => Subgroup.inclusion le_sup_right (toAdelicUnipotent F u)

private abbrev boxSheet : Set (rationalTorusUnipotent F) := boxMap F '' adelicBox F

private abbrev boxHaar : Measure (AdeleRing (𝓞 F) F) :=
  ((adelicAddHaar (𝓞 F) F) (adelicBox F))⁻¹ • adelicAddHaar (𝓞 F) F

private theorem coe_boxMap (u : AdeleRing (𝓞 F) F) : ((boxMap F u : rationalTorusUnipotent F) : AdelicGL2 (𝓞 F) F)
    = unipotentGL2 u := rfl

private theorem restrict_boxSheet_eq_map (hι : Measurable (boxMap F)) :
    (rationalTorusUnipotentHaar F).restrict (boxSheet F)
      = Measure.map (boxMap F) ((boxHaar F).restrict (adelicBox F)) := by
  obtain ⟨-, -, -, -, hT⟩ := isFundamentalDomain_boxSheet_rationalTorusUnipotent F
  ext s hs
  have h := hT (s.indicator 1) (measurable_one.indicator hs)
  rw [Measure.map_apply hι hs, ← lintegral_indicator_one hs, ← lintegral_indicator_one (hι hs)]
  first
    | simpa [Set.indicator_comp_right, Function.comp_def] using h
    | (simpa [Set.indicator_comp_right, Function.comp_def] using (h :)) | (simpa [Function.comp_def] using h) | exact h | (have h__ := h; (try simp [Set.indicator_comp_right, Function.comp_def] at h__); (try simp [Set.indicator_comp_right, Function.comp_def]); exact h__)

private theorem setIntegral_boxSheet_eq (hι : Measurable (boxMap F))
    (k : rationalTorusUnipotent F → ℂ)
    (hk : AEStronglyMeasurable k ((rationalTorusUnipotentHaar F).restrict (boxSheet F))) :
    ∫ x in boxSheet F, k x ∂(rationalTorusUnipotentHaar F) = ∫ u in adelicBox F, k (boxMap F u) ∂(boxHaar F) := by
  rw [restrict_boxSheet_eq_map F hι] at hk ⊢
  exact integral_map hι.aemeasurable hk

private theorem det_unipotentGL2_mul_eq (u : AdeleRing (𝓞 F) F) (y : AdelicGL2 (𝓞 F) F) :
    Matrix.GeneralLinearGroup.det (unipotentGL2 u * y) = Matrix.GeneralLinearGroup.det y := by
  rw [map_mul, det_unipotentGL2_eq_one, one_mul]

private theorem setIntegral_boxSheet_integrand_eq (hι : Measurable (boxMap F))
    (d₁ d₂ : ℝ) (φ f : AdelicGL2 (𝓞 F) F → ℂ)
    (hφN : ∀ (u : AdeleRing (𝓞 F) F) (y : AdelicGL2 (𝓞 F) F), φ (unipotentGL2 u * y) = φ y)
    (y : AdelicGL2 (𝓞 F) F)
    (hk : AEStronglyMeasurable (fun x : rationalTorusUnipotent F => f ((x : AdelicGL2 (𝓞 F) F) * y))
      ((rationalTorusUnipotentHaar F).restrict (boxSheet F))) :
    ∫ x in boxSheet F, ({g : AdelicGL2 (𝓞 F) F |
        NumberField.TateGlobal.ideleNorm F (Matrix.GeneralLinearGroup.det g) ∈ Set.Icc d₁ d₂}.indicator
          (fun g => φ g * (starRingEnd ℂ) (f g))) ((x : AdelicGL2 (𝓞 F) F) * y) ∂(rationalTorusUnipotentHaar F)
      = Set.indicator
        {g : AdelicGL2 (𝓞 F) F | NumberField.TateGlobal.ideleNorm F (Matrix.GeneralLinearGroup.det g) ∈ Set.Icc d₁ d₂}
        (fun g => φ g * (starRingEnd ℂ) (∫ u in adelicBox F, f (unipotentGL2 u * g) ∂(boxHaar F))) y := by
  set S : Set (AdelicGL2 (𝓞 F) F) :=
    {g | NumberField.TateGlobal.ideleNorm F (Matrix.GeneralLinearGroup.det g) ∈ Set.Icc d₁ d₂} with hS
  have hmem : ∀ u : AdeleRing (𝓞 F) F, unipotentGL2 u * y ∈ S ↔ y ∈ S := fun u => by
    simp only [hS, Set.mem_setOf_eq, det_unipotentGL2_mul_eq]
  have hint : ∀ x : rationalTorusUnipotent F, x ∈ boxSheet F →
      S.indicator (fun g => φ g * (starRingEnd ℂ) (f g)) ((x : AdelicGL2 (𝓞 F) F) * y)
        = S.indicator (fun _ => φ y) y * (starRingEnd ℂ) (f ((x : AdelicGL2 (𝓞 F) F) * y)) := by
    rintro x ⟨u, -, rfl⟩
    rw [coe_boxMap]
    by_cases hy : y ∈ S
    · rw [Set.indicator_of_mem ((hmem u).2 hy), Set.indicator_of_mem hy, hφN]
    · rw [Set.indicator_of_notMem (fun h => hy ((hmem u).1 h)), Set.indicator_of_notMem hy, zero_mul]
  obtain ⟨-, -, hTm, -, -⟩ := isFundamentalDomain_boxSheet_rationalTorusUnipotent F
  rw [setIntegral_congr_fun hTm hint, integral_const_mul, integral_conj,
    setIntegral_boxSheet_eq F hι (fun x => f ((x : AdelicGL2 (𝓞 F) F) * y)) hk]
  simp only [coe_boxMap]
  by_cases hy : y ∈ S
  · rw [Set.indicator_of_mem hy, Set.indicator_of_mem hy]
  · rw [Set.indicator_of_notMem hy, Set.indicator_of_notMem hy, zero_mul]

private abbrev boxIntegral (f : AdelicGL2 (𝓞 F) F → ℂ) (g : AdelicGL2 (𝓞 F) F) : ℂ :=
  ∫ u in adelicBox F, f (unipotentGL2 u * g) ∂(boxHaar F)

private abbrev boxCond : Measure (AdeleRing (𝓞 F) F) := ProbabilityTheory.cond (adelicAddHaar (𝓞 F) F) (adelicBox F)

private theorem boxCond_eq : boxCond F = (boxHaar F).restrict (adelicBox F) := by
  rw [boxCond, ProbabilityTheory.cond, boxHaar, Measure.restrict_smul]

private theorem boxIntegral_eq_constantTerm (f : AdelicGL2 (𝓞 F) F → ℂ) (g : AdelicGL2 (𝓞 F) F) :
    boxIntegral F f g = constantTerm (boxCond F) (fun x => unipotentGL2 x) f g := by
  rw [constantTerm, boxIntegral, ← boxCond_eq]
  rfl

private abbrev saturation (N : Set (AdelicGL2 (𝓞 F) F)) : Set (AdelicGL2 (𝓞 F) F) :=
  ⋃ γ : (globalPoints (𝓞 F) F).range, (fun g => (γ : AdelicGL2 (𝓞 F) F) * g) ⁻¹' N

private theorem subset_saturation (N : Set (AdelicGL2 (𝓞 F) F)) : N ⊆ saturation F N := fun g hg =>
  Set.mem_iUnion.2 ⟨1, by simpa using hg⟩

private theorem measurableSet_saturation [Countable (globalPoints (𝓞 F) F).range] {N : Set (AdelicGL2 (𝓞 F) F)}
    (hN : MeasurableSet N) : MeasurableSet (saturation F N) :=
  MeasurableSet.iUnion fun γ => hN.preimage (measurable_const_mul (γ : AdelicGL2 (𝓞 F) F))

private theorem measure_saturation_eq_zero [Countable (globalPoints (𝓞 F) F).range] {N : Set (AdelicGL2 (𝓞 F) F)}
    (hN : adelicGLHaar (Fin 2) (𝓞 F) F N = 0) : adelicGLHaar (Fin 2) (𝓞 F) F (saturation F N) = 0 :=
  measure_iUnion_null fun γ => by rw [measure_preimage_mul]; exact hN

private theorem mul_mem_saturation_iff (N : Set (AdelicGL2 (𝓞 F) F)) (γ₀ : (globalPoints (𝓞 F) F).range)
    (g : AdelicGL2 (𝓞 F) F) : (γ₀ : AdelicGL2 (𝓞 F) F) * g ∈ saturation F N ↔ g ∈ saturation F N := by
  simp only [saturation, Set.mem_iUnion, Set.mem_preimage]
  constructor
  · rintro ⟨γ, hγ⟩
    exact ⟨γ * γ₀, by simpa [mul_assoc] using hγ⟩
  · rintro ⟨γ, hγ⟩
    exact ⟨γ * γ₀⁻¹, by simpa [mul_assoc] using hγ⟩

private theorem constantTerm_boxCond_mul_eq_of_mem_rationalTorusUnipotent (χ : AdelicGL2 (𝓞 F) F → ℂ)
    (hχ : ∀ γ : (globalPoints (𝓞 F) F).range, ∀ h : AdelicGL2 (𝓞 F) F, χ ((γ : AdelicGL2 (𝓞 F) F) * h) = χ h)
    {t : AdelicGL2 (𝓞 F) F} (ht : t ∈ rationalTorusUnipotent F) (g : AdelicGL2 (𝓞 F) F) :
    constantTerm (boxCond F) (fun x => unipotentGL2 x) χ (t * g)
      = constantTerm (boxCond F) (fun x => unipotentGL2 x) χ g := by
  have hborel : ∀ γ ∈ borelSubgroup F, ∀ h : AdelicGL2 (𝓞 F) F, χ (globalPoints (𝓞 F) F γ * h) = χ h :=
    fun γ _ h => hχ ⟨globalPoints (𝓞 F) F γ, γ, rfl⟩ h
  have hunip : ∀ (k : F) (h : AdelicGL2 (𝓞 F) F), χ (globalPoints (𝓞 F) F (unipotentGL2 k) * h) = χ h :=
    fun k h => hχ ⟨_, unipotentGL2 k, rfl⟩ h
  let K : Subgroup (AdelicGL2 (𝓞 F) F) :=
    { carrier := {t | ∀ g : AdelicGL2 (𝓞 F) F,
          constantTerm (boxCond F) (fun x => unipotentGL2 x) χ (t * g)
            = constantTerm (boxCond F) (fun x => unipotentGL2 x) χ g}
      one_mem' := fun g => by rw [one_mul]
      mul_mem' := fun {x y} hx hy g => by rw [mul_assoc, hx (y * g), hy g]
      inv_mem' := fun {x} hx g => by
        have h := hx (x⁻¹ * g)
        rw [mul_inv_cancel_left] at h
        exact h.symm }
  have hle : rationalTorusUnipotent F ≤ K := by
    refine sup_le (sup_le ?_ ?_) ?_
    ·
      rintro _ ⟨a, rfl⟩ g
      exact constantTerm_adelicBox_globalPoints_mul_of_mem_borelSubgroup F hborel
        (by simp [mem_borelSubgroup_iff, Matrix.scalar_apply]) g
    ·
      rintro _ ⟨a, rfl⟩ g
      exact constantTerm_adelicBox_globalPoints_mul_of_mem_borelSubgroup F hborel
        (by simp [mem_borelSubgroup_iff, diagOne, Matrix.diagonal_apply_ne]) g
    ·
      rintro _ ⟨x, rfl⟩ g
      exact constantTerm_adelicBox_unipotentGL2_mul F hunip x.toAdd g
  exact hle ht g

private theorem ae_boxIntegral_out_eq_of_ae_eq [Countable (globalPoints (𝓞 F) F).range]
    (hcont : Continuous fun x : AdeleRing (𝓞 F) F => unipotentGL2 x)
    (f₁ f₂ : AdelicGL2 (𝓞 F) F → ℂ) (he : f₁ =ᵐ[adelicGLHaar (Fin 2) (𝓞 F) F] f₂) :
    ∀ᵐ q ∂(rationalTorusUnipotentQuotientMeasure F), boxIntegral F f₁ q.out = boxIntegral F f₂ q.out := by
  set μ : Measure (AdelicGL2 (𝓞 F) F) := adelicGLHaar (Fin 2) (𝓞 F) F with hμ

  set N₀ : Set (AdelicGL2 (𝓞 F) F) := toMeasurable μ {g | f₁ g ≠ f₂ g} with hN₀
  have hN₀m : MeasurableSet N₀ := measurableSet_toMeasurable _ _
  have hN₀0 : μ N₀ = 0 := by rw [hN₀, measure_toMeasurable]; exact ae_iff.1 he
  have hsub : {g | f₁ g ≠ f₂ g} ⊆ N₀ := subset_toMeasurable _ _
  set N' : Set (AdelicGL2 (𝓞 F) F) := saturation F N₀ with hN'
  have hN'm : MeasurableSet N' := measurableSet_saturation F hN₀m
  have hN'0 : μ N' = 0 := measure_saturation_eq_zero F hN₀0

  set E : Set (AdelicGL2 (𝓞 F) F × AdeleRing (𝓞 F) F) := {p | unipotentGL2 p.2 * p.1 ∈ N'} with hE
  have hEm : MeasurableSet E := hN'm.preimage ((hcont.measurable.comp measurable_snd).mul measurable_fst)
  set W : AdelicGL2 (𝓞 F) F → ℝ≥0∞ := fun g => boxCond F {u | unipotentGL2 u * g ∈ N'} with hW
  have hWsec : ∀ g, W g = ∫⁻ u, E.indicator (fun _ => (1 : ℝ≥0∞)) (g, u) ∂(boxCond F) := fun g => by
    have hs : MeasurableSet {u : AdeleRing (𝓞 F) F | unipotentGL2 u * g ∈ N'} :=
      hN'm.preimage (hcont.measurable.mul_const g)
    rw [hW]
    simp only
    rw [← lintegral_indicator_one hs]
    congr 1
  have hWm : Measurable W := by
    have h : Measurable fun g => boxCond F (Prod.mk g ⁻¹' E) := measurable_measure_prodMk_left hEm
    exact h
  have hWint : ∫⁻ g, W g ∂μ = 0 := by
    simp_rw [hWsec]
    have hEu : AEMeasurable (Function.uncurry fun (g : AdelicGL2 (𝓞 F) F) (u : AdeleRing (𝓞 F) F) =>
        E.indicator (fun _ => (1 : ℝ≥0∞)) (g, u)) (μ.prod (boxCond F)) :=
      (measurable_one.indicator hEm).aemeasurable
    rw [lintegral_lintegral_swap hEu]
    have hinner : ∀ u : AdeleRing (𝓞 F) F, ∫⁻ g, E.indicator (fun _ => (1 : ℝ≥0∞)) (g, u) ∂μ = 0 := fun u => by
      have hpre : MeasurableSet ((fun g : AdelicGL2 (𝓞 F) F => unipotentGL2 u * g) ⁻¹' N') :=
        hN'm.preimage (measurable_const_mul _)
      have hfun : (fun g => E.indicator (fun _ => (1 : ℝ≥0∞)) (g, u))
          = ((fun g : AdelicGL2 (𝓞 F) F => unipotentGL2 u * g) ⁻¹' N').indicator fun _ => (1 : ℝ≥0∞) := by
        classical
        ext g
        simp [hE, Set.indicator_apply]
      rw [hfun, lintegral_indicator_const hpre, one_mul, hμ, measure_preimage_mul]
      exact hN'0
    simp only [hinner, lintegral_zero]
  have hWae : ∀ᵐ g ∂μ, W g = 0 := (lintegral_eq_zero_iff hWm).1 hWint

  set Z : Set (AdelicGL2 (𝓞 F) F) := {g | ¬ W g = 0} with hZ
  have hZm : MeasurableSet Z := (hWm (measurableSet_singleton (0 : ℝ≥0∞))).compl
  have hZ0 : μ Z = 0 := ae_iff.1 hWae

  set χ : AdelicGL2 (𝓞 F) F → ℂ := N'.indicator fun _ => (1 : ℂ) with hχ
  have hχinv : ∀ γ : (globalPoints (𝓞 F) F).range, ∀ h : AdelicGL2 (𝓞 F) F,
      χ ((γ : AdelicGL2 (𝓞 F) F) * h) = χ h := fun γ h => by
    classical
    simp only [hχ, hN', Set.indicator_apply, mul_mem_saturation_iff]
  have hWct : ∀ g, constantTerm (boxCond F) (fun x => unipotentGL2 x) χ g = (((W g).toReal : ℝ) : ℂ) := fun g => by
    have hs : MeasurableSet {u : AdeleRing (𝓞 F) F | unipotentGL2 u * g ∈ N'} :=
      hN'm.preimage (hcont.measurable.mul_const g)
    have hfun : (fun u => constantTermIntegrand (fun x : AdeleRing (𝓞 F) F => unipotentGL2 x) χ g u)
        = {u : AdeleRing (𝓞 F) F | unipotentGL2 u * g ∈ N'}.indicator fun _ => (1 : ℂ) := by
      classical
      ext u
      simp [constantTermIntegrand, hχ, Set.indicator_apply]
    rw [constantTerm, hfun, integral_indicator_const (1 : ℂ) hs]
    simp [hW, measureReal_def]
  have hWinv : ∀ t : rationalTorusUnipotent F, ∀ g : AdelicGL2 (𝓞 F) F, W ((t : AdelicGL2 (𝓞 F) F) * g) = W g :=
    fun t g => by
      have h := constantTerm_boxCond_mul_eq_of_mem_rationalTorusUnipotent F χ hχinv t.2 g
      rw [hWct, hWct] at h
      exact (ENNReal.toReal_eq_toReal_iff' (measure_ne_top _ _) (measure_ne_top _ _)).1 (Complex.ofReal_inj.1 h)
  have hZinv : ∀ (t : rationalTorusUnipotent F) (g : AdelicGL2 (𝓞 F) F), t • g ∈ Z ↔ g ∈ Z := fun t g => by
    simp only [hZ, Set.mem_setOf_eq, Subgroup.smul_def, smul_eq_mul, hWinv]

  have hdesc := ae_out_notMem_of_invariant_of_null μ (rationalTorusUnipotent F) (rationalTorusUnipotentHaar F) Z
    hZm hZ0 hZinv
  rw [rationalTorusUnipotentQuotientMeasure]
  filter_upwards [hdesc] with q hq
  have hW0 : W q.out = 0 := by
    by_contra h
    exact hq h
  have hfib : ∀ᵐ u ∂(boxCond F), f₁ (unipotentGL2 u * q.out) = f₂ (unipotentGL2 u * q.out) := by
    have h0 : boxCond F {u | unipotentGL2 u * q.out ∈ N'} = 0 := hW0
    filter_upwards [measure_eq_zero_iff_ae_notMem.1 h0] with u hu
    by_contra hne
    exact hu (subset_saturation F N₀ (hsub hne))
  rw [boxIntegral, boxIntegral, ← boxCond_eq]
  exact integral_congr_ae hfib

private theorem countable_numberField : Countable F :=
  Countable.of_equiv (Fin (Module.finrank ℚ F) → ℚ) (Module.finBasis ℚ F).equivFun.symm.toEquiv

private theorem countable_globalPoints_range : Countable (globalPoints (𝓞 F) F).range := by
  haveI := countable_numberField F
  haveI : Countable (Matrix (Fin 2) (Fin 2) F) := inferInstanceAs (Countable (Fin 2 → Fin 2 → F))
  haveI : Countable (Matrix.GeneralLinearGroup (Fin 2) F) := Units.val_injective.countable
  exact (MonoidHom.rangeRestrict_surjective _).countable

private theorem measurable_boxMap : Measurable (boxMap F) := by
  have hc : Continuous fun u : AdeleRing (𝓞 F) F =>
      (⟨unipotentGL2 u, (boxMap F u).2⟩ : rationalTorusUnipotent F) :=
    continuous_unipotentGL2.subtype_mk _
  exact hc.measurable

private theorem measurable_constantTerm_boxCond (h : AdelicGL2 (𝓞 F) F → ℂ) (hm : Measurable h) :
    Measurable fun g => constantTerm (boxCond F) (fun x => unipotentGL2 x) h g := by
  haveI : IsProbabilityMeasure (boxCond F) := isProbabilityMeasure_cond_adelicBox F
  have hj : Measurable fun p : AdelicGL2 (𝓞 F) F × AdeleRing (𝓞 F) F => h (unipotentGL2 p.2 * p.1) :=
    hm.comp ((continuous_unipotentGL2.measurable.comp measurable_snd).mul measurable_fst)
  simp only [constantTerm, constantTermIntegrand]
  exact (hj.stronglyMeasurable.integral_prod_right' (ν := boxCond F)).measurable

private theorem constantTerm_boxCond_of_forall_unipotentGL2_mul (k : AdelicGL2 (𝓞 F) F → ℂ)
    (hN : ∀ (x : AdeleRing (𝓞 F) F) (g : AdelicGL2 (𝓞 F) F), k (unipotentGL2 x * g) = k g)
    (g : AdelicGL2 (𝓞 F) F) : constantTerm (boxCond F) (fun x => unipotentGL2 x) k g = k g := by
  haveI : IsProbabilityMeasure (boxCond F) := isProbabilityMeasure_cond_adelicBox F
  have hfun : (fun q => constantTermIntegrand (fun x : AdeleRing (𝓞 F) F => unipotentGL2 x) k g q) = fun _ => k g := by
    funext q
    exact hN q g
  rw [constantTerm, hfun]
  simp [integral_const, measureReal_def]

private theorem constantTerm_boxCond_constantTerm_boxCond (f : AdelicGL2 (𝓞 F) F → ℂ)
    (hrat : ∀ (k : F) (g : AdelicGL2 (𝓞 F) F), f (globalPoints (𝓞 F) F (unipotentGL2 k) * g) = f g)
    (g : AdelicGL2 (𝓞 F) F) :
    constantTerm (boxCond F) (fun x => unipotentGL2 x) (constantTerm (boxCond F) (fun x => unipotentGL2 x) f) g
      = constantTerm (boxCond F) (fun x => unipotentGL2 x) f g :=
  constantTerm_boxCond_of_forall_unipotentGL2_mul F (constantTerm (boxCond F) (fun x => unipotentGL2 x) f)
    (fun x y => constantTerm_adelicBox_unipotentGL2_mul F hrat x y) g

private theorem exists_isFundamentalDomain_borelImage :
    ∃ S : Set (AdelicGL2 (𝓞 F) F),
      IsFundamentalDomain ((borelSubgroup F).map (globalPoints (𝓞 F) F)) S (adelicGLHaar (Fin 2) (𝓞 F) F) := by
  haveI := countable_numberField F
  haveI := countable_globalPoints_range F
  obtain ⟨D, hD⟩ := exists_isFundamentalDomain_globalPoints_range F
  exact ⟨_, isFundamentalDomain_iUnion_bruhatRep F (adelicGLHaar (Fin 2) (𝓞 F) F) D hD⟩

private theorem mul_mem_slab_iff (d₁ d₂ : ℝ) {γ : AdelicGL2 (𝓞 F) F} (hγ : γ ∈ (globalPoints (𝓞 F) F).range)
    (x : AdelicGL2 (𝓞 F) F) : γ * x ∈ slab F d₁ d₂ ↔ x ∈ slab F d₁ d₂ := by
  obtain ⟨m, rfl⟩ := hγ
  simp only [slab, Set.mem_setOf_eq, map_mul, NumberField.TateGlobal.ideleNorm_mul, ideleNorm_det_globalPoints,
    one_mul]

private theorem measurableSet_setOf_out_mem_slab (d₁ d₂ : ℝ) :
    MeasurableSet {q : RationalTorusUnipotentQuotient F | q.out ∈ slab F d₁ d₂} := by
  have h : {q : RationalTorusUnipotentQuotient F | q.out ∈ slab F d₁ d₂}
      = slabQuot F ideleNorm_det_globalPoints d₁ d₂ :=
    Set.ext fun q => out_mem_slab_iff_mem_slabQuot F ideleNorm_det_globalPoints d₁ d₂ q
  rw [h]
  exact measurableSet_slabQuot F _ d₁ d₂ (NumberField.TateGlobal.measurableSet_setOf_ideleNorm_det_mem_Icc F d₁ d₂)

private theorem setIntegral_indicator_mul_conj_eq_setIntegral_quotient (d₁ d₂ : ℝ)
    (S : Set (AdelicGL2 (𝓞 F) F))
    (hS : IsFundamentalDomain ((borelSubgroup F).map (globalPoints (𝓞 F) F)) S (adelicGLHaar (Fin 2) (𝓞 F) F))
    (φ : AdelicGL2 (𝓞 F) F → ℂ) (hφm : Measurable φ)
    (hφB : ∀ b ∈ (borelSubgroup F).map (globalPoints (𝓞 F) F), ∀ g : AdelicGL2 (𝓞 F) F, φ (b * g) = φ g)
    (hφN : ∀ (u : AdeleRing (𝓞 F) F) (y : AdelicGL2 (𝓞 F) F), φ (unipotentGL2 u * y) = φ y)
    (h : AdelicGL2 (𝓞 F) F → ℂ) (hm : Measurable h)
    (hB : ∀ b ∈ (borelSubgroup F).map (globalPoints (𝓞 F) F), ∀ g : AdelicGL2 (𝓞 F) F, h (b * g) = h g)
    (hfin : ∫⁻ g in S, ‖(slab F d₁ d₂).indicator (fun x => φ x * (starRingEnd ℂ) (h x)) g‖ₑ
      ∂(adelicGLHaar (Fin 2) (𝓞 F) F) < ∞) :
    ∫ g in S, (slab F d₁ d₂).indicator (fun x => φ x * (starRingEnd ℂ) (h x)) g ∂(adelicGLHaar (Fin 2) (𝓞 F) F)
      = ∫ q in {q : RationalTorusUnipotentQuotient F | q.out ∈ slab F d₁ d₂},
          φ q.out * (starRingEnd ℂ) (constantTerm (boxCond F) (fun x => unipotentGL2 x) h q.out)
        ∂(rationalTorusUnipotentQuotientMeasure F) := by
  set μ : Measure (AdelicGL2 (𝓞 F) F) := adelicGLHaar (Fin 2) (𝓞 F) F with hμ
  set k : AdelicGL2 (𝓞 F) F → ℂ := (slab F d₁ d₂).indicator fun x => φ x * (starRingEnd ℂ) (h x) with hk
  have hslab : MeasurableSet (slab F d₁ d₂) := NumberField.TateGlobal.measurableSet_setOf_ideleNorm_det_mem_Icc F d₁ d₂
  have hkm : Measurable k := (hφm.mul (Complex.continuous_conj.measurable.comp hm)).indicator hslab
  have hkB : ∀ b ∈ (borelSubgroup F).map (globalPoints (𝓞 F) F), ∀ g : AdelicGL2 (𝓞 F) F, k (b * g) = k g := by
    intro b hb g
    have hbg := mul_mem_slab_iff F d₁ d₂ (borel_map_le_range F hb) g
    by_cases hg : g ∈ slab F d₁ d₂
    · simp only [hk, Set.indicator_of_mem hg, Set.indicator_of_mem (hbg.2 hg), hφB b hb g, hB b hb g]
    · simp only [hk, Set.indicator_of_notMem hg, Set.indicator_of_notMem (fun h' => hg (hbg.1 h'))]
  have hrow := isFundamentalDomain_boxSheet_rationalTorusUnipotent F
  obtain ⟨hle, hcount, -, hT, -⟩ := hrow
  obtain ⟨hHaar, hRight⟩ := isHaarMeasure_rationalTorusUnipotentHaar_and_isMulRightInvariant F
  haveI := hcount
  haveI := hHaar
  haveI := hRight
  obtain ⟨-, -, step3⟩ := HaarQuotient.integrable_setIntegral_mul_out_and_setIntegral_eq_integral_setIntegral_mul_out
    μ (rationalTorusUnipotent F) (isClosed_rationalTorusUnipotent F) (rationalTorusUnipotentHaar F)
    ((borelSubgroup F).map (globalPoints (𝓞 F) F)) hle k hkm hkB S hS (boxSheet F) hT hfin
  have step4 : ∀ q : RationalTorusUnipotentQuotient F,
      ∫ x in boxSheet F, k ((x : AdelicGL2 (𝓞 F) F) * q.out) ∂(rationalTorusUnipotentHaar F)
        = (slab F d₁ d₂).indicator (fun g => φ g * (starRingEnd ℂ) (boxIntegral F h g)) q.out := fun q =>
    setIntegral_boxSheet_integrand_eq F (measurable_boxMap F) d₁ d₂ φ h hφN q.out
      ((hm.comp (measurable_subtype_coe.mul_const q.out)).aestronglyMeasurable)
  have hind : ∀ q : RationalTorusUnipotentQuotient F,
      (slab F d₁ d₂).indicator (fun g => φ g * (starRingEnd ℂ) (boxIntegral F h g)) q.out
        = {q : RationalTorusUnipotentQuotient F | q.out ∈ slab F d₁ d₂}.indicator
            (fun q => φ q.out * (starRingEnd ℂ) (boxIntegral F h q.out)) q := fun q => by
    by_cases hq : q.out ∈ slab F d₁ d₂
    · rw [Set.indicator_of_mem hq, Set.indicator_of_mem (show q ∈ {q : RationalTorusUnipotentQuotient F |
        q.out ∈ slab F d₁ d₂} from hq)]
    · rw [Set.indicator_of_notMem hq, Set.indicator_of_notMem (show q ∉ {q : RationalTorusUnipotentQuotient F |
        q.out ∈ slab F d₁ d₂} from hq)]
  calc ∫ g in S, k g ∂μ
      = ∫ q, (∫ x in boxSheet F, k ((x : AdelicGL2 (𝓞 F) F) * q.out) ∂(rationalTorusUnipotentHaar F))
          ∂(rationalTorusUnipotentQuotientMeasure F) := by
        rw [rationalTorusUnipotentQuotientMeasure]; exact step3
    _ = ∫ q in {q : RationalTorusUnipotentQuotient F | q.out ∈ slab F d₁ d₂},
          φ q.out * (starRingEnd ℂ) (boxIntegral F h q.out) ∂(rationalTorusUnipotentQuotientMeasure F) := by
        simp only [step4, hind]
        exact integral_indicator (measurableSet_setOf_out_mem_slab F d₁ d₂)
    _ = ∫ q in {q : RationalTorusUnipotentQuotient F | q.out ∈ slab F d₁ d₂},
          φ q.out * (starRingEnd ℂ) (constantTerm (boxCond F) (fun x => unipotentGL2 x) h q.out)
        ∂(rationalTorusUnipotentQuotientMeasure F) := by
        simp only [boxIntegral_eq_constantTerm]

private theorem setIntegral_inter_slab_mul_conj_eq_setIntegral_quotient (d₁ d₂ : ℝ)
    (S : Set (AdelicGL2 (𝓞 F) F))
    (hS : IsFundamentalDomain ((borelSubgroup F).map (globalPoints (𝓞 F) F)) S (adelicGLHaar (Fin 2) (𝓞 F) F))
    (φ : AdelicGL2 (𝓞 F) F → ℂ) (hφm : Measurable φ)
    (hφB : ∀ b ∈ (borelSubgroup F).map (globalPoints (𝓞 F) F), ∀ g : AdelicGL2 (𝓞 F) F, φ (b * g) = φ g)
    (hφN : ∀ (u : AdeleRing (𝓞 F) F) (y : AdelicGL2 (𝓞 F) F), φ (unipotentGL2 u * y) = φ y)
    (h : AdelicGL2 (𝓞 F) F → ℂ) (hm : Measurable h)
    (hB : ∀ b ∈ (borelSubgroup F).map (globalPoints (𝓞 F) F), ∀ g : AdelicGL2 (𝓞 F) F, h (b * g) = h g)
    (hfin : ∫⁻ g in S ∩ slab F d₁ d₂, ‖φ g * (starRingEnd ℂ) (h g)‖ₑ ∂(adelicGLHaar (Fin 2) (𝓞 F) F) < ∞) :
    ∫ g in S ∩ slab F d₁ d₂, φ g * (starRingEnd ℂ) (h g) ∂(adelicGLHaar (Fin 2) (𝓞 F) F)
      = ∫ q in {q : RationalTorusUnipotentQuotient F | q.out ∈ slab F d₁ d₂},
          φ q.out * (starRingEnd ℂ) (constantTerm (boxCond F) (fun x => unipotentGL2 x) h q.out)
        ∂(rationalTorusUnipotentQuotientMeasure F) := by
  have hslab : MeasurableSet (slab F d₁ d₂) := NumberField.TateGlobal.measurableSet_setOf_ideleNorm_det_mem_Icc F d₁ d₂
  rw [← setIntegral_indicator hslab]
  refine setIntegral_indicator_mul_conj_eq_setIntegral_quotient F d₁ d₂ S hS φ hφm hφB hφN h hm hB ?_
  rw [Set.inter_comm, ← Measure.restrict_restrict hslab, ← lintegral_indicator hslab] at hfin
  refine lt_of_le_of_lt (lintegral_mono fun g => ?_) hfin
  by_cases hg : g ∈ slab F d₁ d₂
  · simp only [Set.indicator_of_mem hg, le_refl]
  · simp only [Set.indicator_of_notMem hg, enorm_zero, zero_le]

private theorem ae_constantTerm_out_eq_of_ae_eq (f₁ f₂ : AdelicGL2 (𝓞 F) F → ℂ)
    (he : f₁ =ᵐ[adelicGLHaar (Fin 2) (𝓞 F) F] f₂) :
    ∀ᵐ q ∂(rationalTorusUnipotentQuotientMeasure F),
      constantTerm (boxCond F) (fun x => unipotentGL2 x) f₁ q.out
        = constantTerm (boxCond F) (fun x => unipotentGL2 x) f₂ q.out := by
  haveI := countable_globalPoints_range F
  exact (ae_boxIntegral_out_eq_of_ae_eq F continuous_unipotentGL2 f₁ f₂ he).mono fun q hq => by
    rw [← boxIntegral_eq_constantTerm, ← boxIntegral_eq_constantTerm]
    exact hq

end SlabPairingDescent
p2m_reactivate "P2MW.S_AutomorphicForm_exists_isSlabProfile_eLpNorm_sub_pseudoEisenstein_lt_of_forall_setIntegral_eq_zero_slab.SlabPairingDescent"

end
p2m_reactivate "P2MW.S_AutomorphicForm_exists_isSlabProfile_eLpNorm_sub_pseudoEisenstein_lt_of_forall_setIntegral_eq_zero_slab.SlabPairingDescent"
end
p2m_reactivate "P2MW.S_AutomorphicForm_exists_isSlabProfile_eLpNorm_sub_pseudoEisenstein_lt_of_forall_setIntegral_eq_zero_slab.SlabPairingDescent"

section
set_option autoImplicit false

open MeasureTheory NumberField NumberField.AdelicHaar NumberField.AdelicLevel NumberField.AdelicBox
p2m_open "NumberField.TateGlobal NumberField.AdelicHeight AutomorphicForm P2MW.S_AutomorphicForm_exists_isSlabProfile_eLpNorm_sub_pseudoEisenstein_lt_of_forall_setIntegral_eq_zero_slab.AutomorphicForm"
open scoped ENNReal

attribute [local instance] NumberField.AdelicHaar.glBorel NumberField.AdelicHaar.borelSpace_glBorel
attribute [local instance] NumberField.Idele.ideleBorel NumberField.Idele.borelSpace_ideleBorel
attribute [local instance] NumberField.Idele.isHaarMeasure_idelicHaar

noncomputable section

namespace SlabBandVolume

section RealWindows

private theorem min_one_le_of_le_mul_self {x p : ℝ} (hx : 0 ≤ x) (h : p ≤ x * x) : min 1 p ≤ x := by
  rcases le_or_gt x 1 with hx1 | hx1
  · exact (min_le_right _ _).trans (h.trans (by nlinarith))
  · exact (min_le_left _ _).trans hx1.le

private theorem le_max_one_of_mul_self_le {x q : ℝ} (hx : 0 ≤ x) (h : x * x ≤ q) : x ≤ max 1 q := by
  rcases le_or_gt x 1 with hx1 | hx1
  · exact hx1.trans (le_max_left _ _)
  · exact (le_max_right _ _).trans' (by nlinarith)

end RealWindows
p2m_reactivate "P2MW.S_AutomorphicForm_exists_isSlabProfile_eLpNorm_sub_pseudoEisenstein_lt_of_forall_setIntegral_eq_zero_slab.SlabPairingDescent"

section Invariance

variable (F : Type) [Field F] [NumberField F]

private def leftInvariantSubgroup {β : Type*} (c : AdelicGL2 (𝓞 F) F → β) : Subgroup (AdelicGL2 (𝓞 F) F) where
  carrier := {h | ∀ g : AdelicGL2 (𝓞 F) F, c (h * g) = c g}
  one_mem' := by
    intro g
    rw [one_mul]
  mul_mem' := by
    intro x y hx hy
    have hx' : ∀ g : AdelicGL2 (𝓞 F) F, c (x * g) = c g := hx
    have hy' : ∀ g : AdelicGL2 (𝓞 F) F, c (y * g) = c g := hy
    intro g
    rw [mul_assoc, hx', hy']
  inv_mem' := by
    intro x hx
    have hx' : ∀ g : AdelicGL2 (𝓞 F) F, c (x * g) = c g := hx
    intro g
    have h := hx' (x⁻¹ * g)
    rw [mul_inv_cancel_left] at h
    exact h.symm

private theorem mem_leftInvariantSubgroup {β : Type*} {c : AdelicGL2 (𝓞 F) F → β} {h : AdelicGL2 (𝓞 F) F} :
    h ∈ leftInvariantSubgroup F c ↔ ∀ g : AdelicGL2 (𝓞 F) F, c (h * g) = c g :=
  Iff.rfl

omit [NumberField F] in

private theorem scalar_mem_borelSubgroup (x : Fˣ) :
    Units.map (Matrix.scalar (Fin 2) : F →+* Matrix (Fin 2) (Fin 2) F).toMonoidHom x ∈ borelSubgroup F := by
  show ((Units.map (Matrix.scalar (Fin 2) : F →+* Matrix (Fin 2) (Fin 2) F).toMonoidHom x :
      Matrix.GeneralLinearGroup (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) 1 0 = 0
  have hval : ((Units.map (Matrix.scalar (Fin 2) : F →+* Matrix (Fin 2) (Fin 2) F).toMonoidHom x :
      Matrix.GeneralLinearGroup (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) = Matrix.scalar (Fin 2) (x : F) := rfl
  rw [hval, Matrix.scalar_apply]
  exact Matrix.diagonal_apply_ne _ (by decide)

omit [NumberField F] in

private theorem diagOne_mem_borelSubgroup (x : Fˣ) : diagOne x ∈ borelSubgroup F := by
  show ((diagOne x : Matrix.GeneralLinearGroup (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) 1 0 = 0
  rw [diagOne_coe_apply]
  exact Matrix.diagonal_apply_ne _ (by decide)

private theorem forall_mem_rationalTorusUnipotent_mul_eq {β : Type*} (c : AdelicGL2 (𝓞 F) F → β)
    (hN : ∀ (x : AdeleRing (𝓞 F) F) (g : AdelicGL2 (𝓞 F) F), c (unipotentGL2 x * g) = c g)
    (hB : ∀ γ ∈ borelSubgroup F, ∀ g : AdelicGL2 (𝓞 F) F, c (globalPoints (𝓞 F) F γ * g) = c g) :
    ∀ h ∈ rationalTorusUnipotent F, ∀ g : AdelicGL2 (𝓞 F) F, c (h * g) = c g := by
  have hle : rationalTorusUnipotent F ≤ leftInvariantSubgroup F c := by
    refine sup_le (sup_le ?_ ?_) ?_
    · rintro _ ⟨x, rfl⟩ g
      exact hB _ (scalar_mem_borelSubgroup F x) g
    · rintro _ ⟨x, rfl⟩ g
      exact hB _ (diagOne_mem_borelSubgroup F x) g
    · rintro _ ⟨x, rfl⟩ g
      exact hN x.toAdd g
  intro h hh g
  have hmem : h ∈ leftInvariantSubgroup F c := hle hh
  exact (mem_leftInvariantSubgroup F).mp hmem g

end Invariance
p2m_reactivate "P2MW.S_AutomorphicForm_exists_isSlabProfile_eLpNorm_sub_pseudoEisenstein_lt_of_forall_setIntegral_eq_zero_slab.SlabPairingDescent"

section Determinants

variable (F : Type) [Field F] [NumberField F]

private theorem
det_unipotentGL2_eq_one
    (x : AdeleRing (𝓞 F) F) : Matrix.GeneralLinearGroup.det (unipotentGL2 x) = 1 := by
  ext
  simp [Matrix.det_fin_two_of]

private theorem det_diagOne_eq (t : (AdeleRing (𝓞 F) F)ˣ) : Matrix.GeneralLinearGroup.det (diagOne t) = t := by
  ext
  simp [Matrix.det_fin_two, diagOne_coe_apply]

private theorem det_centralScalar_eq_sq (z : (AdeleRing (𝓞 F) F)ˣ) :
    Matrix.GeneralLinearGroup.det (centralScalar (𝓞 F) F z) = z ^ 2 := by
  rw [show centralScalar (𝓞 F) F = Matrix.GeneralLinearGroup.scalar (Fin 2) from rfl,
    Matrix.GeneralLinearGroup.det_scalar, Fintype.card_fin]

private theorem ideleNorm_det_unipotentGL2_mul (x : AdeleRing (𝓞 F) F) (g : AdelicGL2 (𝓞 F) F) :
    ideleNorm F (Matrix.GeneralLinearGroup.det (unipotentGL2 x * g)) =
      ideleNorm F (Matrix.GeneralLinearGroup.det g) := by
  rw [map_mul, det_unipotentGL2_eq_one, one_mul]

private theorem ideleNorm_det_globalPoints_mul (γ : Matrix.GeneralLinearGroup (Fin 2) F) (g : AdelicGL2 (𝓞 F) F) :
    ideleNorm F (Matrix.GeneralLinearGroup.det (globalPoints (𝓞 F) F γ * g)) =
      ideleNorm F (Matrix.GeneralLinearGroup.det g) := by
  rw [map_mul, ideleNorm_mul, ideleNorm_det_globalPoints, one_mul]

private theorem ideleNorm_det_centralScalar_mul_diagOne_mul (z t : (AdeleRing (𝓞 F) F)ˣ) (k : AdelicGL2 (𝓞 F) F) :
    ideleNorm F (Matrix.GeneralLinearGroup.det (centralScalar (𝓞 F) F z * diagOne t * k)) =
      ideleNorm F z * ideleNorm F z * ideleNorm F t * ideleNorm F (Matrix.GeneralLinearGroup.det k) := by
  rw [map_mul, map_mul, det_centralScalar_eq_sq, det_diagOne_eq, ideleNorm_mul, ideleNorm_mul, pow_two, ideleNorm_mul]

end Determinants
p2m_reactivate "P2MW.S_AutomorphicForm_exists_isSlabProfile_eLpNorm_sub_pseudoEisenstein_lt_of_forall_setIntegral_eq_zero_slab.SlabPairingDescent"

section Volume

variable (F : Type) [Field F] [NumberField F]

private theorem adelicGLHaar_inter_setOf_ideleNorm_det_mem_Icc_inter_setOf_adelicHeight_mem_Icc_lt_top
    (hN : ∀ (x : AdeleRing (𝓞 F) F) (g : AdelicGL2 (𝓞 F) F),
      adelicHeight F (unipotentGL2 x * g) = adelicHeight F g)
    (hZ : ∀ (z : (AdeleRing (𝓞 F) F)ˣ) (g : AdelicGL2 (𝓞 F) F),
      adelicHeight F (centralScalar (𝓞 F) F z * g) = adelicHeight F g)
    (d₁ d₂ : ℝ) (hd₁ : 0 < d₁) (a b : ℝ) (ha : 0 < a) (S : Set (AdelicGL2 (𝓞 F) F))
    (hS : IsFundamentalDomain ((borelSubgroup F).map (globalPoints (𝓞 F) F)) S (adelicGLHaar (Fin 2) (𝓞 F) F)) :
    adelicGLHaar (Fin 2) (𝓞 F) F
      (S ∩ {g | ideleNorm F (Matrix.GeneralLinearGroup.det g) ∈ Set.Icc d₁ d₂} ∩
        {g | adelicHeight F g ∈ Set.Icc a b}) < ⊤ := by
  rw [Set.inter_assoc]
  set R : Set (AdelicGL2 (𝓞 F) F) := {g | ideleNorm F (Matrix.GeneralLinearGroup.det g) ∈ Set.Icc d₁ d₂} ∩
    {g | adelicHeight F g ∈ Set.Icc a b} with hRdef

  have hRmeas : MeasurableSet R := by
    have hband : MeasurableSet {g : AdelicGL2 (𝓞 F) F | adelicHeight F g ∈ Set.Icc a b} :=
      (continuous_adelicHeight F).measurable measurableSet_Icc
    exact (measurableSet_setOf_ideleNorm_det_mem_Icc F d₁ d₂).inter hband
  have hRN : ∀ (x : AdeleRing (𝓞 F) F) (g : AdelicGL2 (𝓞 F) F), unipotentGL2 x * g ∈ R ↔ g ∈ R := by
    intro x g
    simp only [hRdef, Set.mem_inter_iff, Set.mem_setOf_eq, ideleNorm_det_unipotentGL2_mul, hN]
  have hRB : ∀ γ ∈ borelSubgroup F, ∀ g : AdelicGL2 (𝓞 F) F, globalPoints (𝓞 F) F γ * g ∈ R ↔ g ∈ R := by
    intro γ hγ g
    have hγ' : (γ : Matrix (Fin 2) (Fin 2) F) 1 0 = 0 := hγ
    simp only [hRdef, Set.mem_inter_iff, Set.mem_setOf_eq, ideleNorm_det_globalPoints_mul,
      adelicHeight_globalPoints_mul_of_apply_one_zero_eq_zero F γ hγ']
  set f : AdelicGL2 (𝓞 F) F → ℝ≥0∞ := R.indicator fun _ => 1 with hfdef
  have hfm : Measurable f := measurable_const.indicator hRmeas
  have hfH : ∀ h ∈ rationalTorusUnipotent F, ∀ g : AdelicGL2 (𝓞 F) F, f (h * g) = f g := by
    refine forall_mem_rationalTorusUnipotent_mul_eq F f ?_ ?_
    · intro x g
      by_cases hg : g ∈ R
      · rw [hfdef, Set.indicator_of_mem hg, Set.indicator_of_mem ((hRN x g).2 hg)]
      · rw [hfdef, Set.indicator_of_notMem hg, Set.indicator_of_notMem (fun h => hg ((hRN x g).1 h))]
    · intro γ hγ g
      by_cases hg : g ∈ R
      · rw [hfdef, Set.indicator_of_mem hg, Set.indicator_of_mem ((hRB γ hγ g).2 hg)]
      · rw [hfdef, Set.indicator_of_notMem hg, Set.indicator_of_notMem (fun h => hg ((hRB γ hγ g).1 h))]

  obtain ⟨hle, hcount, -, hT, hTint⟩ := isFundamentalDomain_boxSheet_rationalTorusUnipotent F
  obtain ⟨hHaar, hRight⟩ := isHaarMeasure_rationalTorusUnipotentHaar_and_isMulRightInvariant F
  haveI := hcount
  haveI := hHaar
  haveI := hRight
  haveI := NumberField.AdeleRing.secondCountableTopology_generalLinearGroup_finTwo F
  haveI := isHaarMeasure_adelicGLHaar (Fin 2) (𝓞 F) F
  have h1 : adelicGLHaar (Fin 2) (𝓞 F) F (S ∩ R) = ∫⁻ g in S, f g ∂(adelicGLHaar (Fin 2) (𝓞 F) F) := by
    rw [hfdef, lintegral_indicator_const hRmeas, one_mul, Measure.restrict_apply hRmeas, Set.inter_comm]
  have h2 := HaarQuotient.setLIntegral_eq_lintegral_setLIntegral_mul_out (adelicGLHaar (Fin 2) (𝓞 F) F)
    (rationalTorusUnipotent F) (isClosed_rationalTorusUnipotent F) (rationalTorusUnipotentHaar F) _ hle f hfm
    (fun γ hγ g => hfH γ (hle hγ) g) S hS _ hT
  have h3 : ∀ (T' : Set (rationalTorusUnipotent F)) (q : RationalTorusUnipotentQuotient F),
      ∫⁻ x in T', f ((x : AdelicGL2 (𝓞 F) F) * q.out) ∂(rationalTorusUnipotentHaar F) =
        f q.out * rationalTorusUnipotentHaar F T' := by
    intro T' q
    have hx : ∀ x : rationalTorusUnipotent F, f ((x : AdelicGL2 (𝓞 F) F) * q.out) = f q.out :=
      fun x => hfH x x.2 q.out
    simp only [hx]
    exact setLIntegral_const T' (f q.out)

  have hTeq := hTint (fun _ => 1) measurable_const
  rw [setLIntegral_const, setLIntegral_const, one_mul, one_mul] at hTeq
  have hbox : ((adelicAddHaar (𝓞 F) F (adelicBox F))⁻¹ • adelicAddHaar (𝓞 F) F) (adelicBox F) < ⊤ := by
    rw [Measure.smul_apply, smul_eq_mul,
      ENNReal.inv_mul_cancel (adelicAddHaar_adelicBox_pos F).ne' (adelicAddHaar_adelicBox_lt_top F).ne]
    exact ENNReal.one_lt_top
  have hTlt := lt_of_eq_of_lt hTeq hbox

  obtain ⟨c, -, hc, hiw⟩ := exists_lintegral_rationalTorusUnipotentQuotientMeasure_eq_mul_setLIntegral_iwasawa F
  obtain ⟨D, hDm, hDF, -⟩ :=
    exists_isFundamentalDomain_principalIdeles_forall_exists_integrableOn_min_ideleNorm_pow F
      (NumberField.Idele.idelicHaar F)
  have h4 := hiw D D hDm hDm hDF hDF f hfm hfH
  rw [rationalTorusUnipotentQuotientMeasure] at h4

  obtain ⟨κ, K, hκ, hsand⟩ :=
    exists_forall_mul_adelicHeight_le_adelicHeight_mul_of_isCompact F _ (isCompact_adelicMaximalCompact F)
  have hone : 0 < adelicHeight F (1 : AdelicGL2 (𝓞 F) F) := adelicHeight_pos _
  have hk_bounds : ∀ k : adelicMaximalCompact F,
      κ * adelicHeight F 1 ≤ adelicHeight F (k : AdelicGL2 (𝓞 F) F) ∧
        adelicHeight F (k : AdelicGL2 (𝓞 F) F) ≤ K * adelicHeight F 1 := by
    intro k
    have h := hsand 1 (k : AdelicGL2 (𝓞 F) F) k.2
    rwa [one_mul] at h
  have hκh : 0 < κ * adelicHeight F 1 := mul_pos hκ hone
  have hKh : 0 < K * adelicHeight F 1 := hκh.trans_le ((hk_bounds 1).1.trans (hk_bounds 1).2)
  obtain ⟨k₁, hk₁, hmin⟩ := (isCompact_adelicMaximalCompact F).exists_isMinOn
    ⟨1, (adelicMaximalCompact F).one_mem⟩ (continuous_ideleNorm_det F).continuousOn
  obtain ⟨k₂, hk₂, hmax⟩ := (isCompact_adelicMaximalCompact F).exists_isMaxOn
    ⟨1, (adelicMaximalCompact F).one_mem⟩ (continuous_ideleNorm_det F).continuousOn
  set m₁ : ℝ := ideleNorm F (Matrix.GeneralLinearGroup.det k₁) with hm₁def
  set m₂ : ℝ := ideleNorm F (Matrix.GeneralLinearGroup.det k₂) with hm₂def
  have hm₁ : 0 < m₁ := ideleNorm_pos (Matrix.GeneralLinearGroup.det k₁)
  have hm₂ : 0 < m₂ := ideleNorm_pos (Matrix.GeneralLinearGroup.det k₂)
  have hdet_bounds : ∀ k : adelicMaximalCompact F,
      m₁ ≤ ideleNorm F (Matrix.GeneralLinearGroup.det (k : AdelicGL2 (𝓞 F) F)) ∧
        ideleNorm F (Matrix.GeneralLinearGroup.det (k : AdelicGL2 (𝓞 F) F)) ≤ m₂ :=
    fun k => ⟨isMinOn_iff.1 hmin _ k.2, isMaxOn_iff.1 hmax _ k.2⟩
  set τ₁ : ℝ := a / (K * adelicHeight F 1) with hτ₁def
  set τ₂ : ℝ := max a b / (κ * adelicHeight F 1) with hτ₂def
  have hτ₁ : 0 < τ₁ := div_pos ha hKh
  have hτ₂ : 0 < τ₂ := div_pos (ha.trans_le (le_max_left a b)) hκh
  set p : ℝ := d₁ / (τ₂ * m₂) with hpdef
  set q : ℝ := d₂ / (τ₁ * m₁) with hqdef
  have hp : 0 < p := div_pos hd₁ (mul_pos hτ₂ hm₂)
  have hTw6 := NumberField.Idele.idelicHaar_inter_setOf_ideleNorm_mem_Icc_pos_and_lt_top F D hDm hDF τ₁
    (max τ₂ τ₁ + 1) hτ₁ ((le_max_right τ₂ τ₁).trans_lt (lt_add_one _))
  have hZw6 := NumberField.Idele.idelicHaar_inter_setOf_ideleNorm_mem_Icc_pos_and_lt_top F D hDm hDF (min 1 p)
    (max 1 q + 1) (lt_min one_pos hp) ((min_le_left 1 p).trans_lt ((le_max_left 1 q).trans_lt (lt_add_one _)))
  set Tw : Set (AdeleRing (𝓞 F) F)ˣ := {t | ideleNorm F t ∈ Set.Icc τ₁ (max τ₂ τ₁ + 1)} with hTwdef
  set Zw : Set (AdeleRing (𝓞 F) F)ˣ := {z | ideleNorm F z ∈ Set.Icc (min 1 p) (max 1 q + 1)} with hZwdef

  have hpt : ∀ (z t : (AdeleRing (𝓞 F) F)ˣ) (k : adelicMaximalCompact F),
      f (centralScalar (𝓞 F) F z * diagOne t * (k : AdelicGL2 (𝓞 F) F)) * ENNReal.ofReal ((ideleNorm F t)⁻¹) ≤
        Zw.indicator (fun _ => (1 : ℝ≥0∞)) z * Tw.indicator (fun _ => ENNReal.ofReal τ₁⁻¹) t := by
    intro z t k
    by_cases hg : centralScalar (𝓞 F) F z * diagOne t * (k : AdelicGL2 (𝓞 F) F) ∈ R
    · have hg2 := hg
      rw [hRdef] at hg2
      obtain ⟨hdet, hht⟩ := hg2
      have hdet' : ideleNorm F (Matrix.GeneralLinearGroup.det
          (centralScalar (𝓞 F) F z * diagOne t * (k : AdelicGL2 (𝓞 F) F))) ∈ Set.Icc d₁ d₂ := hdet
      have hht' : adelicHeight F (centralScalar (𝓞 F) F z * diagOne t * (k : AdelicGL2 (𝓞 F) F)) ∈
          Set.Icc a b := hht
      have hnz : 0 < ideleNorm F z := ideleNorm_pos (F := F) z
      have hnt : 0 < ideleNorm F t := ideleNorm_pos (F := F) t
      have hnk : 0 < ideleNorm F (Matrix.GeneralLinearGroup.det (k : AdelicGL2 (𝓞 F) F)) := ideleNorm_pos (F := F) _
      have hnk1 := (hdet_bounds k).1
      have hnk2 := (hdet_bounds k).2
      have hkh1 := (hk_bounds k).1
      have hkh2 := (hk_bounds k).2
      have hhk : 0 < adelicHeight F (k : AdelicGL2 (𝓞 F) F) := adelicHeight_pos _

      have hheight : adelicHeight F (centralScalar (𝓞 F) F z * diagOne t * (k : AdelicGL2 (𝓞 F) F)) =
          ideleNorm F t * adelicHeight F (k : AdelicGL2 (𝓞 F) F) := by
        rw [mul_assoc, hZ, adelicHeight_diagOne_mul]
      have hta : a ≤ ideleNorm F t * adelicHeight F (k : AdelicGL2 (𝓞 F) F) := hheight ▸ hht'.1
      have htb : ideleNorm F t * adelicHeight F (k : AdelicGL2 (𝓞 F) F) ≤ b := hheight ▸ hht'.2
      have hτ₁le : τ₁ ≤ ideleNorm F t := (div_le_iff₀ hKh).2 (by nlinarith)
      have hleτ₂ : ideleNorm F t ≤ τ₂ := (le_div_iff₀ hκh).2 (by nlinarith [le_max_right a b])
      have htT : t ∈ Tw := ⟨hτ₁le, hleτ₂.trans ((le_max_left τ₂ τ₁).trans (lt_add_one _).le)⟩

      have hdetg := ideleNorm_det_centralScalar_mul_diagOne_mul F z t (k : AdelicGL2 (𝓞 F) F)
      have hd₁' : d₁ ≤ ideleNorm F z * ideleNorm F z * ideleNorm F t *
          ideleNorm F (Matrix.GeneralLinearGroup.det (k : AdelicGL2 (𝓞 F) F)) := hdetg ▸ hdet'.1
      have hd₂' : ideleNorm F z * ideleNorm F z * ideleNorm F t *
          ideleNorm F (Matrix.GeneralLinearGroup.det (k : AdelicGL2 (𝓞 F) F)) ≤ d₂ := hdetg ▸ hdet'.2
      have h5 : ideleNorm F z * ideleNorm F z * ideleNorm F t *
          ideleNorm F (Matrix.GeneralLinearGroup.det (k : AdelicGL2 (𝓞 F) F)) ≤
            ideleNorm F z * ideleNorm F z * τ₂ * m₂ := by gcongr
      have h6 : ideleNorm F z * ideleNorm F z * τ₁ * m₁ ≤ ideleNorm F z * ideleNorm F z * ideleNorm F t *
          ideleNorm F (Matrix.GeneralLinearGroup.det (k : AdelicGL2 (𝓞 F) F)) := by gcongr
      have hpz : p ≤ ideleNorm F z * ideleNorm F z :=
        (div_le_iff₀ (mul_pos hτ₂ hm₂)).2 (by rw [← mul_assoc]; exact hd₁'.trans h5)
      have hzq : ideleNorm F z * ideleNorm F z ≤ q :=
        (le_div_iff₀ (mul_pos hτ₁ hm₁)).2 (by rw [← mul_assoc]; exact h6.trans hd₂')
      have hzZ : z ∈ Zw := ⟨min_one_le_of_le_mul_self hnz.le hpz,
        (le_max_one_of_mul_self_le hnz.le hzq).trans (lt_add_one _).le⟩
      simp only [hfdef, Set.indicator_of_mem hg, Set.indicator_of_mem hzZ, Set.indicator_of_mem htT, one_mul]
      exact ENNReal.ofReal_le_ofReal (inv_anti₀ hτ₁ hτ₁le)
    · simp only [hfdef, Set.indicator_of_notMem hg, zero_mul, zero_le]

  have hZne : ∀ z : (AdeleRing (𝓞 F) F)ˣ, Zw.indicator (fun _ => (1 : ℝ≥0∞)) z ≠ ⊤ := by
    intro z
    by_cases hz : z ∈ Zw
    · rw [Set.indicator_of_mem hz]
      exact ENNReal.one_ne_top
    · rw [Set.indicator_of_notMem hz]
      exact ENNReal.zero_ne_top
  have hinner : ∀ z t : (AdeleRing (𝓞 F) F)ˣ,
      ∫⁻ k, f (centralScalar (𝓞 F) F z * diagOne t * (k : AdelicGL2 (𝓞 F) F)) *
          ENNReal.ofReal ((ideleNorm F t)⁻¹) ∂(maximalCompactHaar F) ≤
        Zw.indicator (fun _ => (1 : ℝ≥0∞)) z * Tw.indicator (fun _ => ENNReal.ofReal τ₁⁻¹) t := by
    intro z t
    refine (lintegral_mono fun k => hpt z t k).trans (le_of_eq ?_)
    rw [lintegral_const, measure_univ, mul_one]
  have hTwin : ∫⁻ t in D, Tw.indicator (fun _ => ENNReal.ofReal τ₁⁻¹) t ∂(NumberField.Idele.idelicHaar F) ≤
      ENNReal.ofReal τ₁⁻¹ * NumberField.Idele.idelicHaar F (D ∩ Tw) := by
    refine (lintegral_indicator_le _ _).trans (le_of_eq ?_)
    rw [setLIntegral_const, Measure.restrict_apply' hDm, Set.inter_comm]
  have hKc : ENNReal.ofReal τ₁⁻¹ * NumberField.Idele.idelicHaar F (D ∩ Tw) < ⊤ :=
    ENNReal.mul_lt_top ENNReal.ofReal_lt_top hTw6.2
  have hmid : ∀ z : (AdeleRing (𝓞 F) F)ˣ,
      ∫⁻ t in D, ∫⁻ k, f (centralScalar (𝓞 F) F z * diagOne t * (k : AdelicGL2 (𝓞 F) F)) *
          ENNReal.ofReal ((ideleNorm F t)⁻¹) ∂(maximalCompactHaar F) ∂(NumberField.Idele.idelicHaar F) ≤
        Zw.indicator (fun _ => (1 : ℝ≥0∞)) z *
          (ENNReal.ofReal τ₁⁻¹ * NumberField.Idele.idelicHaar F (D ∩ Tw)) := by
    intro z
    refine (lintegral_mono fun t => hinner z t).trans ?_
    rw [lintegral_const_mul' _ _ (hZne z)]
    exact mul_le_mul' le_rfl hTwin
  have houter : ∫⁻ z in D, Zw.indicator (fun _ => (1 : ℝ≥0∞)) z *
      (ENNReal.ofReal τ₁⁻¹ * NumberField.Idele.idelicHaar F (D ∩ Tw)) ∂(NumberField.Idele.idelicHaar F) < ⊤ := by
    rw [lintegral_mul_const' _ _ hKc.ne]
    refine ENNReal.mul_lt_top ?_ hKc
    refine (lintegral_indicator_le _ _).trans_lt ?_
    rw [setLIntegral_const, Measure.restrict_apply' hDm, one_mul, Set.inter_comm]
    exact hZw6.2

  rw [h1, h2]
  simp only [h3]
  rw [lintegral_mul_const' _ _ hTlt.ne]
  refine ENNReal.mul_lt_top ?_ hTlt
  rw [h4]
  refine ENNReal.mul_lt_top hc.lt_top ?_
  exact (lintegral_mono fun z => hmid z).trans_lt houter

end Volume
p2m_reactivate "P2MW.S_AutomorphicForm_exists_isSlabProfile_eLpNorm_sub_pseudoEisenstein_lt_of_forall_setIntegral_eq_zero_slab.SlabPairingDescent"

end SlabBandVolume
p2m_reactivate "P2MW.S_AutomorphicForm_exists_isSlabProfile_eLpNorm_sub_pseudoEisenstein_lt_of_forall_setIntegral_eq_zero_slab.SlabPairingDescent"

end
p2m_reactivate "P2MW.S_AutomorphicForm_exists_isSlabProfile_eLpNorm_sub_pseudoEisenstein_lt_of_forall_setIntegral_eq_zero_slab.SlabPairingDescent"
end
p2m_reactivate "P2MW.S_AutomorphicForm_exists_isSlabProfile_eLpNorm_sub_pseudoEisenstein_lt_of_forall_setIntegral_eq_zero_slab.SlabPairingDescent"

section
set_option autoImplicit false

open MeasureTheory NumberField NumberField.AdelicHaar NumberField.TateGlobal NumberField.AdelicHeight
open scoped ENNReal NNReal Pointwise

attribute [local instance] NumberField.AdelicHaar.glBorel NumberField.AdelicHaar.borelSpace_glBorel
  NumberField.AdelicHaar.isHaarMeasure_adelicGLHaar
attribute [local instance] NumberField.AdelicHaar.adeleBorel NumberField.AdelicHaar.borelSpace_adeleBorel
attribute [local instance] NumberField.Idele.ideleBorel NumberField.Idele.borelSpace_ideleBorel
  NumberField.Idele.isHaarMeasure_idelicHaar

noncomputable section

namespace AutomorphicForm
p2m_export "AutomorphicForm" "lsXiMemberAt_iff IsAutomorphicFnAt CarrierPins productionPinsOf AdelicGL2 globalPoints centralScalar IsLsXiFunction unipotentGL2 unipotentGL2_coe constantTermIntegrand constantTerm IsSlabProfile pseudoEisenstein pseudoEisenstein_apply isSlabProfile_zero pseudoEisenstein_zero borelSubgroup mem_borelSubgroup_iff globalPoints_apply gl2Weyl adelicWeyl WindowedSiegel.rowNormSq WindowedSiegel.localHeight WindowedSiegel.archHeight WindowedSiegel.archHeight_scalar_entries_mul finite_support_pseudoEisenstein_summand isAutomorphicFnAt_pseudoEisenstein_slab aestronglyMeasurable_adelicGLHaar_of_isAutomorphicFnAt_slab setIntegral_pseudoEisenstein_mul_conj_eq_setIntegral_rationalTorusUnipotentQuotient_slab rationalTorusUnipotent RationalTorusUnipotentQuotient rationalTorusUnipotentHaar rationalTorusUnipotentQuotientMeasure toAdelicUnipotent adelicMaximalCompact isCompact_adelicMaximalCompact maximalCompactHaar constantTerm_adelicBox_globalPoints_mul_of_mem_borelSubgroup constantTerm_adelicBox_unipotentGL2_mul continuous_unipotentGL2 exists_isFundamentalDomain_globalPoints_range exists_lintegral_rationalTorusUnipotentQuotientMeasure_eq_mul_setLIntegral_iwasawa ideleNorm_det_globalPoints isClosed_rationalTorusUnipotent isFundamentalDomain_boxSheet_rationalTorusUnipotent isHaarMeasure_rationalTorusUnipotentHaar_and_isMulRightInvariant"
namespace TwistedCentralAverage
p2m_open "AutomorphicForm"

variable (F : Type) [Field F] [NumberField F]

section LocalFactors

variable {K : Type*} [NormedField K]

private theorem rowNormSq_unipotent_mul (x : K) (g : GL (Fin 2) K) :
    WindowedSiegel.rowNormSq ((unipotentGL2 x * g : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K)
      = WindowedSiegel.rowNormSq (g : Matrix (Fin 2) (Fin 2) K) := by
  unfold WindowedSiegel.rowNormSq
  rw [Matrix.GeneralLinearGroup.coe_mul, unipotentGL2_coe]
  simp [Matrix.mul_apply, Fin.sum_univ_two]

private theorem localHeight_unipotent_mul (x : K) (g : GL (Fin 2) K) :
    WindowedSiegel.localHeight (unipotentGL2 x * g) = WindowedSiegel.localHeight g := by
  unfold WindowedSiegel.localHeight
  rw [rowNormSq_unipotent_mul, Matrix.GeneralLinearGroup.coe_mul, Matrix.det_mul, unipotentGL2_coe,
    Matrix.det_fin_two_of]
  simp

private theorem rowMaxNorm_unipotent_mul (x : K) (g : GL (Fin 2) K) :
    rowMaxNorm ((unipotentGL2 x * g : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K)
      = rowMaxNorm (g : Matrix (Fin 2) (Fin 2) K) := by
  unfold rowMaxNorm
  rw [Matrix.GeneralLinearGroup.coe_mul, unipotentGL2_coe]
  simp [Matrix.mul_apply, Fin.sum_univ_two]

private theorem finLocalHeight_unipotent_mul (x : K) (g : GL (Fin 2) K) :
    finLocalHeight (unipotentGL2 x * g) = finLocalHeight g := by
  unfold finLocalHeight
  rw [rowMaxNorm_unipotent_mul, Matrix.GeneralLinearGroup.coe_mul, Matrix.det_mul, unipotentGL2_coe,
    Matrix.det_fin_two_of]
  simp

private theorem finLocalHeight_scalar_entries_mul {s : GL (Fin 2) K} {c : K} (hc : c ≠ 0)
    (h00 : (s : Matrix (Fin 2) (Fin 2) K) 0 0 = c) (h01 : (s : Matrix (Fin 2) (Fin 2) K) 0 1 = 0)
    (h10 : (s : Matrix (Fin 2) (Fin 2) K) 1 0 = 0) (h11 : (s : Matrix (Fin 2) (Fin 2) K) 1 1 = c)
    (g : GL (Fin 2) K) : finLocalHeight (s * g) = finLocalHeight g := by
  have hdet : ((s * g : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K).det
      = c * c * (g : Matrix (Fin 2) (Fin 2) K).det := by
    rw [Matrix.GeneralLinearGroup.coe_mul, Matrix.det_mul, Matrix.det_fin_two, h00, h01, h10, h11]
    ring
  have hrow : rowMaxNorm ((s * g : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K)
      = ‖c‖ * rowMaxNorm (g : Matrix (Fin 2) (Fin 2) K) := by
    unfold rowMaxNorm
    rw [Matrix.GeneralLinearGroup.coe_mul]
    simp only [Matrix.mul_apply, Fin.sum_univ_two, h10, h11, zero_mul, zero_add, norm_mul]
    exact (mul_max_of_nonneg _ _ (norm_nonneg c)).symm
  have hc' : (0 : ℝ) < ‖c‖ ^ 2 := by positivity
  unfold finLocalHeight
  rw [hdet, hrow, mul_pow, norm_mul, norm_mul, ← pow_two]
  exact mul_div_mul_left _ _ hc'.ne'

end LocalFactors
p2m_reactivate "P2MW.S_AutomorphicForm_exists_isSlabProfile_eLpNorm_sub_pseudoEisenstein_lt_of_forall_setIntegral_eq_zero_slab.SlabPairingDescent"

private theorem map_unipotentGL2 {R S : Type*} [CommRing R] [CommRing S] (f : R →+* S) (x : R) :
    Matrix.GeneralLinearGroup.map f (unipotentGL2 x) = unipotentGL2 (f x) := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.GeneralLinearGroup.map_apply, unipotentGL2]

private theorem adelicHeight_unipotentGL2_mul (x : AdeleRing (𝓞 F) F) (g : AdelicGL2 (𝓞 F) F) :
    adelicHeight F (unipotentGL2 x * g) = adelicHeight F g := by
  unfold adelicHeight
  congr 1
  · rw [map_mul]
    unfold WindowedSiegel.archHeight
    refine Finset.prod_congr rfl fun v _ => ?_
    rw [map_mul]
    congr 1
    rw [AdelicLevel.glArch, map_unipotentGL2, AdelicLevel.archComponent, map_unipotentGL2,
      localHeight_unipotent_mul]
  · rw [map_mul]
    unfold finHeight
    refine finprod_congr fun v => ?_
    rw [map_mul, AdelicLevel.glFin, map_unipotentGL2, AdelicLevel.finComponent, map_unipotentGL2,
      finLocalHeight_unipotent_mul]

private theorem adelicHeight_centralScalar_mul (z : (AdeleRing (𝓞 F) F)ˣ) (g : AdelicGL2 (𝓞 F) F) :
    adelicHeight F (centralScalar (𝓞 F) F z * g) = adelicHeight F g := by
  have hent : ∀ (S : Type) [CommRing S] (f : AdeleRing (𝓞 F) F →+* S) (i j : Fin 2),
      ((Matrix.GeneralLinearGroup.map f (centralScalar (𝓞 F) F z) : GL (Fin 2) S) :
        Matrix (Fin 2) (Fin 2) S) i j = if i = j then f z else 0 := by
    intro S _ f i j
    rw [Matrix.GeneralLinearGroup.map_apply]
    fin_cases i <;> fin_cases j <;> simp [centralScalar, Matrix.GeneralLinearGroup.scalar]
  unfold adelicHeight
  congr 1
  · rw [map_mul]
    exact WindowedSiegel.archHeight_scalar_entries_mul F (z := AdelicLevel.adeleArch (𝓞 F) F z)
      (fun v => (z.isUnit.map ((AdelicLevel.archEval F v).comp
        (AdelicLevel.adeleArch (𝓞 F) F))).ne_zero)
      (hent _ _ 0 0) (hent _ _ 0 1) (hent _ _ 1 0) (hent _ _ 1 1) _
  · rw [map_mul]
    unfold finHeight
    refine finprod_congr fun v => ?_
    rw [map_mul, AdelicLevel.glFin, AdelicLevel.finComponent, ← MonoidHom.comp_apply,
      ← Matrix.GeneralLinearGroup.map_comp]
    refine finLocalHeight_scalar_entries_mul
      (c := ((AdelicLevel.finAdeleEval (𝓞 F) F v).comp (AdelicLevel.adeleFin (𝓞 F) F)) z)
      (z.isUnit.map _).ne_zero (hent _ _ 0 0) (hent _ _ 0 1) (hent _ _ 1 0) (hent _ _ 1 1) _

private theorem det_globalPoints (m : GL (Fin 2) F) :
    Matrix.GeneralLinearGroup.det (globalPoints (𝓞 F) F m)
      = Units.map (algebraMap F (AdeleRing (𝓞 F) F)).toMonoidHom (Matrix.GeneralLinearGroup.det m) := by
  ext
  simp [globalPoints, Matrix.GeneralLinearGroup.map, RingHom.map_det]

private theorem ideleNorm_det_globalPoints (m : GL (Fin 2) F) :
    NumberField.TateGlobal.ideleNorm F (Matrix.GeneralLinearGroup.det (globalPoints (𝓞 F) F m)) = 1 := by
  rw [det_globalPoints, NumberField.TateGlobal.ideleNorm,
    @NumberField.AdeleRing.distribHaarChar_algebraMap F _ _ (NumberField.AdelicHaar.adeleBorel (𝓞 F) F)
      (NumberField.AdelicHaar.borelSpace_adeleBorel (𝓞 F) F) (Matrix.GeneralLinearGroup.det m)]
  simp

private theorem mul_centralScalar_comm' (z : (AdeleRing (𝓞 F) F)ˣ) (X : AdelicGL2 (𝓞 F) F) :
    X * centralScalar (𝓞 F) F z = centralScalar (𝓞 F) F z * X := by
  refine Units.ext ?_
  show (X : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 F) F)) * Matrix.scalar (Fin 2) (z : AdeleRing (𝓞 F) F)
    = Matrix.scalar (Fin 2) (z : AdeleRing (𝓞 F) F) * (X : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 F) F))
  exact ((Matrix.scalar_commute _ (fun r' => Commute.all _ r') _).eq).symm

private theorem det_centralScalar' (z : (AdeleRing (𝓞 F) F)ˣ) :
    Matrix.GeneralLinearGroup.det (centralScalar (𝓞 F) F z) = z ^ 2 := by
  rw [show centralScalar (𝓞 F) F = Matrix.GeneralLinearGroup.scalar (Fin 2) from rfl,
    Matrix.GeneralLinearGroup.det_scalar, Fintype.card_fin]

private theorem ideleNorm_det_centralScalar_mul (z : (AdeleRing (𝓞 F) F)ˣ) (g : AdelicGL2 (𝓞 F) F) :
    ideleNorm F (Matrix.GeneralLinearGroup.det (centralScalar (𝓞 F) F z * g))
      = ideleNorm F z * ideleNorm F z * ideleNorm F (Matrix.GeneralLinearGroup.det g) := by
  rw [map_mul, det_centralScalar', sq, ideleNorm_mul, ideleNorm_mul]

private theorem exists_centralScalar_eq_globalPoints_scalar {γ : (AdeleRing (𝓞 F) F)ˣ}
    (hγ : γ ∈ M4aHerbrand.principalIdeles (𝓞 F) F) :
    ∃ η : Fˣ, centralScalar (𝓞 F) F γ = globalPoints (𝓞 F) F (Matrix.GeneralLinearGroup.scalar (Fin 2) η) := by
  obtain ⟨η, rfl⟩ := MonoidHom.mem_range.mp hγ
  refine ⟨η, ?_⟩
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [centralScalar, globalPoints, Matrix.GeneralLinearGroup.scalar, Matrix.GeneralLinearGroup.map_apply]

omit [NumberField F] in
private theorem scalar_mem_borelSubgroup (η : Fˣ) :
    Matrix.GeneralLinearGroup.scalar (Fin 2) η ∈ borelSubgroup F := by
  show ((Matrix.GeneralLinearGroup.scalar (Fin 2) η : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) 1 0 = 0
  simp [Matrix.GeneralLinearGroup.scalar]

private theorem continuous_centralScalar : Continuous (centralScalar (𝓞 F) F) := by
  have hdiag : ∀ x : AdeleRing (𝓞 F) F, Matrix.scalar (Fin 2) x = Matrix.diagonal fun _ => x := fun x =>
    Matrix.scalar_apply x
  refine Units.continuous_iff.2 ⟨?_, ?_⟩
  · show Continuous fun z : (AdeleRing (𝓞 F) F)ˣ => Matrix.scalar (Fin 2) (z : AdeleRing (𝓞 F) F)
    simp only [hdiag]
    exact (continuous_pi fun _ => Units.continuous_val).matrix_diagonal
  · show Continuous fun z : (AdeleRing (𝓞 F) F)ˣ =>
      Matrix.scalar (Fin 2) ((z⁻¹ : (AdeleRing (𝓞 F) F)ˣ) : AdeleRing (𝓞 F) F)
    simp only [hdiag]
    exact (continuous_pi fun _ => Units.continuous_coe_inv).matrix_diagonal

private theorem secondCountable_adelicGL2 : SecondCountableTopology (AdelicGL2 (𝓞 F) F) :=
  NumberField.AdeleRing.secondCountableTopology_generalLinearGroup_finTwo F

private theorem measurable_det_norm :
    Measurable fun g : AdelicGL2 (𝓞 F) F => ideleNorm F (Matrix.GeneralLinearGroup.det g) :=
  (continuous_ideleNorm_det F).measurable

private theorem measurable_adelicHeight : Measurable (adelicHeight F) :=
  (continuous_adelicHeight F).measurable

variable {F}

private def xi (ξ : (⊤ : Subgroup (AdeleRing (𝓞 F) F)ˣ) →* ℂˣ) (z : (AdeleRing (𝓞 F) F)ˣ) : ℂ :=
  ((ξ ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ)

private theorem xi_mul (ξ : (⊤ : Subgroup (AdeleRing (𝓞 F) F)ˣ) →* ℂˣ) (z w : (AdeleRing (𝓞 F) F)ˣ) :
    xi ξ (z * w) = xi ξ z * xi ξ w := by
  unfold xi
  rw [show (⟨z * w, Subgroup.mem_top _⟩ : (⊤ : Subgroup (AdeleRing (𝓞 F) F)ˣ))
      = ⟨z, Subgroup.mem_top z⟩ * ⟨w, Subgroup.mem_top w⟩ from rfl, map_mul, Units.val_mul]

private theorem xi_ne_zero (ξ : (⊤ : Subgroup (AdeleRing (𝓞 F) F)ˣ) →* ℂˣ) (z : (AdeleRing (𝓞 F) F)ˣ) :
    xi ξ z ≠ 0 :=
  Units.ne_zero _

private theorem continuous_xi {ξ : (⊤ : Subgroup (AdeleRing (𝓞 F) F)ˣ) →* ℂˣ} (hξ : Continuous ξ) :
    Continuous (xi ξ) := by
  unfold xi
  exact Units.continuous_val.comp (hξ.comp (continuous_id.subtype_mk _))

private theorem measurable_xi {ξ : (⊤ : Subgroup (AdeleRing (𝓞 F) F)ˣ) →* ℂˣ} (hξ : Continuous ξ) :
    Measurable (xi ξ) :=
  (continuous_xi hξ).measurable

private def ct (ν : Measure (AdeleRing (𝓞 F) F)) (w : AdelicGL2 (𝓞 F) F → ℂ) : AdelicGL2 (𝓞 F) F → ℂ :=
  constantTerm ν (fun x => unipotentGL2 x) w

private theorem ct_apply (ν : Measure (AdeleRing (𝓞 F) F)) (w : AdelicGL2 (𝓞 F) F → ℂ) (g : AdelicGL2 (𝓞 F) F) :
    ct ν w g = ∫ x, w (unipotentGL2 x * g) ∂ν :=
  rfl

private theorem ct_centralScalar_mul_of_forall (ν : Measure (AdeleRing (𝓞 F) F)) {u : AdelicGL2 (𝓞 F) F → ℂ}
    {c : ℂ} {z : (AdeleRing (𝓞 F) F)ˣ}
    (hu : ∀ g : AdelicGL2 (𝓞 F) F, u (centralScalar (𝓞 F) F z * g) = c * u g) (g : AdelicGL2 (𝓞 F) F) :
    ct ν u (centralScalar (𝓞 F) F z * g) = c * ct ν u g := by
  rw [ct_apply, ct_apply, ← integral_const_mul]
  refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
  show u (unipotentGL2 x * (centralScalar (𝓞 F) F z * g)) = c * u (unipotentGL2 x * g)
  rw [← mul_assoc, mul_centralScalar_comm' F z (unipotentGL2 x), mul_assoc, hu]

private theorem measurable_ct (ν : Measure (AdeleRing (𝓞 F) F)) [SFinite ν] {w : AdelicGL2 (𝓞 F) F → ℂ}
    (hw : Measurable w) : Measurable (ct ν w) := by
  haveI := secondCountable_adelicGL2 F
  have hshear : Continuous fun p : AdelicGL2 (𝓞 F) F × AdeleRing (𝓞 F) F => unipotentGL2 p.2 * p.1 :=
    (continuous_unipotentGL2.comp continuous_snd).mul continuous_fst
  have hjoint : Measurable fun p : AdelicGL2 (𝓞 F) F × AdeleRing (𝓞 F) F => w (unipotentGL2 p.2 * p.1) :=
    hw.comp hshear.measurable
  show Measurable fun g : AdelicGL2 (𝓞 F) F => ∫ x, w (unipotentGL2 x * g) ∂ν
  exact (hjoint.stronglyMeasurable.integral_prod_right').measurable

private theorem ct_unipotentGL2_mul {w : AdelicGL2 (𝓞 F) F → ℂ}
    (hw : ∀ (γ : GL (Fin 2) F) (g : AdelicGL2 (𝓞 F) F), w (globalPoints (𝓞 F) F γ * g) = w g)
    (x : AdeleRing (𝓞 F) F) (g : AdelicGL2 (𝓞 F) F) :
    ct (ProbabilityTheory.cond (adelicAddHaar (𝓞 F) F) (AdelicBox.adelicBox F)) w (unipotentGL2 x * g)
      = ct (ProbabilityTheory.cond (adelicAddHaar (𝓞 F) F) (AdelicBox.adelicBox F)) w g :=
  constantTerm_adelicBox_unipotentGL2_mul F (fun k h => hw (unipotentGL2 k) h) x g

private theorem ct_globalPoints_mul {w : AdelicGL2 (𝓞 F) F → ℂ}
    (hw : ∀ (γ : GL (Fin 2) F) (g : AdelicGL2 (𝓞 F) F), w (globalPoints (𝓞 F) F γ * g) = w g)
    {γ : GL (Fin 2) F} (hγ : γ ∈ borelSubgroup F) (g : AdelicGL2 (𝓞 F) F) :
    ct (ProbabilityTheory.cond (adelicAddHaar (𝓞 F) F) (AdelicBox.adelicBox F)) w (globalPoints (𝓞 F) F γ * g)
      = ct (ProbabilityTheory.cond (adelicAddHaar (𝓞 F) F) (AdelicBox.adelicBox F)) w g :=
  constantTerm_adelicBox_globalPoints_mul_of_mem_borelSubgroup F (fun γ' _ h => hw γ' h) hγ g

private def cutSet (ν : Measure (AdeleRing (𝓞 F) F)) (w : AdelicGL2 (𝓞 F) F → ℂ) (d₁ d₂ a b R : ℝ) :
    Set (AdelicGL2 (𝓞 F) F) :=
  {g | ideleNorm F (Matrix.GeneralLinearGroup.det g) ∈ Set.Icc d₁ (4 * d₂) ∧ adelicHeight F g ∈ Set.Icc a b ∧
    ‖ct ν w g‖ ≤ R}

private def kernel (ν : Measure (AdeleRing (𝓞 F) F)) (w : AdelicGL2 (𝓞 F) F → ℂ) (d₁ d₂ a b R : ℝ) :
    AdelicGL2 (𝓞 F) F → ℂ :=
  (cutSet ν w d₁ d₂ a b R).indicator (ct ν w)

private theorem measurableSet_cutSet (ν : Measure (AdeleRing (𝓞 F) F)) {w : AdelicGL2 (𝓞 F) F → ℂ}
    (hct : Measurable (ct ν w)) (d₁ d₂ a b R : ℝ) : MeasurableSet (cutSet ν w d₁ d₂ a b R) := by
  refine ((measurable_det_norm F) measurableSet_Icc).inter
    (((measurable_adelicHeight F) measurableSet_Icc).inter ?_)
  exact measurableSet_le hct.norm measurable_const

private theorem measurable_kernel (ν : Measure (AdeleRing (𝓞 F) F)) {w : AdelicGL2 (𝓞 F) F → ℂ}
    (hct : Measurable (ct ν w)) (d₁ d₂ a b R : ℝ) : Measurable (kernel ν w d₁ d₂ a b R) :=
  hct.indicator (measurableSet_cutSet ν hct d₁ d₂ a b R)

private theorem norm_kernel_le (ν : Measure (AdeleRing (𝓞 F) F)) (w : AdelicGL2 (𝓞 F) F → ℂ) {d₁ d₂ a b R : ℝ}
    (hR : 0 ≤ R) (g : AdelicGL2 (𝓞 F) F) : ‖kernel ν w d₁ d₂ a b R g‖ ≤ R := by
  unfold kernel
  by_cases hg : g ∈ cutSet ν w d₁ d₂ a b R
  · rw [Set.indicator_of_mem hg]
    exact hg.2.2
  · rw [Set.indicator_of_notMem hg, norm_zero]
    exact hR

private theorem kernel_eq_zero_of_det (ν : Measure (AdeleRing (𝓞 F) F)) (w : AdelicGL2 (𝓞 F) F → ℂ) (d₁ d₂ a b R : ℝ)
    {g : AdelicGL2 (𝓞 F) F} (hg : ideleNorm F (Matrix.GeneralLinearGroup.det g) ∉ Set.Icc d₁ (4 * d₂)) :
    kernel ν w d₁ d₂ a b R g = 0 :=
  Set.indicator_of_notMem (fun h => hg h.1) _

private theorem kernel_eq_zero_of_height (ν : Measure (AdeleRing (𝓞 F) F)) (w : AdelicGL2 (𝓞 F) F → ℂ)
    (d₁ d₂ a b R : ℝ) {g : AdelicGL2 (𝓞 F) F} (hg : adelicHeight F g ∉ Set.Icc a b) : kernel ν w d₁ d₂ a b R g = 0 :=
  Set.indicator_of_notMem (fun h => hg h.2.1) _

private theorem kernel_mul_of (ν : Measure (AdeleRing (𝓞 F) F)) (w : AdelicGL2 (𝓞 F) F → ℂ) (d₁ d₂ a b R : ℝ)
    {h g : AdelicGL2 (𝓞 F) F} (hct : ct ν w (h * g) = ct ν w g)
    (hdet : ideleNorm F (Matrix.GeneralLinearGroup.det (h * g)) = ideleNorm F (Matrix.GeneralLinearGroup.det g))
    (hht : adelicHeight F (h * g) = adelicHeight F g) :
    kernel ν w d₁ d₂ a b R (h * g) = kernel ν w d₁ d₂ a b R g := by
  have hmem : h * g ∈ cutSet ν w d₁ d₂ a b R ↔ g ∈ cutSet ν w d₁ d₂ a b R := by
    simp only [cutSet, Set.mem_setOf_eq, hct, hdet, hht]
  unfold kernel
  by_cases hg : g ∈ cutSet ν w d₁ d₂ a b R
  · rw [Set.indicator_of_mem (hmem.mpr hg), Set.indicator_of_mem hg, hct]
  · rw [Set.indicator_of_notMem (fun h' => hg (hmem.mp h')), Set.indicator_of_notMem hg]

private theorem det_unipotentGL2 (x : AdeleRing (𝓞 F) F) :
    Matrix.GeneralLinearGroup.det (unipotentGL2 x : AdelicGL2 (𝓞 F) F) = 1 := by
  ext
  simp [Matrix.det_fin_two]

private theorem kernel_unipotentGL2_mul {w : AdelicGL2 (𝓞 F) F → ℂ}
    (hw : ∀ (γ : GL (Fin 2) F) (g : AdelicGL2 (𝓞 F) F), w (globalPoints (𝓞 F) F γ * g) = w g) (d₁ d₂ a b R : ℝ)
    (x : AdeleRing (𝓞 F) F) (g : AdelicGL2 (𝓞 F) F) :
    kernel (ProbabilityTheory.cond (adelicAddHaar (𝓞 F) F) (AdelicBox.adelicBox F)) w d₁ d₂ a b R (unipotentGL2 x * g)
      = kernel (ProbabilityTheory.cond (adelicAddHaar (𝓞 F) F) (AdelicBox.adelicBox F)) w d₁ d₂ a b R g := by
  refine kernel_mul_of _ w d₁ d₂ a b R (ct_unipotentGL2_mul hw x g) ?_ (adelicHeight_unipotentGL2_mul F x g)
  rw [map_mul, det_unipotentGL2, one_mul]

private theorem kernel_globalPoints_mul {w : AdelicGL2 (𝓞 F) F → ℂ}
    (hw : ∀ (γ : GL (Fin 2) F) (g : AdelicGL2 (𝓞 F) F), w (globalPoints (𝓞 F) F γ * g) = w g) (d₁ d₂ a b R : ℝ)
    {γ : GL (Fin 2) F} (hγ : γ ∈ borelSubgroup F) (g : AdelicGL2 (𝓞 F) F) :
    kernel (ProbabilityTheory.cond (adelicAddHaar (𝓞 F) F) (AdelicBox.adelicBox F)) w d₁ d₂ a b R
        (globalPoints (𝓞 F) F γ * g)
      = kernel (ProbabilityTheory.cond (adelicAddHaar (𝓞 F) F) (AdelicBox.adelicBox F)) w d₁ d₂ a b R g := by
  refine kernel_mul_of _ w d₁ d₂ a b R (ct_globalPoints_mul hw hγ g) ?_
    (adelicHeight_globalPoints_mul_of_apply_one_zero_eq_zero F γ hγ g)
  rw [map_mul, ideleNorm_mul, ideleNorm_det_globalPoints, one_mul]

private theorem kernel_centralScalar_mul_of_mem_principalIdeles {w : AdelicGL2 (𝓞 F) F → ℂ}
    (hw : ∀ (γ : GL (Fin 2) F) (g : AdelicGL2 (𝓞 F) F), w (globalPoints (𝓞 F) F γ * g) = w g) (d₁ d₂ a b R : ℝ)
    {γ : (AdeleRing (𝓞 F) F)ˣ} (hγ : γ ∈ M4aHerbrand.principalIdeles (𝓞 F) F) (g : AdelicGL2 (𝓞 F) F) :
    kernel (ProbabilityTheory.cond (adelicAddHaar (𝓞 F) F) (AdelicBox.adelicBox F)) w d₁ d₂ a b R
        (centralScalar (𝓞 F) F γ * g)
      = kernel (ProbabilityTheory.cond (adelicAddHaar (𝓞 F) F) (AdelicBox.adelicBox F)) w d₁ d₂ a b R g := by
  obtain ⟨η, hη⟩ := exists_centralScalar_eq_globalPoints_scalar F hγ
  rw [hη]
  exact kernel_globalPoints_mul hw d₁ d₂ a b R (scalar_mem_borelSubgroup F η) g

private def average (ξ : (⊤ : Subgroup (AdeleRing (𝓞 F) F)ˣ) →* ℂˣ) (D : Set (AdeleRing (𝓞 F) F)ˣ)
    (ν : Measure (AdeleRing (𝓞 F) F)) (w : AdelicGL2 (𝓞 F) F → ℂ) (d₁ d₂ a b R : ℝ) (g : AdelicGL2 (𝓞 F) F) : ℂ :=
  ∫ z in D, (xi ξ z)⁻¹ * kernel ν w d₁ d₂ a b R (centralScalar (𝓞 F) F z * g) ∂(NumberField.Idele.idelicHaar F)

private theorem secondCountableTopology_units_adeleRing' : SecondCountableTopology (AdeleRing (𝓞 F) F)ˣ := by
  haveI := NumberField.AdeleRing.secondCountableTopology F
  haveI : SecondCountableTopology (AdeleRing (𝓞 F) F)ᵐᵒᵖ :=
    MulOpposite.opHomeomorph.symm.isEmbedding.secondCountableTopology
  exact Units.isEmbedding_embedProduct.secondCountableTopology

private theorem sigmaFinite_idelicHaar' : SigmaFinite (NumberField.Idele.idelicHaar F) := by
  haveI := secondCountableTopology_units_adeleRing' (F := F)
  haveI := NumberField.Idele.isHaarMeasure_idelicHaar F
  infer_instance

private theorem measurable_average {ξ : (⊤ : Subgroup (AdeleRing (𝓞 F) F)ˣ) →* ℂˣ} (hξ : Continuous ξ)
    (D : Set (AdeleRing (𝓞 F) F)ˣ) (ν : Measure (AdeleRing (𝓞 F) F)) {w : AdelicGL2 (𝓞 F) F → ℂ}
    (hct : Measurable (ct ν w)) (d₁ d₂ a b R : ℝ) : Measurable (average ξ D ν w d₁ d₂ a b R) := by
  haveI := secondCountable_adelicGL2 F
  haveI : SigmaFinite (NumberField.Idele.idelicHaar F) := sigmaFinite_idelicHaar'
  have hshear : Continuous fun p : AdelicGL2 (𝓞 F) F × (AdeleRing (𝓞 F) F)ˣ => centralScalar (𝓞 F) F p.2 * p.1 :=
    ((continuous_centralScalar F).comp continuous_snd).mul continuous_fst
  have hjoint : Measurable fun p : AdelicGL2 (𝓞 F) F × (AdeleRing (𝓞 F) F)ˣ =>
      (xi ξ p.2)⁻¹ * kernel ν w d₁ d₂ a b R (centralScalar (𝓞 F) F p.2 * p.1) :=
    ((measurable_xi hξ).comp measurable_snd).inv.mul ((measurable_kernel ν hct d₁ d₂ a b R).comp hshear.measurable)
  show Measurable fun g : AdelicGL2 (𝓞 F) F =>
    ∫ z in D, (xi ξ z)⁻¹ * kernel ν w d₁ d₂ a b R (centralScalar (𝓞 F) F z * g) ∂(NumberField.Idele.idelicHaar F)
  exact (hjoint.stronglyMeasurable.integral_prod_right').measurable

private theorem average_mul_of (ξ : (⊤ : Subgroup (AdeleRing (𝓞 F) F)ˣ) →* ℂˣ) (D : Set (AdeleRing (𝓞 F) F)ˣ)
    (ν : Measure (AdeleRing (𝓞 F) F)) (w : AdelicGL2 (𝓞 F) F → ℂ) (d₁ d₂ a b R : ℝ) {h : AdelicGL2 (𝓞 F) F}
    (hk : ∀ x : AdelicGL2 (𝓞 F) F, kernel ν w d₁ d₂ a b R (h * x) = kernel ν w d₁ d₂ a b R x) (g : AdelicGL2 (𝓞 F) F) :
    average ξ D ν w d₁ d₂ a b R (h * g) = average ξ D ν w d₁ d₂ a b R g := by
  unfold average
  refine integral_congr_ae (Filter.Eventually.of_forall fun z => ?_)
  show (xi ξ z)⁻¹ * kernel ν w d₁ d₂ a b R (centralScalar (𝓞 F) F z * (h * g))
    = (xi ξ z)⁻¹ * kernel ν w d₁ d₂ a b R (centralScalar (𝓞 F) F z * g)
  rw [← mul_assoc, ← mul_centralScalar_comm' F z h, mul_assoc, hk]

private theorem average_unipotentGL2_mul (ξ : (⊤ : Subgroup (AdeleRing (𝓞 F) F)ˣ) →* ℂˣ) (D : Set (AdeleRing (𝓞 F) F)ˣ)
    {w : AdelicGL2 (𝓞 F) F → ℂ}
    (hw : ∀ (γ : GL (Fin 2) F) (g : AdelicGL2 (𝓞 F) F), w (globalPoints (𝓞 F) F γ * g) = w g) (d₁ d₂ a b R : ℝ)
    (x : AdeleRing (𝓞 F) F) (g : AdelicGL2 (𝓞 F) F) :
    average ξ D (ProbabilityTheory.cond (adelicAddHaar (𝓞 F) F) (AdelicBox.adelicBox F)) w d₁ d₂ a b R
        (unipotentGL2 x * g)
      = average ξ D (ProbabilityTheory.cond (adelicAddHaar (𝓞 F) F) (AdelicBox.adelicBox F)) w d₁ d₂ a b R g :=
  average_mul_of ξ D _ w d₁ d₂ a b R (kernel_unipotentGL2_mul hw d₁ d₂ a b R x) g

private theorem average_globalPoints_mul (ξ : (⊤ : Subgroup (AdeleRing (𝓞 F) F)ˣ) →* ℂˣ) (D : Set (AdeleRing (𝓞 F) F)ˣ)
    {w : AdelicGL2 (𝓞 F) F → ℂ}
    (hw : ∀ (γ : GL (Fin 2) F) (g : AdelicGL2 (𝓞 F) F), w (globalPoints (𝓞 F) F γ * g) = w g) (d₁ d₂ a b R : ℝ)
    {γ : GL (Fin 2) F} (hγ : γ ∈ borelSubgroup F) (g : AdelicGL2 (𝓞 F) F) :
    average ξ D (ProbabilityTheory.cond (adelicAddHaar (𝓞 F) F) (AdelicBox.adelicBox F)) w d₁ d₂ a b R
        (globalPoints (𝓞 F) F γ * g)
      = average ξ D (ProbabilityTheory.cond (adelicAddHaar (𝓞 F) F) (AdelicBox.adelicBox F)) w d₁ d₂ a b R g :=
  average_mul_of ξ D _ w d₁ d₂ a b R (kernel_globalPoints_mul hw d₁ d₂ a b R hγ) g

private theorem average_eq_zero_of_height (ξ : (⊤ : Subgroup (AdeleRing (𝓞 F) F)ˣ) →* ℂˣ)
    (D : Set (AdeleRing (𝓞 F) F)ˣ)
    (ν : Measure (AdeleRing (𝓞 F) F)) (w : AdelicGL2 (𝓞 F) F → ℂ) (d₁ d₂ a b R : ℝ) {g : AdelicGL2 (𝓞 F) F}
    (hg : adelicHeight F g ∉ Set.Icc a b) : average ξ D ν w d₁ d₂ a b R g = 0 := by
  unfold average
  refine setIntegral_eq_zero_of_forall_eq_zero fun z _ => ?_
  rw [kernel_eq_zero_of_height ν w d₁ d₂ a b R (by rwa [adelicHeight_centralScalar_mul]), mul_zero]

private scoped instance instSMulCommClassPrincipalIdeles :
    SMulCommClass (AdeleRing (𝓞 F) F)ˣ (M4aHerbrand.principalIdeles (𝓞 F) F) (AdeleRing (𝓞 F) F)ˣ :=
  ⟨fun a γ x =>
    show a * ((γ : (AdeleRing (𝓞 F) F)ˣ) * x) = (γ : (AdeleRing (𝓞 F) F)ˣ) * (a * x) from mul_left_comm _ _ _⟩

private theorem countable_numberField : Countable F :=
  (Module.finBasis ℚ F).equivFun.injective.countable

private theorem countable_principalIdeles : Countable (M4aHerbrand.principalIdeles (𝓞 F) F) := by
  haveI : Countable F := countable_numberField
  haveI : Countable Fˣ := Units.val_injective.countable
  show Countable (Units.map (algebraMap F (AdeleRing (𝓞 F) F) : F →* AdeleRing (𝓞 F) F)).range
  exact (MonoidHom.rangeRestrict_surjective _).countable

private theorem integrand_smul {ξ : (⊤ : Subgroup (AdeleRing (𝓞 F) F)ˣ) →* ℂˣ}
    (hξF : ∀ γ ∈ M4aHerbrand.principalIdeles (𝓞 F) F, xi ξ γ = 1) {w : AdelicGL2 (𝓞 F) F → ℂ}
    (hw : ∀ (γ : GL (Fin 2) F) (g : AdelicGL2 (𝓞 F) F), w (globalPoints (𝓞 F) F γ * g) = w g) (d₁ d₂ a b R : ℝ)
    (g : AdelicGL2 (𝓞 F) F) (γ : M4aHerbrand.principalIdeles (𝓞 F) F) (z : (AdeleRing (𝓞 F) F)ˣ) :
    (xi ξ (γ • z))⁻¹ * kernel (ProbabilityTheory.cond (adelicAddHaar (𝓞 F) F) (AdelicBox.adelicBox F)) w d₁ d₂ a b R
        (centralScalar (𝓞 F) F (γ • z) * g)
      = (xi ξ z)⁻¹ * kernel (ProbabilityTheory.cond (adelicAddHaar (𝓞 F) F) (AdelicBox.adelicBox F)) w d₁ d₂ a b R
        (centralScalar (𝓞 F) F z * g) := by
  rw [Subgroup.smul_def, smul_eq_mul, xi_mul, hξF γ γ.2, one_mul, map_mul, mul_assoc,
    kernel_centralScalar_mul_of_mem_principalIdeles hw d₁ d₂ a b R γ.2]

private theorem average_centralScalar_mul {ξ : (⊤ : Subgroup (AdeleRing (𝓞 F) F)ˣ) →* ℂˣ}
    (hξF : ∀ γ ∈ M4aHerbrand.principalIdeles (𝓞 F) F, xi ξ γ = 1) {D : Set (AdeleRing (𝓞 F) F)ˣ}
    (hD : IsFundamentalDomain (M4aHerbrand.principalIdeles (𝓞 F) F) D (NumberField.Idele.idelicHaar F))
    {w : AdelicGL2 (𝓞 F) F → ℂ}
    (hw : ∀ (γ : GL (Fin 2) F) (g : AdelicGL2 (𝓞 F) F), w (globalPoints (𝓞 F) F γ * g) = w g) (d₁ d₂ a b R : ℝ)
    (z₀ : (AdeleRing (𝓞 F) F)ˣ) (g : AdelicGL2 (𝓞 F) F) :
    average ξ D (ProbabilityTheory.cond (adelicAddHaar (𝓞 F) F) (AdelicBox.adelicBox F)) w d₁ d₂ a b R
        (centralScalar (𝓞 F) F z₀ * g)
      = xi ξ z₀ *
        average ξ D (ProbabilityTheory.cond (adelicAddHaar (𝓞 F) F) (AdelicBox.adelicBox F)) w d₁ d₂ a b R g := by
  set ν := ProbabilityTheory.cond (adelicAddHaar (𝓞 F) F) (AdelicBox.adelicBox F) with hν
  set Φ : (AdeleRing (𝓞 F) F)ˣ → ℂ := fun y => (xi ξ y)⁻¹ * kernel ν w d₁ d₂ a b R (centralScalar (𝓞 F) F y * g)
    with hΦ
  have hscalar : ∀ z : (AdeleRing (𝓞 F) F)ˣ, xi ξ z₀ * (xi ξ z * xi ξ z₀)⁻¹ = (xi ξ z)⁻¹ := by
    intro z
    rw [mul_inv, mul_comm (xi ξ z)⁻¹, ← mul_assoc, mul_inv_cancel₀ (xi_ne_zero ξ z₀), one_mul]
  have h1 : ∀ z : (AdeleRing (𝓞 F) F)ˣ,
      (xi ξ z)⁻¹ * kernel ν w d₁ d₂ a b R (centralScalar (𝓞 F) F z * (centralScalar (𝓞 F) F z₀ * g))
        = xi ξ z₀ * Φ (z * z₀) := by
    intro z
    simp only [hΦ, xi_mul, map_mul, mul_assoc]
    generalize kernel ν w d₁ d₂ a b R (centralScalar (𝓞 F) F z * (centralScalar (𝓞 F) F z₀ * g)) = K
    rw [← mul_assoc, hscalar]
  have h2 : ∫ z in D, Φ (z * z₀) ∂(NumberField.Idele.idelicHaar F)
      = ∫ y in z₀ • D, Φ y ∂(NumberField.Idele.idelicHaar F) := by
    have hpre : (fun z : (AdeleRing (𝓞 F) F)ˣ => z * z₀) ⁻¹' (z₀ • D) = D := by
      ext z
      simp only [Set.mem_preimage, Set.mem_smul_set_iff_inv_smul_mem, smul_eq_mul]
      rw [mul_comm z, inv_mul_cancel_left]
    have h := (measurePreserving_mul_right (NumberField.Idele.idelicHaar F) z₀).setIntegral_preimage_emb
      (measurableEmbedding_mulRight z₀) Φ (z₀ • D)
    rw [hpre] at h
    exact h
  haveI : Countable (M4aHerbrand.principalIdeles (𝓞 F) F) := countable_principalIdeles
  have h3 : ∫ y in z₀ • D, Φ y ∂(NumberField.Idele.idelicHaar F) = ∫ y in D, Φ y ∂(NumberField.Idele.idelicHaar F) :=
    (hD.smul_of_comm z₀).setIntegral_eq hD fun γ y => integrand_smul hξF hw d₁ d₂ a b R g γ y
  calc average ξ D ν w d₁ d₂ a b R (centralScalar (𝓞 F) F z₀ * g)
      = ∫ z in D, xi ξ z₀ * Φ (z * z₀) ∂(NumberField.Idele.idelicHaar F) :=
        integral_congr_ae (Filter.Eventually.of_forall fun z => h1 z)
    _ = xi ξ z₀ * ∫ z in D, Φ (z * z₀) ∂(NumberField.Idele.idelicHaar F) := integral_const_mul _ _
    _ = xi ξ z₀ * ∫ y in D, Φ y ∂(NumberField.Idele.idelicHaar F) := by rw [h2, h3]
    _ = xi ξ z₀ * average ξ D ν w d₁ d₂ a b R g := rfl

section Shear

variable {G Y : Type*} [Group G] [MeasurableSpace G] [MeasurableSpace Y]

private theorem quasiMeasurePreserving_shear [MeasurableMul G] (μ ρ : Measure G) [μ.IsMulLeftInvariant] [SFinite ρ]
    (hρ : ρ ≤ μ) (ν : Measure Y) [SFinite ν] {c : Y → G} (hc : Measurable fun p : G × Y => c p.2 * p.1) :
    Measure.QuasiMeasurePreserving (fun p : G × Y => c p.2 * p.1) (ρ.prod ν) μ := by
  refine ⟨hc, Measure.AbsolutelyContinuous.mk fun N hN hN0 => ?_⟩
  have hsec : ∀ y : Y, ρ ((fun g : G => (g, y)) ⁻¹' ((fun p : G × Y => c p.2 * p.1) ⁻¹' N)) = 0 := by
    intro y
    refine nonpos_iff_eq_zero.mp ?_
    calc ρ ((fun g : G => (g, y)) ⁻¹' ((fun p : G × Y => c p.2 * p.1) ⁻¹' N))
        ≤ μ ((fun g : G => c y * g) ⁻¹' N) := Measure.le_iff'.mp hρ _
      _ = μ N := (measurePreserving_mul_left μ (c y)).measure_preimage hN.nullMeasurableSet
      _ = 0 := hN0
  calc (ρ.prod ν).map (fun p : G × Y => c p.2 * p.1) N
      = ρ.prod ν ((fun p : G × Y => c p.2 * p.1) ⁻¹' N) := Measure.map_apply hc hN
    _ = ∫⁻ y, ρ ((fun g : G => (g, y)) ⁻¹' ((fun p : G × Y => c p.2 * p.1) ⁻¹' N)) ∂ν :=
        Measure.prod_apply_symm (hc hN)
    _ = 0 := by simp only [hsec, lintegral_zero]

private theorem ae_ae_shear [MeasurableMul G] (μ ρ : Measure G) [μ.IsMulLeftInvariant] [SFinite ρ] (hρ : ρ ≤ μ)
    (ν : Measure Y) [SFinite ν] {c : Y → G} (hc : Measurable fun p : G × Y => c p.2 * p.1) {v v' : G → ℂ}
    (hv : v =ᵐ[μ] v') :
    ∀ᵐ g ∂ρ, ∀ᵐ y ∂ν, v (c y * g) = v' (c y * g) ∧ v g = v' g := by
  have h1 : ∀ᵐ p ∂ρ.prod ν, v (c p.2 * p.1) = v' (c p.2 * p.1) :=
    (quasiMeasurePreserving_shear μ ρ hρ ν hc).ae hv
  have h2 : ∀ᵐ p ∂ρ.prod ν, v p.1 = v' p.1 :=
    Measure.quasiMeasurePreserving_fst.ae ((Measure.absolutelyContinuous_of_le hρ).ae_eq hv)
  exact Measure.ae_ae_of_ae_prod (h1.and h2)

end Shear
p2m_reactivate "P2MW.S_AutomorphicForm_exists_isSlabProfile_eLpNorm_sub_pseudoEisenstein_lt_of_forall_setIntegral_eq_zero_slab.SlabPairingDescent"

private theorem measurable_unipotent_shear :
    Measurable fun p : AdelicGL2 (𝓞 F) F × AdeleRing (𝓞 F) F => unipotentGL2 p.2 * p.1 := by
  haveI := secondCountable_adelicGL2 F
  exact ((continuous_unipotentGL2.comp continuous_snd).mul continuous_fst).measurable

private theorem measurable_central_shear :
    Measurable fun p : AdelicGL2 (𝓞 F) F × (AdeleRing (𝓞 F) F)ˣ => centralScalar (𝓞 F) F p.2 * p.1 := by
  haveI := secondCountable_adelicGL2 F
  exact (((continuous_centralScalar F).comp continuous_snd).mul continuous_fst).measurable

private theorem sigmaFinite_adelicGLHaar : SigmaFinite (adelicGLHaar (Fin 2) (𝓞 F) F) := by
  haveI := secondCountable_adelicGL2 F
  infer_instance

private theorem ct_congr_ae {w u : AdelicGL2 (𝓞 F) F → ℂ} (hwu : w =ᵐ[adelicGLHaar (Fin 2) (𝓞 F) F] u) :
    ct (ProbabilityTheory.cond (adelicAddHaar (𝓞 F) F) (AdelicBox.adelicBox F)) w
      =ᵐ[adelicGLHaar (Fin 2) (𝓞 F) F]
        ct (ProbabilityTheory.cond (adelicAddHaar (𝓞 F) F) (AdelicBox.adelicBox F)) u := by
  haveI := sigmaFinite_adelicGLHaar (F := F)
  haveI : IsProbabilityMeasure (ProbabilityTheory.cond (adelicAddHaar (𝓞 F) F) (AdelicBox.adelicBox F)) :=
    NumberField.AdelicBox.isProbabilityMeasure_cond_adelicBox F
  have h := ae_ae_shear (adelicGLHaar (Fin 2) (𝓞 F) F) (adelicGLHaar (Fin 2) (𝓞 F) F) le_rfl
    (ProbabilityTheory.cond (adelicAddHaar (𝓞 F) F) (AdelicBox.adelicBox F)) measurable_unipotent_shear hwu
  filter_upwards [h] with g hg
  rw [ct_apply, ct_apply]
  exact integral_congr_ae (hg.mono fun x hx => hx.1)

private theorem ae_ae_ct_centralScalar_mul {ξ : (⊤ : Subgroup (AdeleRing (𝓞 F) F)ˣ) →* ℂˣ} {u : AdelicGL2 (𝓞 F) F → ℂ}
    (hu : IsLsXiFunction (𝓞 F) F ⊤ ξ u) {w : AdelicGL2 (𝓞 F) F → ℂ} (hwu : w =ᵐ[adelicGLHaar (Fin 2) (𝓞 F) F] u)
    (ρ : Measure (AdelicGL2 (𝓞 F) F)) [SFinite ρ] (hρ : ρ ≤ adelicGLHaar (Fin 2) (𝓞 F) F)
    (ν : Measure (AdeleRing (𝓞 F) F)ˣ) [SFinite ν] :
    ∀ᵐ g ∂ρ, ∀ᵐ z ∂ν,
      ct (ProbabilityTheory.cond (adelicAddHaar (𝓞 F) F) (AdelicBox.adelicBox F)) w (centralScalar (𝓞 F) F z * g)
        = xi ξ z * ct (ProbabilityTheory.cond (adelicAddHaar (𝓞 F) F) (AdelicBox.adelicBox F)) w g := by
  have hexact : ∀ (z : (AdeleRing (𝓞 F) F)ˣ) (g : AdelicGL2 (𝓞 F) F),
      ct (ProbabilityTheory.cond (adelicAddHaar (𝓞 F) F) (AdelicBox.adelicBox F)) u (centralScalar (𝓞 F) F z * g)
        = xi ξ z * ct (ProbabilityTheory.cond (adelicAddHaar (𝓞 F) F) (AdelicBox.adelicBox F)) u g :=
    fun z g => ct_centralScalar_mul_of_forall _ (fun g' => hu.central_transform ⟨z, Subgroup.mem_top z⟩ g') g
  have h := ae_ae_shear (adelicGLHaar (Fin 2) (𝓞 F) F) ρ hρ ν measurable_central_shear (ct_congr_ae hwu)
  filter_upwards [h] with g hg
  filter_upwards [hg] with z hz
  rw [hz.1, hexact, hz.2]

private theorem map_mem_principalIdeles (η : Fˣ) :
    Units.map (algebraMap F (AdeleRing (𝓞 F) F)).toMonoidHom η ∈ M4aHerbrand.principalIdeles (𝓞 F) F :=
  ⟨η, rfl⟩

private theorem isCompact_section_image (s : ℝ≥0ˣ →* (AdeleRing (𝓞 F) F)ˣ) (hs : Continuous s) {α β : ℝ} (hα : 0 < α) :
    IsCompact (s '' {r : ℝ≥0ˣ | ((r : ℝ≥0) : ℝ) ∈ Set.Icc α β}) := by
  refine IsCompact.image ?_ hs
  rw [Units.isEmbedding_val₀.isCompact_iff]
  have himage : (Units.val '' {r : ℝ≥0ˣ | ((r : ℝ≥0) : ℝ) ∈ Set.Icc α β}) = {x : ℝ≥0 | (x : ℝ) ∈ Set.Icc α β} := by
    ext x
    constructor
    · rintro ⟨r, hr, rfl⟩
      exact hr
    · intro hx
      have hx0 : x ≠ 0 := by
        rintro rfl
        exact absurd hx.1 (by simpa using hα)
      exact ⟨Units.mk0 x hx0, hx, rfl⟩
  rw [himage]
  have hclosed : IsClosed {x : ℝ≥0 | (x : ℝ) ∈ Set.Icc α β} := isClosed_Icc.preimage NNReal.continuous_coe
  refine (isCompact_Icc (a := (0 : ℝ≥0)) (b := ⟨max β 0, le_max_right β 0⟩)).of_isClosed_subset hclosed ?_
  intro x hx
  exact ⟨zero_le, NNReal.coe_le_coe.mp (hx.2.trans (le_max_left β 0))⟩

private theorem exists_forall_norm_xi_le {ξ : (⊤ : Subgroup (AdeleRing (𝓞 F) F)ˣ) →* ℂˣ} (hξ : Continuous ξ)
    (hξF : ∀ γ ∈ M4aHerbrand.principalIdeles (𝓞 F) F, xi ξ γ = 1) {α β : ℝ} (hα : 0 < α) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ z : (AdeleRing (𝓞 F) F)ˣ, ideleNorm F z ∈ Set.Icc α β →
      ‖xi ξ z‖ ≤ M ∧ ‖(xi ξ z)⁻¹‖ ≤ M := by
  obtain ⟨K, hK, -, hKdec⟩ := exists_isCompact_subset_normOneIdeles_forall_mem_exists_eq_map_algebraMap_mul F
  obtain ⟨s, hs, hsnorm, -⟩ := exists_continuous_monoidHom_ideleNorm_apply_eq F
  have hS := isCompact_section_image s hs (β := β) hα
  have hcont₁ : Continuous fun z => ‖xi ξ z‖ := (continuous_xi hξ).norm
  have hcont₂ : Continuous fun z => ‖(xi ξ z)⁻¹‖ := ((continuous_xi hξ).inv₀ (xi_ne_zero ξ)).norm
  obtain ⟨C₁, hC₁⟩ := hK.exists_bound_of_continuousOn hcont₁.continuousOn
  obtain ⟨C₂, hC₂⟩ := hK.exists_bound_of_continuousOn hcont₂.continuousOn
  obtain ⟨C₃, hC₃⟩ := hS.exists_bound_of_continuousOn hcont₁.continuousOn
  obtain ⟨C₄, hC₄⟩ := hS.exists_bound_of_continuousOn hcont₂.continuousOn
  refine ⟨max (max C₁ 0 * max C₃ 0) (max C₂ 0 * max C₄ 0),
    le_max_of_le_left (mul_nonneg (le_max_right _ _) (le_max_right _ _)), fun z hz => ?_⟩
  have hzpos : 0 < ideleNorm F z := ideleNorm_pos z
  set r : ℝ≥0ˣ := Units.mk0 ⟨ideleNorm F z, hzpos.le⟩ (by
    intro h
    have := congrArg (fun x : ℝ≥0 => (x : ℝ)) h
    simp only [NNReal.coe_zero] at this
    exact hzpos.ne' this) with hr
  have hrcoe : ((r : ℝ≥0) : ℝ) = ideleNorm F z := by rw [hr]; rfl
  have hsr : s r ∈ s '' {r : ℝ≥0ˣ | ((r : ℝ≥0) : ℝ) ∈ Set.Icc α β} :=
    ⟨r, by rw [Set.mem_setOf_eq, hrcoe]; exact hz, rfl⟩
  have hnorm : z * s r⁻¹ ∈ normOneIdeles F := by
    rw [mem_normOneIdeles_iff, ideleNorm_mul, hsnorm, Units.val_inv_eq_inv_val, NNReal.coe_inv, hrcoe,
      mul_inv_cancel₀ hzpos.ne']
  obtain ⟨η, κ, hκ, hdec⟩ := hKdec _ hnorm
  have hz' : z = Units.map (algebraMap F (AdeleRing (𝓞 F) F)).toMonoidHom η * κ * s r := by
    rw [← hdec, mul_assoc, ← map_mul, inv_mul_cancel, map_one, mul_one]
  have hxi : xi ξ z = xi ξ κ * xi ξ (s r) := by
    rw [hz', xi_mul, xi_mul, hξF _ (map_mem_principalIdeles η), one_mul]
  obtain ⟨h₁, h₂⟩ := And.intro (hC₁ κ hκ) (hC₃ _ hsr)
  obtain ⟨h₃, h₄⟩ := And.intro (hC₂ κ hκ) (hC₄ _ hsr)
  simp only [norm_norm] at h₁ h₂ h₃ h₄
  constructor
  · refine le_max_of_le_left ?_
    rw [hxi, norm_mul]
    exact mul_le_mul (h₁.trans (le_max_left _ _)) (h₂.trans (le_max_left _ _)) (norm_nonneg _) (le_max_right _ _)
  · refine le_max_of_le_right ?_
    rw [hxi, mul_inv, norm_mul]
    exact mul_le_mul (h₃.trans (le_max_left _ _)) (h₄.trans (le_max_left _ _)) (norm_nonneg _) (le_max_right _ _)

private theorem mem_window_of_mul_self_mul_mem {d₁ d₂ e₁ e₂ t m : ℝ} (_hd₁ : 0 < d₁) (he₁ : 0 < e₁) (ht : 0 < t)
    (hz : t * t * m ∈ Set.Icc d₁ (4 * d₂)) (hm : m ∈ Set.Icc e₁ e₂) :
    t ∈ Set.Icc (min (d₁ / e₂) 1) (max (4 * d₂ / e₁) 1 + 1) := by
  have he₂ : 0 < e₂ := he₁.trans_le (hm.1.trans hm.2)
  constructor
  · rcases le_or_gt 1 t with h1 | h1
    · exact (min_le_right _ _).trans h1
    · refine (min_le_left _ _).trans ?_
      rw [div_le_iff₀ he₂]
      nlinarith [hz.1, mul_nonneg (mul_nonneg ht.le ht.le) (sub_nonneg.2 hm.2),
        mul_pos (mul_pos ht (sub_pos.2 h1)) he₂]
  · rcases le_or_gt t 1 with h1 | h1
    · exact h1.trans (by linarith [le_max_right (4 * d₂ / e₁) 1])
    · refine ((le_max_left _ _).trans (by linarith : max (4 * d₂ / e₁) 1 ≤ max (4 * d₂ / e₁) 1 + 1)).trans' ?_
      rw [le_div_iff₀ he₁]
      nlinarith [hz.2, mul_nonneg (mul_nonneg ht.le ht.le) (sub_nonneg.2 hm.1),
        mul_nonneg (mul_nonneg ht.le (sub_nonneg.2 h1.le)) he₁.le]

private def window (d₁ d₂ e₁ e₂ : ℝ) : Set (AdeleRing (𝓞 F) F)ˣ :=
  {z | ideleNorm F z ∈ Set.Icc (min (d₁ / e₂) 1) (max (4 * d₂ / e₁) 1 + 1)}

private theorem measurable_ideleNorm' : Measurable (ideleNorm F) :=
  (continuous_ideleNorm F).measurable

private theorem window_volume_lt_top {D : Set (AdeleRing (𝓞 F) F)ˣ} (hD : MeasurableSet D)
    (hDF : IsFundamentalDomain (M4aHerbrand.principalIdeles (𝓞 F) F) D (NumberField.Idele.idelicHaar F))
    {d₁ d₂ e₁ e₂ : ℝ} (hd₁ : 0 < d₁) (he₂ : 0 < e₂) :
    NumberField.Idele.idelicHaar F (D ∩ window (F := F) d₁ d₂ e₁ e₂) < ⊤ :=
  (NumberField.Idele.idelicHaar_inter_setOf_ideleNorm_mem_Icc_pos_and_lt_top F D hD hDF _ _
    (lt_min (div_pos hd₁ he₂) one_pos) (by linarith [min_le_right (d₁ / e₂) 1, le_max_right (4 * d₂ / e₁) 1])).2

private theorem kernel_centralScalar_mul_eq_zero_of_notMem_window (ν : Measure (AdeleRing (𝓞 F) F))
    (w : AdelicGL2 (𝓞 F) F → ℂ) {d₁ d₂ e₁ e₂ : ℝ} (hd₁ : 0 < d₁) (he₁ : 0 < e₁) (a b R : ℝ) {g : AdelicGL2 (𝓞 F) F}
    (hg : ideleNorm F (Matrix.GeneralLinearGroup.det g) ∈ Set.Icc e₁ e₂) {z : (AdeleRing (𝓞 F) F)ˣ}
    (hz : z ∉ window (F := F) d₁ d₂ e₁ e₂) : kernel ν w d₁ d₂ a b R (centralScalar (𝓞 F) F z * g) = 0 := by
  refine kernel_eq_zero_of_det ν w d₁ d₂ a b R fun hmem => hz ?_
  rw [ideleNorm_det_centralScalar_mul] at hmem
  exact mem_window_of_mul_self_mul_mem hd₁ he₁ (ideleNorm_pos z) hmem hg

private theorem exists_forall_norm_average_le {ξ : (⊤ : Subgroup (AdeleRing (𝓞 F) F)ˣ) →* ℂˣ} (hξ : Continuous ξ)
    (hξF : ∀ γ ∈ M4aHerbrand.principalIdeles (𝓞 F) F, xi ξ γ = 1) {D : Set (AdeleRing (𝓞 F) F)ˣ} (hD : MeasurableSet D)
    (hDF : IsFundamentalDomain (M4aHerbrand.principalIdeles (𝓞 F) F) D (NumberField.Idele.idelicHaar F))
    (ν : Measure (AdeleRing (𝓞 F) F)) (w : AdelicGL2 (𝓞 F) F → ℂ) {d₁ : ℝ} (d₂ : ℝ) (hd₁ : 0 < d₁) (a b : ℝ) {R : ℝ}
    (hR : 0 ≤ R) {e₁ : ℝ} (e₂ : ℝ) (he₁ : 0 < e₁) :
    ∃ C : ℝ, ∀ g : AdelicGL2 (𝓞 F) F, ideleNorm F (Matrix.GeneralLinearGroup.det g) ∈ Set.Icc e₁ e₂ →
      ‖average ξ D ν w d₁ d₂ a b R g‖ ≤ C := by
  rcases lt_or_ge e₂ e₁ with he | he
  · exact ⟨0, fun g hg => absurd (hg.1.trans hg.2) (not_le.mpr he)⟩
  have he₂ : 0 < e₂ := he₁.trans_le he
  obtain ⟨M, -, hM⟩ :=
    exists_forall_norm_xi_le hξ hξF (β := max (4 * d₂ / e₁) 1 + 1) (lt_min (div_pos hd₁ he₂) one_pos)
  have hfin := window_volume_lt_top hD hDF (d₂ := d₂) (e₁ := e₁) hd₁ he₂
  refine ⟨M * R * (NumberField.Idele.idelicHaar F).real (D ∩ window (F := F) d₁ d₂ e₁ e₂), fun g hg => ?_⟩
  have hcut : average ξ D ν w d₁ d₂ a b R g = ∫ z in D ∩ window (F := F) d₁ d₂ e₁ e₂,
      (xi ξ z)⁻¹ * kernel ν w d₁ d₂ a b R (centralScalar (𝓞 F) F z * g) ∂(NumberField.Idele.idelicHaar F) := by
    unfold average
    refine setIntegral_eq_of_subset_of_forall_diff_eq_zero hD Set.inter_subset_left fun z hz => ?_
    rw [kernel_centralScalar_mul_eq_zero_of_notMem_window ν w hd₁ he₁ a b R hg fun hzw => hz.2 ⟨hz.1, hzw⟩, mul_zero]
  rw [hcut]
  refine norm_setIntegral_le_of_norm_le_const hfin fun z hz => ?_
  rw [norm_mul]
  exact mul_le_mul (hM z hz.2).2 (norm_kernel_le ν w hR _) (norm_nonneg _) ((norm_nonneg _).trans (hM z hz.2).2)

private def seen (ξ : (⊤ : Subgroup (AdeleRing (𝓞 F) F)ˣ) →* ℂˣ) (ν : Measure (AdeleRing (𝓞 F) F))
    (w : AdelicGL2 (𝓞 F) F → ℂ) (d₁ d₂ a b R : ℝ) (g : AdelicGL2 (𝓞 F) F) : Set (AdeleRing (𝓞 F) F)ˣ :=
  {z | ideleNorm F z * ideleNorm F z * ideleNorm F (Matrix.GeneralLinearGroup.det g) ∈ Set.Icc d₁ (4 * d₂) ∧
    adelicHeight F g ∈ Set.Icc a b ∧ ‖xi ξ z‖ * ‖ct ν w g‖ ≤ R}

private theorem measurableSet_seen {ξ : (⊤ : Subgroup (AdeleRing (𝓞 F) F)ˣ) →* ℂˣ} (hξ : Continuous ξ)
    (ν : Measure (AdeleRing (𝓞 F) F)) (w : AdelicGL2 (𝓞 F) F → ℂ) (d₁ d₂ a b R : ℝ) (g : AdelicGL2 (𝓞 F) F) :
    MeasurableSet (seen ξ ν w d₁ d₂ a b R g) := by
  unfold seen
  refine (((measurable_ideleNorm' (F := F)).mul measurable_ideleNorm').mul_const _ measurableSet_Icc).inter
    ((MeasurableSet.const _).inter ?_)
  exact measurableSet_le ((measurable_xi hξ).norm.mul_const _) measurable_const

private theorem centralScalar_mul_mem_cutSet_iff {ξ : (⊤ : Subgroup (AdeleRing (𝓞 F) F)ˣ) →* ℂˣ}
    (ν : Measure (AdeleRing (𝓞 F) F)) (w : AdelicGL2 (𝓞 F) F → ℂ) (d₁ d₂ a b R : ℝ) {g : AdelicGL2 (𝓞 F) F}
    {z : (AdeleRing (𝓞 F) F)ˣ} (hlaw : ct ν w (centralScalar (𝓞 F) F z * g) = xi ξ z * ct ν w g) :
    centralScalar (𝓞 F) F z * g ∈ cutSet ν w d₁ d₂ a b R ↔ z ∈ seen ξ ν w d₁ d₂ a b R g := by
  simp only [cutSet, seen, Set.mem_setOf_eq, ideleNorm_det_centralScalar_mul, adelicHeight_centralScalar_mul, hlaw,
    norm_mul]

private theorem integrand_eq_indicator {ξ : (⊤ : Subgroup (AdeleRing (𝓞 F) F)ˣ) →* ℂˣ}
    (ν : Measure (AdeleRing (𝓞 F) F))
    (w : AdelicGL2 (𝓞 F) F → ℂ) (d₁ d₂ a b R : ℝ) {g : AdelicGL2 (𝓞 F) F} {z : (AdeleRing (𝓞 F) F)ˣ}
    (hlaw : ct ν w (centralScalar (𝓞 F) F z * g) = xi ξ z * ct ν w g) :
    (xi ξ z)⁻¹ * kernel ν w d₁ d₂ a b R (centralScalar (𝓞 F) F z * g)
      = (seen ξ ν w d₁ d₂ a b R g).indicator (fun _ => ct ν w g) z := by
  unfold kernel
  by_cases hz : z ∈ seen ξ ν w d₁ d₂ a b R g
  · rw [Set.indicator_of_mem ((centralScalar_mul_mem_cutSet_iff ν w d₁ d₂ a b R hlaw).mpr hz), Set.indicator_of_mem hz,
      hlaw, inv_mul_cancel_left₀ (xi_ne_zero ξ z)]
  · rw [Set.indicator_of_notMem (fun h => hz ((centralScalar_mul_mem_cutSet_iff ν w d₁ d₂ a b R hlaw).mp h)),
      Set.indicator_of_notMem hz, mul_zero]

private def weight (ξ : (⊤ : Subgroup (AdeleRing (𝓞 F) F)ˣ) →* ℂˣ) (D : Set (AdeleRing (𝓞 F) F)ˣ)
    (ν : Measure (AdeleRing (𝓞 F) F)) (w : AdelicGL2 (𝓞 F) F → ℂ) (d₁ d₂ a b R : ℝ) (g : AdelicGL2 (𝓞 F) F) : ℝ :=
  (NumberField.Idele.idelicHaar F).real (D ∩ window (F := F) d₁ d₂ d₁ d₂ ∩ seen ξ ν w d₁ d₂ a b R g)

private theorem weight_nonneg (ξ : (⊤ : Subgroup (AdeleRing (𝓞 F) F)ˣ) →* ℂˣ) (D : Set (AdeleRing (𝓞 F) F)ˣ)
    (ν : Measure (AdeleRing (𝓞 F) F)) (w : AdelicGL2 (𝓞 F) F → ℂ) (d₁ d₂ a b R : ℝ) (g : AdelicGL2 (𝓞 F) F) :
    0 ≤ weight ξ D ν w d₁ d₂ a b R g :=
  ENNReal.toReal_nonneg

private theorem weight_le {ξ : (⊤ : Subgroup (AdeleRing (𝓞 F) F)ˣ) →* ℂˣ} {D : Set (AdeleRing (𝓞 F) F)ˣ}
    {d₁ d₂ : ℝ} (hfin : NumberField.Idele.idelicHaar F (D ∩ window (F := F) d₁ d₂ d₁ d₂) < ⊤)
    (ν : Measure (AdeleRing (𝓞 F) F)) (w : AdelicGL2 (𝓞 F) F → ℂ) (a b R : ℝ) (g : AdelicGL2 (𝓞 F) F) :
    weight ξ D ν w d₁ d₂ a b R g ≤ (NumberField.Idele.idelicHaar F).real (D ∩ window (F := F) d₁ d₂ d₁ d₂) := by
  unfold weight
  rw [measureReal_def, measureReal_def]
  exact ENNReal.toReal_mono hfin.ne (measure_mono Set.inter_subset_left)

private theorem weight_eq_zero_of_height (ξ : (⊤ : Subgroup (AdeleRing (𝓞 F) F)ˣ) →* ℂˣ) (D : Set (AdeleRing (𝓞 F) F)ˣ)
    (ν : Measure (AdeleRing (𝓞 F) F)) (w : AdelicGL2 (𝓞 F) F → ℂ) (d₁ d₂ a b R : ℝ) {g : AdelicGL2 (𝓞 F) F}
    (hg : adelicHeight F g ∉ Set.Icc a b) : weight ξ D ν w d₁ d₂ a b R g = 0 := by
  unfold weight
  have hempty : seen ξ ν w d₁ d₂ a b R g = ∅ := Set.eq_empty_of_forall_notMem fun z hz => hg hz.2.1
  rw [hempty, Set.inter_empty, measureReal_empty]

private theorem norm_ct_le_of_weight_ne_zero {ξ : (⊤ : Subgroup (AdeleRing (𝓞 F) F)ˣ) →* ℂˣ}
    {D : Set (AdeleRing (𝓞 F) F)ˣ}
    (ν : Measure (AdeleRing (𝓞 F) F)) (w : AdelicGL2 (𝓞 F) F → ℂ) {d₁ d₂ : ℝ} {M : ℝ}
    (hM : ∀ z : (AdeleRing (𝓞 F) F)ˣ, z ∈ window (F := F) d₁ d₂ d₁ d₂ → ‖xi ξ z‖ ≤ M ∧ ‖(xi ξ z)⁻¹‖ ≤ M) (a b : ℝ)
    {R : ℝ} (_hR : 0 ≤ R) {g : AdelicGL2 (𝓞 F) F} (hg : weight ξ D ν w d₁ d₂ a b R g ≠ 0) : ‖ct ν w g‖ ≤ R * M := by
  have hne : NumberField.Idele.idelicHaar F (D ∩ window (F := F) d₁ d₂ d₁ d₂ ∩ seen ξ ν w d₁ d₂ a b R g) ≠ 0 := by
    intro h0
    exact hg (by unfold weight; rw [measureReal_def, h0, ENNReal.toReal_zero])
  obtain ⟨z, hz⟩ := nonempty_of_measure_ne_zero hne
  obtain ⟨hzM, hzM'⟩ := hM z hz.1.2
  have hseen : ‖xi ξ z‖ * ‖ct ν w g‖ ≤ R := hz.2.2.2
  have hxi : 0 < ‖xi ξ z‖ := norm_pos_iff.mpr (xi_ne_zero ξ z)
  rw [norm_inv] at hzM'
  calc ‖ct ν w g‖ = ‖xi ξ z‖⁻¹ * (‖xi ξ z‖ * ‖ct ν w g‖) := by rw [inv_mul_cancel_left₀ hxi.ne']
    _ ≤ M * R := mul_le_mul hzM' hseen (by positivity) ((inv_nonneg.mpr hxi.le).trans hzM')
    _ = R * M := mul_comm _ _

private theorem le_weight {ξ : (⊤ : Subgroup (AdeleRing (𝓞 F) F)ˣ) →* ℂˣ} {D : Set (AdeleRing (𝓞 F) F)ˣ} {d₁ d₂ : ℝ}
    (hd₁ : 0 < d₁) (hfin : NumberField.Idele.idelicHaar F (D ∩ window (F := F) d₁ d₂ d₁ d₂) < ⊤) {M₀ : ℝ}
    (hM₀ : ∀ z : (AdeleRing (𝓞 F) F)ˣ, ideleNorm F z ∈ Set.Icc 1 2 → ‖xi ξ z‖ ≤ M₀ ∧ ‖(xi ξ z)⁻¹‖ ≤ M₀)
    (ν : Measure (AdeleRing (𝓞 F) F)) (w : AdelicGL2 (𝓞 F) F → ℂ) {a b : ℝ} {g : AdelicGL2 (𝓞 F) F}
    (hgs : ideleNorm F (Matrix.GeneralLinearGroup.det g) ∈ Set.Icc d₁ d₂) (hgb : adelicHeight F g ∈ Set.Icc a b)
    {R : ℝ}
    (hR : M₀ * ‖ct ν w g‖ ≤ R) :
    (NumberField.Idele.idelicHaar F).real (D ∩ {z | ideleNorm F z ∈ Set.Icc 1 2}) ≤ weight ξ D ν w d₁ d₂ a b R g := by
  unfold weight
  rw [measureReal_def, measureReal_def]
  refine ENNReal.toReal_mono ((measure_mono Set.inter_subset_left).trans_lt hfin).ne (measure_mono fun z hz => ?_)
  obtain ⟨hzD, hz12⟩ := hz
  have hz1 : (1 : ℝ) ≤ ideleNorm F z := hz12.1
  have hz2 : ideleNorm F z ≤ 2 := hz12.2
  refine ⟨⟨hzD, ?_⟩, ?_, hgb, ?_⟩
  ·
    refine ⟨(min_le_right _ _).trans hz1, hz2.trans ?_⟩
    linarith [le_max_right (4 * d₂ / d₁) 1]
  · have hd := hgs.1
    have hd' := hgs.2
    have hdg : 0 ≤ ideleNorm F (Matrix.GeneralLinearGroup.det g) := hd₁.le.trans hd
    constructor
    · nlinarith [hd, mul_nonneg (mul_nonneg (sub_nonneg.2 hz1) (by linarith : (0 : ℝ) ≤ ideleNorm F z + 1)) hdg]
    · nlinarith [hd', mul_nonneg (mul_nonneg (sub_nonneg.2 hz2) (by linarith : (0 : ℝ) ≤ 2 + ideleNorm F z)) hdg]
  · exact (mul_le_mul_of_nonneg_right (hM₀ z hz12).1 (norm_nonneg _)).trans hR

private theorem ae_average_eq_weight_smul {ξ : (⊤ : Subgroup (AdeleRing (𝓞 F) F)ˣ) →* ℂˣ}
    {D : Set (AdeleRing (𝓞 F) F)ˣ}
    (hD : MeasurableSet D) {d₁ d₂ : ℝ} (hfin : NumberField.Idele.idelicHaar F (D ∩ window (F := F) d₁ d₂ d₁ d₂) < ⊤)
    (hξ : Continuous ξ) {u : AdelicGL2 (𝓞 F) F → ℂ} (hu : IsLsXiFunction (𝓞 F) F ⊤ ξ u) {w : AdelicGL2 (𝓞 F) F → ℂ}
    (hwu : w =ᵐ[adelicGLHaar (Fin 2) (𝓞 F) F] u) (hd₁ : 0 < d₁) (ρ : Measure (AdelicGL2 (𝓞 F) F)) [SFinite ρ]
    (hρ : ρ ≤ adelicGLHaar (Fin 2) (𝓞 F) F)
    (hρs : ∀ᵐ g ∂ρ, ideleNorm F (Matrix.GeneralLinearGroup.det g) ∈ Set.Icc d₁ d₂)
    (a b R : ℝ) :
    ∀ᵐ g ∂ρ, average ξ D (ProbabilityTheory.cond (adelicAddHaar (𝓞 F) F) (AdelicBox.adelicBox F)) w d₁ d₂ a b R g
      = (weight ξ D (ProbabilityTheory.cond (adelicAddHaar (𝓞 F) F) (AdelicBox.adelicBox F)) w d₁ d₂ a b R g : ℂ) *
        ct (ProbabilityTheory.cond (adelicAddHaar (𝓞 F) F) (AdelicBox.adelicBox F)) w g := by
  set ν := ProbabilityTheory.cond (adelicAddHaar (𝓞 F) F) (AdelicBox.adelicBox F) with hν
  set W := window (F := F) d₁ d₂ d₁ d₂ with hW
  haveI : IsFiniteMeasure ((NumberField.Idele.idelicHaar F).restrict (D ∩ W)) := isFiniteMeasure_restrict.mpr hfin.ne
  have hlaw := ae_ae_ct_centralScalar_mul hu hwu ρ hρ ((NumberField.Idele.idelicHaar F).restrict (D ∩ W))
  filter_upwards [hlaw, hρs] with g hg hgs
  have hcut : average ξ D ν w d₁ d₂ a b R g =
      ∫ z in D ∩ W, (xi ξ z)⁻¹ * kernel ν w d₁ d₂ a b R (centralScalar (𝓞 F) F z * g)
        ∂(NumberField.Idele.idelicHaar F) := by
    unfold average
    refine setIntegral_eq_of_subset_of_forall_diff_eq_zero hD Set.inter_subset_left fun z hz => ?_
    rw [kernel_centralScalar_mul_eq_zero_of_notMem_window ν w hd₁ hd₁ a b R hgs fun hzw => hz.2 ⟨hz.1, hzw⟩, mul_zero]
  have hint : ∫ z in D ∩ W, (xi ξ z)⁻¹ * kernel ν w d₁ d₂ a b R (centralScalar (𝓞 F) F z * g)
        ∂(NumberField.Idele.idelicHaar F)
      = ∫ z in D ∩ W, (seen ξ ν w d₁ d₂ a b R g).indicator (fun _ => ct ν w g) z ∂(NumberField.Idele.idelicHaar F) :=
    integral_congr_ae (hg.mono fun z hz => integrand_eq_indicator ν w d₁ d₂ a b R hz)
  rw [hcut, hint, setIntegral_indicator (measurableSet_seen hξ ν w d₁ d₂ a b R g), setIntegral_const, weight,
    Complex.real_smul]

private theorem ae_average_mul_conj_eq {ξ : (⊤ : Subgroup (AdeleRing (𝓞 F) F)ˣ) →* ℂˣ} {D : Set (AdeleRing (𝓞 F) F)ˣ}
    (hD : MeasurableSet D) {d₁ d₂ : ℝ} (hfin : NumberField.Idele.idelicHaar F (D ∩ window (F := F) d₁ d₂ d₁ d₂) < ⊤)
    (hξ : Continuous ξ) {u : AdelicGL2 (𝓞 F) F → ℂ} (hu : IsLsXiFunction (𝓞 F) F ⊤ ξ u) {w : AdelicGL2 (𝓞 F) F → ℂ}
    (hwu : w =ᵐ[adelicGLHaar (Fin 2) (𝓞 F) F] u) (hd₁ : 0 < d₁) {S' : Set (AdelicGL2 (𝓞 F) F)}
    (hS' : NullMeasurableSet S' (adelicGLHaar (Fin 2) (𝓞 F) F))
    (hS's : S' ⊆ {g | ideleNorm F (Matrix.GeneralLinearGroup.det g) ∈ Set.Icc d₁ d₂}) (a b R : ℝ) :
    (fun g => average ξ D (ProbabilityTheory.cond (adelicAddHaar (𝓞 F) F) (AdelicBox.adelicBox F)) w d₁ d₂ a b R g *
        (starRingEnd ℂ) (ct (ProbabilityTheory.cond (adelicAddHaar (𝓞 F) F) (AdelicBox.adelicBox F)) w g))
      =ᵐ[(adelicGLHaar (Fin 2) (𝓞 F) F).restrict S'] fun g =>
        ((weight ξ D (ProbabilityTheory.cond (adelicAddHaar (𝓞 F) F) (AdelicBox.adelicBox F)) w d₁ d₂ a b R g *
          ‖ct (ProbabilityTheory.cond (adelicAddHaar (𝓞 F) F) (AdelicBox.adelicBox F)) w g‖ ^ 2 : ℝ) : ℂ) := by
  haveI := sigmaFinite_adelicGLHaar (F := F)
  have hmem : ∀ᵐ g ∂(adelicGLHaar (Fin 2) (𝓞 F) F).restrict S',
      ideleNorm F (Matrix.GeneralLinearGroup.det g) ∈ Set.Icc d₁ d₂ :=
    (ae_restrict_mem₀ hS').mono fun g hg => hS's hg
  have h := ae_average_eq_weight_smul hD hfin hξ hu hwu hd₁ ((adelicGLHaar (Fin 2) (𝓞 F) F).restrict S')
    Measure.restrict_le_self hmem a b R
  filter_upwards [h] with g hg
  rw [hg, mul_assoc, Complex.mul_conj, Complex.normSq_eq_norm_sq]
  push_cast
  ring

private theorem exists_ae_norm_average_mul_conj_le {ξ : (⊤ : Subgroup (AdeleRing (𝓞 F) F)ˣ) →* ℂˣ} (hξ : Continuous ξ)
    (hξF : ∀ γ ∈ M4aHerbrand.principalIdeles (𝓞 F) F, xi ξ γ = 1) {D : Set (AdeleRing (𝓞 F) F)ˣ} (hD : MeasurableSet D)
    (hDF : IsFundamentalDomain (M4aHerbrand.principalIdeles (𝓞 F) F) D (NumberField.Idele.idelicHaar F))
    {u : AdelicGL2 (𝓞 F) F → ℂ} (hu : IsLsXiFunction (𝓞 F) F ⊤ ξ u) {w : AdelicGL2 (𝓞 F) F → ℂ}
    (hwu : w =ᵐ[adelicGLHaar (Fin 2) (𝓞 F) F] u) {d₁ : ℝ} (d₂ : ℝ) (hd₁ : 0 < d₁) (hd₂ : 0 < d₂)
    {S' : Set (AdelicGL2 (𝓞 F) F)}
    (hS' : NullMeasurableSet S' (adelicGLHaar (Fin 2) (𝓞 F) F))
    (hS's : S' ⊆ {g | ideleNorm F (Matrix.GeneralLinearGroup.det g) ∈ Set.Icc d₁ d₂}) (a b : ℝ) {R : ℝ} (hR : 0 ≤ R) :
    ∃ C : ℝ, ∀ᵐ g ∂(adelicGLHaar (Fin 2) (𝓞 F) F).restrict S',
      ‖average ξ D (ProbabilityTheory.cond (adelicAddHaar (𝓞 F) F) (AdelicBox.adelicBox F)) w d₁ d₂ a b R g *
        (starRingEnd ℂ) (ct (ProbabilityTheory.cond (adelicAddHaar (𝓞 F) F) (AdelicBox.adelicBox F)) w g)‖ ≤ C := by
  set ν := ProbabilityTheory.cond (adelicAddHaar (𝓞 F) F) (AdelicBox.adelicBox F) with hν
  clear_value ν
  have hfin : NumberField.Idele.idelicHaar F (D ∩ window (F := F) d₁ d₂ d₁ d₂) < ⊤ :=
    window_volume_lt_top hD hDF hd₁ hd₂
  obtain ⟨M, -, hM⟩ :=
    exists_forall_norm_xi_le hξ hξF (β := max (4 * d₂ / d₁) 1 + 1) (lt_min (div_pos hd₁ hd₂) one_pos)
  have hMw : ∀ z : (AdeleRing (𝓞 F) F)ˣ,
      z ∈ window (F := F) d₁ d₂ d₁ d₂ → ‖xi ξ z‖ ≤ M ∧ ‖(xi ξ z)⁻¹‖ ≤ M :=
    fun z hz => hM z hz
  refine ⟨(NumberField.Idele.idelicHaar F).real (D ∩ window (F := F) d₁ d₂ d₁ d₂) * (R * M) ^ 2, ?_⟩
  have hae := ae_average_mul_conj_eq hD hfin hξ hu hwu hd₁ hS' hS's a b R
  rw [← hν] at hae
  filter_upwards [hae] with g hg
  rw [hg, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (weight_nonneg _ _ _ _ _ _ _ _ _ _)
    (sq_nonneg _))]
  by_cases hwt : weight ξ D ν w d₁ d₂ a b R g = 0
  · rw [hwt, zero_mul]
    exact mul_nonneg ENNReal.toReal_nonneg (sq_nonneg _)
  · have hct := norm_ct_le_of_weight_ne_zero ν w hMw a b hR hwt
    exact mul_le_mul (weight_le hfin ν w a b R g) (pow_le_pow_left₀ (norm_nonneg _) hct 2) (sq_nonneg _)
      ENNReal.toReal_nonneg

private theorem weight_mul_sq_le_indicator {ξ : (⊤ : Subgroup (AdeleRing (𝓞 F) F)ˣ) →* ℂˣ}
    {D : Set (AdeleRing (𝓞 F) F)ˣ}
    {d₁ d₂ : ℝ} (hfin : NumberField.Idele.idelicHaar F (D ∩ window (F := F) d₁ d₂ d₁ d₂) < ⊤) {M : ℝ}
    (hM : ∀ z : (AdeleRing (𝓞 F) F)ˣ, z ∈ window (F := F) d₁ d₂ d₁ d₂ → ‖xi ξ z‖ ≤ M ∧ ‖(xi ξ z)⁻¹‖ ≤ M)
    (ν : Measure (AdeleRing (𝓞 F) F)) (w : AdelicGL2 (𝓞 F) F → ℂ) (a b : ℝ) {R : ℝ} (hR : 0 ≤ R)
    (g : AdelicGL2 (𝓞 F) F) :
    weight ξ D ν w d₁ d₂ a b R g * ‖ct ν w g‖ ^ 2
      ≤ ({g | adelicHeight F g ∈ Set.Icc a b} : Set (AdelicGL2 (𝓞 F) F)).indicator
          (fun _ => (NumberField.Idele.idelicHaar F).real (D ∩ window (F := F) d₁ d₂ d₁ d₂) * (R * M) ^ 2) g := by
  by_cases hgb : adelicHeight F g ∈ Set.Icc a b
  · rw [Set.indicator_of_mem (show g ∈ {g : AdelicGL2 (𝓞 F) F | adelicHeight F g ∈ Set.Icc a b} from hgb)]
    by_cases hwt : weight ξ D ν w d₁ d₂ a b R g = 0
    · rw [hwt, zero_mul]
      exact mul_nonneg ENNReal.toReal_nonneg (sq_nonneg _)
    · exact mul_le_mul (weight_le hfin ν w a b R g)
        (pow_le_pow_left₀ (norm_nonneg _) (norm_ct_le_of_weight_ne_zero ν w hM a b hR hwt) 2) (sq_nonneg _)
        ENNReal.toReal_nonneg
  · simp only [Set.indicator_of_notMem (show g ∉ {g : AdelicGL2 (𝓞 F) F | adelicHeight F g ∈ Set.Icc a b} from hgb),
      weight_eq_zero_of_height ξ D ν w d₁ d₂ a b R hgb, zero_mul, le_refl]

private theorem integrableOn_weight_mul_sq {ξ : (⊤ : Subgroup (AdeleRing (𝓞 F) F)ˣ) →* ℂˣ} (hξ : Continuous ξ)
    (hξF : ∀ γ ∈ M4aHerbrand.principalIdeles (𝓞 F) F, xi ξ γ = 1) {D : Set (AdeleRing (𝓞 F) F)ˣ} (hD : MeasurableSet D)
    (hDF : IsFundamentalDomain (M4aHerbrand.principalIdeles (𝓞 F) F) D (NumberField.Idele.idelicHaar F))
    {u : AdelicGL2 (𝓞 F) F → ℂ} (hu : IsLsXiFunction (𝓞 F) F ⊤ ξ u) {w : AdelicGL2 (𝓞 F) F → ℂ} (hwm : Measurable w)
    (hwu : w =ᵐ[adelicGLHaar (Fin 2) (𝓞 F) F] u) {d₁ : ℝ} (d₂ : ℝ) (hd₁ : 0 < d₁) (hd₂ : 0 < d₂)
    {S' : Set (AdelicGL2 (𝓞 F) F)}
    (hS' : NullMeasurableSet S' (adelicGLHaar (Fin 2) (𝓞 F) F))
    (hS's : S' ⊆ {g | ideleNorm F (Matrix.GeneralLinearGroup.det g) ∈ Set.Icc d₁ d₂})
    (hfinite : ∀ a b : ℝ, 0 < a → adelicGLHaar (Fin 2) (𝓞 F) F (S' ∩ {g | adelicHeight F g ∈ Set.Icc a b}) < ⊤)
    {a : ℝ} (b : ℝ) (ha : 0 < a) {R : ℝ} (hR : 0 ≤ R) :
    IntegrableOn (fun g =>
        weight ξ D (ProbabilityTheory.cond (adelicAddHaar (𝓞 F) F) (AdelicBox.adelicBox F)) w d₁ d₂ a b R g *
          ‖ct (ProbabilityTheory.cond (adelicAddHaar (𝓞 F) F) (AdelicBox.adelicBox F)) w g‖ ^ 2)
      S' (adelicGLHaar (Fin 2) (𝓞 F) F) := by
  set ν := ProbabilityTheory.cond (adelicAddHaar (𝓞 F) F) (AdelicBox.adelicBox F) with hν
  clear_value ν
  haveI : IsProbabilityMeasure ν := by
    rw [hν]
    exact NumberField.AdelicBox.isProbabilityMeasure_cond_adelicBox F
  have hfin : NumberField.Idele.idelicHaar F (D ∩ window (F := F) d₁ d₂ d₁ d₂) < ⊤ :=
    window_volume_lt_top hD hDF hd₁ hd₂
  obtain ⟨M, -, hM⟩ :=
    exists_forall_norm_xi_le hξ hξF (β := max (4 * d₂ / d₁) 1 + 1) (lt_min (div_pos hd₁ hd₂) one_pos)
  have hMw : ∀ z : (AdeleRing (𝓞 F) F)ˣ,
      z ∈ window (F := F) d₁ d₂ d₁ d₂ → ‖xi ξ z‖ ≤ M ∧ ‖(xi ξ z)⁻¹‖ ≤ M :=
    fun z hz => hM z hz
  have hbandmeas : MeasurableSet {g : AdelicGL2 (𝓞 F) F | adelicHeight F g ∈ Set.Icc a b} :=
    (measurable_adelicHeight F) measurableSet_Icc
  have hmaj : IntegrableOn (fun g : AdelicGL2 (𝓞 F) F =>
      ({g | adelicHeight F g ∈ Set.Icc a b} : Set (AdelicGL2 (𝓞 F) F)).indicator
        (fun _ => (NumberField.Idele.idelicHaar F).real (D ∩ window (F := F) d₁ d₂ d₁ d₂) * (R * M) ^ 2) g)
      S' (adelicGLHaar (Fin 2) (𝓞 F) F) := by
    rw [IntegrableOn, integrable_indicator_iff hbandmeas, IntegrableOn, Measure.restrict_restrict hbandmeas,
      Set.inter_comm]
    exact integrableOn_const (by simpa only [Set.inter_comm] using (hfinite a b ha).ne)
  have hct : Measurable (ct ν w) := measurable_ct ν hwm
  have hpair : Measurable fun g => (average ξ D ν w d₁ d₂ a b R g * (starRingEnd ℂ) (ct ν w g)).re :=
    Complex.measurable_re.comp
      ((measurable_average hξ D ν hct d₁ d₂ a b R).mul (Complex.continuous_conj.measurable.comp hct))
  have haesm : AEStronglyMeasurable (fun g => weight ξ D ν w d₁ d₂ a b R g * ‖ct ν w g‖ ^ 2)
      ((adelicGLHaar (Fin 2) (𝓞 F) F).restrict S') := by
    refine hpair.aestronglyMeasurable.congr ?_
    have hae := ae_average_mul_conj_eq hD hfin hξ hu hwu hd₁ hS' hS's a b R
    rw [← hν] at hae
    filter_upwards [hae] with g hg
    rw [hg, Complex.ofReal_re]
  refine Integrable.mono' hmaj haesm (Filter.Eventually.of_forall fun g => ?_)
  rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (weight_nonneg _ _ _ _ _ _ _ _ _ _) (sq_nonneg _))]
  exact weight_mul_sq_le_indicator hfin hMw ν w a b hR g

private theorem ae_weight_mul_sq_eq_zero {ξ : (⊤ : Subgroup (AdeleRing (𝓞 F) F)ˣ) →* ℂˣ} (hξ : Continuous ξ)
    (hξF : ∀ γ ∈ M4aHerbrand.principalIdeles (𝓞 F) F, xi ξ γ = 1) {D : Set (AdeleRing (𝓞 F) F)ˣ} (hD : MeasurableSet D)
    (hDF : IsFundamentalDomain (M4aHerbrand.principalIdeles (𝓞 F) F) D (NumberField.Idele.idelicHaar F))
    {u : AdelicGL2 (𝓞 F) F → ℂ} (hu : IsLsXiFunction (𝓞 F) F ⊤ ξ u) {w : AdelicGL2 (𝓞 F) F → ℂ} (hwm : Measurable w)
    (hwu : w =ᵐ[adelicGLHaar (Fin 2) (𝓞 F) F] u) {d₁ : ℝ} (d₂ : ℝ) (hd₁ : 0 < d₁) (hd₂ : 0 < d₂)
    {S' : Set (AdelicGL2 (𝓞 F) F)}
    (hS' : NullMeasurableSet S' (adelicGLHaar (Fin 2) (𝓞 F) F))
    (hS's : S' ⊆ {g | ideleNorm F (Matrix.GeneralLinearGroup.det g) ∈ Set.Icc d₁ d₂})
    (hfinite : ∀ a b : ℝ, 0 < a → adelicGLHaar (Fin 2) (𝓞 F) F (S' ∩ {g | adelicHeight F g ∈ Set.Icc a b}) < ⊤)
    {a : ℝ} (b : ℝ) (ha : 0 < a) {R : ℝ} (hR : 0 ≤ R)
    (hzero : ∫ g in S',
        average ξ D (ProbabilityTheory.cond (adelicAddHaar (𝓞 F) F) (AdelicBox.adelicBox F)) w d₁ d₂ a b R g *
        (starRingEnd ℂ) (ct (ProbabilityTheory.cond (adelicAddHaar (𝓞 F) F) (AdelicBox.adelicBox F)) w g)
          ∂(adelicGLHaar (Fin 2) (𝓞 F) F) = 0) :
    ∀ᵐ g ∂(adelicGLHaar (Fin 2) (𝓞 F) F).restrict S',
      weight ξ D (ProbabilityTheory.cond (adelicAddHaar (𝓞 F) F) (AdelicBox.adelicBox F)) w d₁ d₂ a b R g *
        ‖ct (ProbabilityTheory.cond (adelicAddHaar (𝓞 F) F) (AdelicBox.adelicBox F)) w g‖ ^ 2 = 0 := by
  set ν := ProbabilityTheory.cond (adelicAddHaar (𝓞 F) F) (AdelicBox.adelicBox F) with hν
  clear_value ν
  have hfin : NumberField.Idele.idelicHaar F (D ∩ window (F := F) d₁ d₂ d₁ d₂) < ⊤ :=
    window_volume_lt_top hD hDF hd₁ hd₂
  have hae := ae_average_mul_conj_eq hD hfin hξ hu hwu hd₁ hS' hS's a b R
  rw [← hν] at hae
  have hreal : ∫ g in S', weight ξ D ν w d₁ d₂ a b R g * ‖ct ν w g‖ ^ 2 ∂(adelicGLHaar (Fin 2) (𝓞 F) F) = 0 := by
    have h1 : ∫ g in S', ((weight ξ D ν w d₁ d₂ a b R g * ‖ct ν w g‖ ^ 2 : ℝ) : ℂ) ∂(adelicGLHaar (Fin 2) (𝓞 F) F)
        = 0 := by
      rw [← hzero]
      exact (integral_congr_ae hae).symm
    rw [integral_complex_ofReal] at h1
    exact Complex.ofReal_eq_zero.mp h1
  have hnonneg : 0 ≤ᵐ[(adelicGLHaar (Fin 2) (𝓞 F) F).restrict S']
      fun g => weight ξ D ν w d₁ d₂ a b R g * ‖ct ν w g‖ ^ 2 :=
    Filter.Eventually.of_forall fun g => mul_nonneg (weight_nonneg ξ D ν w d₁ d₂ a b R g) (sq_nonneg _)
  have hint := integrableOn_weight_mul_sq hξ hξF hD hDF hu hwm hwu d₂ hd₁ hd₂ hS' hS's hfinite b ha hR
  rw [← hν] at hint
  exact (integral_eq_zero_iff_of_nonneg_ae hnonneg hint).mp hreal

private theorem exists_nat_mem_band {h : ℝ} (hpos : 0 < h) :
    ∃ m : ℕ, h ∈ Set.Icc (1 / ((m : ℝ) + 1)) ((m : ℝ) + 1) := by
  obtain ⟨m₁, hm₁⟩ := exists_nat_gt h
  obtain ⟨m₂, hm₂⟩ := exists_nat_one_div_lt hpos
  refine ⟨m₁ + m₂, ?_, ?_⟩
  · refine le_trans (one_div_le_one_div_of_le (by positivity) ?_) hm₂.le
    push_cast
    linarith [(Nat.cast_nonneg m₁ : (0 : ℝ) ≤ m₁)]
  · push_cast
    linarith [hm₁.le, (Nat.cast_nonneg m₂ : (0 : ℝ) ≤ m₂)]

private theorem ae_ct_eq_zero_of_forall_integral_average_mul_conj_eq_zero
    {ξ : (⊤ : Subgroup (AdeleRing (𝓞 F) F)ˣ) →* ℂˣ} (hξ : Continuous ξ)
    (hξF : ∀ γ ∈ M4aHerbrand.principalIdeles (𝓞 F) F, xi ξ γ = 1) {D : Set (AdeleRing (𝓞 F) F)ˣ} (hD : MeasurableSet D)
    (hDF : IsFundamentalDomain (M4aHerbrand.principalIdeles (𝓞 F) F) D (NumberField.Idele.idelicHaar F))
    {u : AdelicGL2 (𝓞 F) F → ℂ} (hu : IsLsXiFunction (𝓞 F) F ⊤ ξ u) {w : AdelicGL2 (𝓞 F) F → ℂ} (hwm : Measurable w)
    (hwu : w =ᵐ[adelicGLHaar (Fin 2) (𝓞 F) F] u) {d₁ : ℝ} (d₂ : ℝ) (hd₁ : 0 < d₁) (hd₂ : 0 < d₂)
    {S' : Set (AdelicGL2 (𝓞 F) F)}
    (hS' : NullMeasurableSet S' (adelicGLHaar (Fin 2) (𝓞 F) F))
    (hS's : S' ⊆ {g | ideleNorm F (Matrix.GeneralLinearGroup.det g) ∈ Set.Icc d₁ d₂})
    (hfinite : ∀ a b : ℝ, 0 < a → adelicGLHaar (Fin 2) (𝓞 F) F (S' ∩ {g | adelicHeight F g ∈ Set.Icc a b}) < ⊤)
    (hzero : ∀ a b R : ℝ, 0 < a → 0 ≤ R →
      ∫ g in S', average ξ D (ProbabilityTheory.cond (adelicAddHaar (𝓞 F) F) (AdelicBox.adelicBox F)) w d₁ d₂ a b R g *
        (starRingEnd ℂ) (ct (ProbabilityTheory.cond (adelicAddHaar (𝓞 F) F) (AdelicBox.adelicBox F)) w g)
          ∂(adelicGLHaar (Fin 2) (𝓞 F) F) = 0) :
    ct (ProbabilityTheory.cond (adelicAddHaar (𝓞 F) F) (AdelicBox.adelicBox F)) w
      =ᵐ[(adelicGLHaar (Fin 2) (𝓞 F) F).restrict S'] 0 := by
  set ν := ProbabilityTheory.cond (adelicAddHaar (𝓞 F) F) (AdelicBox.adelicBox F) with hν
  clear_value ν
  have hfin : NumberField.Idele.idelicHaar F (D ∩ window (F := F) d₁ d₂ d₁ d₂) < ⊤ :=
    window_volume_lt_top hD hDF hd₁ hd₂
  obtain ⟨M₀, -, hM₀⟩ := exists_forall_norm_xi_le hξ hξF (β := (2 : ℝ)) one_pos
  have hc₀ :=
    NumberField.Idele.idelicHaar_inter_setOf_ideleNorm_mem_Icc_pos_and_lt_top F D hD hDF 1 2 one_pos one_lt_two
  have hc₀pos : 0 < (NumberField.Idele.idelicHaar F).real (D ∩ {z | ideleNorm F z ∈ Set.Icc 1 2}) := by
    rw [measureReal_def]
    exact ENNReal.toReal_pos hc₀.1.ne' hc₀.2.ne
  have hall : ∀ᵐ g ∂(adelicGLHaar (Fin 2) (𝓞 F) F).restrict S', ∀ m n : ℕ,
      weight ξ D ν w d₁ d₂ (1 / ((m : ℝ) + 1)) ((m : ℝ) + 1) n g * ‖ct ν w g‖ ^ 2 = 0 := by
    rw [ae_all_iff]
    intro m
    rw [ae_all_iff]
    intro n
    have hz := hzero (1 / ((m : ℝ) + 1)) ((m : ℝ) + 1) n (by positivity) (Nat.cast_nonneg n)
    rw [hν] at hz
    have h := ae_weight_mul_sq_eq_zero hξ hξF hD hDF hu hwm hwu d₂ hd₁ hd₂ hS' hS's hfinite ((m : ℝ) + 1)
      (by positivity) (Nat.cast_nonneg n) hz
    rw [← hν] at h
    exact h
  filter_upwards [hall, ae_restrict_mem₀ hS'] with g hg hgS
  obtain ⟨m, hm⟩ := exists_nat_mem_band (adelicHeight_pos g)
  obtain ⟨n, hn⟩ := exists_nat_ge (M₀ * ‖ct ν w g‖)
  have hw := le_weight hd₁ hfin hM₀ ν w (hS's hgS) hm hn
  have hwpos : weight ξ D ν w d₁ d₂ (1 / ((m : ℝ) + 1)) ((m : ℝ) + 1) n g ≠ 0 := (hc₀pos.trans_le hw).ne'
  have hsq : ‖ct ν w g‖ ^ 2 = 0 := (mul_eq_zero.mp (hg m n)).resolve_left hwpos
  show ct ν w g = 0
  exact norm_eq_zero.mp (pow_eq_zero_iff two_ne_zero |>.mp hsq)

private theorem isSlabProfile_average {ξ : (⊤ : Subgroup (AdeleRing (𝓞 F) F)ˣ) →* ℂˣ} (hξ : Continuous ξ)
    (hξF : ∀ γ ∈ M4aHerbrand.principalIdeles (𝓞 F) F, xi ξ γ = 1) {D : Set (AdeleRing (𝓞 F) F)ˣ} (hD : MeasurableSet D)
    (hDF : IsFundamentalDomain (M4aHerbrand.principalIdeles (𝓞 F) F) D (NumberField.Idele.idelicHaar F))
    {w : AdelicGL2 (𝓞 F) F → ℂ} (hwm : Measurable w)
    (hwinv : ∀ (γ : GL (Fin 2) F) (g : AdelicGL2 (𝓞 F) F), w (globalPoints (𝓞 F) F γ * g) = w g) {d₁ : ℝ} (d₂ : ℝ)
    (hd₁ : 0 < d₁) {a : ℝ} (b : ℝ) (ha : 0 < a) {R : ℝ} (hR : 0 ≤ R) :
    IsSlabProfile F ⊤ ξ
      (average ξ D (ProbabilityTheory.cond (adelicAddHaar (𝓞 F) F) (AdelicBox.adelicBox F)) w d₁ d₂ a b R) where
  measurable := by
    haveI : IsProbabilityMeasure (ProbabilityTheory.cond (adelicAddHaar (𝓞 F) F) (AdelicBox.adelicBox F)) :=
      NumberField.AdelicBox.isProbabilityMeasure_cond_adelicBox F
    exact measurable_average hξ D _ (measurable_ct _ hwm) d₁ d₂ a b R
  unipotent_mul := fun x g => average_unipotentGL2_mul ξ D hwinv d₁ d₂ a b R x g
  borel_mul := fun γ hγ g => average_globalPoints_mul ξ D hwinv d₁ d₂ a b R hγ g
  central_transform := fun z g => average_centralScalar_mul hξF hDF hwinv d₁ d₂ a b R (z : (AdeleRing (𝓞 F) F)ˣ) g
  bounded_on_slab := fun _ e₂ he₁ =>
    exists_forall_norm_average_le hξ hξF hD hDF
      (ProbabilityTheory.cond (adelicAddHaar (𝓞 F) F) (AdelicBox.adelicBox F)) w d₂ hd₁ a b hR e₂ he₁
  height_band := ⟨a, b, ha, fun g hg => Classical.byContradiction fun hgb =>
    hg (average_eq_zero_of_height ξ D (ProbabilityTheory.cond (adelicAddHaar (𝓞 F) F) (AdelicBox.adelicBox F)) w d₁ d₂
      a b R hgb)⟩

private theorem ae_constantTerm_eq_zero_of_forall_isSlabProfile_setIntegral_mul_conj_eq_zero
    (Z : Subgroup (AdeleRing (𝓞 F) F)ˣ) (ξ : Z →* ℂˣ) (u : AdelicGL2 (𝓞 F) F → ℂ)
    (hu : IsLsXiFunction (𝓞 F) F Z ξ u) (w : AdelicGL2 (𝓞 F) F → ℂ) (hwm : Measurable w)
    (hwinv : ∀ (γ : GL (Fin 2) F) (g : AdelicGL2 (𝓞 F) F), w (globalPoints (𝓞 F) F γ * g) = w g)
    (hwu : w =ᵐ[adelicGLHaar (Fin 2) (𝓞 F) F] u) (hξ : Continuous ξ) (hZ : Z = ⊤)
    (hξF : ∀ γ ∈ M4aHerbrand.principalIdeles (𝓞 F) F, ∀ hγ : γ ∈ Z, ξ ⟨γ, hγ⟩ = 1)
    (d₁ d₂ : ℝ) (hd₁ : 0 < d₁) (hd₂ : 0 < d₂) (S' : Set (AdelicGL2 (𝓞 F) F))
    (hS' : NullMeasurableSet S' (adelicGLHaar (Fin 2) (𝓞 F) F))
    (hS's : S' ⊆ {g | ideleNorm F (Matrix.GeneralLinearGroup.det g) ∈ Set.Icc d₁ d₂})
    (hfinite : ∀ a b : ℝ, 0 < a → adelicGLHaar (Fin 2) (𝓞 F) F (S' ∩ {g | adelicHeight F g ∈ Set.Icc a b}) < ⊤)
    (hpair : ∀ φ : AdelicGL2 (𝓞 F) F → ℂ, IsSlabProfile F Z ξ φ →
      (∃ C : ℝ, ∀ᵐ g ∂(adelicGLHaar (Fin 2) (𝓞 F) F).restrict S',
        ‖φ g * (starRingEnd ℂ) (constantTerm (ProbabilityTheory.cond (adelicAddHaar (𝓞 F) F) (AdelicBox.adelicBox F))
          (fun x => unipotentGL2 x) w g)‖ ≤ C) →
      ∫ g in S', φ g * (starRingEnd ℂ) (constantTerm (ProbabilityTheory.cond (adelicAddHaar (𝓞 F) F)
        (AdelicBox.adelicBox F)) (fun x => unipotentGL2 x) w g) ∂(adelicGLHaar (Fin 2) (𝓞 F) F) = 0) :
    (fun g => constantTerm (ProbabilityTheory.cond (adelicAddHaar (𝓞 F) F) (AdelicBox.adelicBox F))
        (fun x => unipotentGL2 x) w g)
      =ᵐ[(adelicGLHaar (Fin 2) (𝓞 F) F).restrict S'] 0 := by
  subst hZ
  obtain ⟨D, hD, hDF, -⟩ :=
    exists_isFundamentalDomain_principalIdeles_forall_exists_integrableOn_min_ideleNorm_pow F
      (NumberField.Idele.idelicHaar F)
  have hξF' : ∀ γ ∈ M4aHerbrand.principalIdeles (𝓞 F) F, xi ξ γ = 1 := fun γ hγ => by
    simp only [xi, hξF γ hγ (Subgroup.mem_top γ), Units.val_one]
  exact ae_ct_eq_zero_of_forall_integral_average_mul_conj_eq_zero hξ hξF' hD hDF hu hwm hwu d₂ hd₁ hd₂ hS' hS's
    hfinite
    fun a b R ha hR => hpair _ (isSlabProfile_average hξ hξF' hD hDF hwm hwinv d₂ hd₁ b ha hR)
      (exists_ae_norm_average_mul_conj_le hξ hξF' hD hDF hu hwu d₂ hd₁ hd₂ hS' hS's a b hR)

end AutomorphicForm.TwistedCentralAverage
p2m_reactivate "P2MW.S_AutomorphicForm_exists_isSlabProfile_eLpNorm_sub_pseudoEisenstein_lt_of_forall_setIntegral_eq_zero_slab.SlabPairingDescent P2MW.S_AutomorphicForm_exists_isSlabProfile_eLpNorm_sub_pseudoEisenstein_lt_of_forall_setIntegral_eq_zero_slab.AutomorphicForm P2MW.S_AutomorphicForm_exists_isSlabProfile_eLpNorm_sub_pseudoEisenstein_lt_of_forall_setIntegral_eq_zero_slab.AutomorphicForm.TwistedCentralAverage"
p2m_reactivate "P2MW.S_AutomorphicForm_exists_isSlabProfile_eLpNorm_sub_pseudoEisenstein_lt_of_forall_setIntegral_eq_zero_slab.SlabPairingDescent P2MW.S_AutomorphicForm_exists_isSlabProfile_eLpNorm_sub_pseudoEisenstein_lt_of_forall_setIntegral_eq_zero_slab.AutomorphicForm"

end
p2m_reactivate "P2MW.S_AutomorphicForm_exists_isSlabProfile_eLpNorm_sub_pseudoEisenstein_lt_of_forall_setIntegral_eq_zero_slab.SlabPairingDescent P2MW.S_AutomorphicForm_exists_isSlabProfile_eLpNorm_sub_pseudoEisenstein_lt_of_forall_setIntegral_eq_zero_slab.AutomorphicForm P2MW.S_AutomorphicForm_exists_isSlabProfile_eLpNorm_sub_pseudoEisenstein_lt_of_forall_setIntegral_eq_zero_slab.AutomorphicForm.TwistedCentralAverage"
end
p2m_reactivate "P2MW.S_AutomorphicForm_exists_isSlabProfile_eLpNorm_sub_pseudoEisenstein_lt_of_forall_setIntegral_eq_zero_slab.SlabPairingDescent P2MW.S_AutomorphicForm_exists_isSlabProfile_eLpNorm_sub_pseudoEisenstein_lt_of_forall_setIntegral_eq_zero_slab.AutomorphicForm P2MW.S_AutomorphicForm_exists_isSlabProfile_eLpNorm_sub_pseudoEisenstein_lt_of_forall_setIntegral_eq_zero_slab.AutomorphicForm.TwistedCentralAverage"

section
section

open MeasureTheory NumberField
open NumberField.AdelicHaar NumberField.AdelicLevel NumberField.AdelicBox
p2m_open "AutomorphicForm P2MW.S_AutomorphicForm_exists_isSlabProfile_eLpNorm_sub_pseudoEisenstein_lt_of_forall_setIntegral_eq_zero_slab.AutomorphicForm"
open scoped Pointwise

attribute [local instance] NumberField.AdelicHaar.glBorel NumberField.AdelicHaar.adeleBorel
attribute [local instance] NumberField.AdelicHaar.borelSpace_glBorel NumberField.AdelicHaar.borelSpace_adeleBorel

noncomputable section

set_option autoImplicit false

namespace AutomorphicForm
p2m_export "AutomorphicForm" "lsXiMemberAt_iff IsAutomorphicFnAt CarrierPins productionPinsOf AdelicGL2 globalPoints centralScalar IsLsXiFunction unipotentGL2 unipotentGL2_coe constantTermIntegrand constantTerm IsSlabProfile pseudoEisenstein pseudoEisenstein_apply isSlabProfile_zero pseudoEisenstein_zero borelSubgroup mem_borelSubgroup_iff globalPoints_apply gl2Weyl adelicWeyl WindowedSiegel.rowNormSq WindowedSiegel.localHeight WindowedSiegel.archHeight WindowedSiegel.archHeight_scalar_entries_mul finite_support_pseudoEisenstein_summand isAutomorphicFnAt_pseudoEisenstein_slab aestronglyMeasurable_adelicGLHaar_of_isAutomorphicFnAt_slab setIntegral_pseudoEisenstein_mul_conj_eq_setIntegral_rationalTorusUnipotentQuotient_slab rationalTorusUnipotent RationalTorusUnipotentQuotient rationalTorusUnipotentHaar rationalTorusUnipotentQuotientMeasure toAdelicUnipotent adelicMaximalCompact isCompact_adelicMaximalCompact maximalCompactHaar constantTerm_adelicBox_globalPoints_mul_of_mem_borelSubgroup constantTerm_adelicBox_unipotentGL2_mul continuous_unipotentGL2 exists_isFundamentalDomain_globalPoints_range exists_lintegral_rationalTorusUnipotentQuotientMeasure_eq_mul_setLIntegral_iwasawa ideleNorm_det_globalPoints isClosed_rationalTorusUnipotent isFundamentalDomain_boxSheet_rationalTorusUnipotent isHaarMeasure_rationalTorusUnipotentHaar_and_isMulRightInvariant"
namespace PseudoEisensteinDensity
namespace SlabToGroup
p2m_open "AutomorphicForm"

variable (F : Type) [Field F] [NumberField F]

private abbrev _root_.AutomorphicForm.PseudoEisensteinDensity.SlabToGroup.slab (d₁ d₂ : ℝ) : Set (AdelicGL2 (𝓞 F) F) :=
  {g | NumberField.TateGlobal.ideleNorm F (Matrix.GeneralLinearGroup.det g) ∈ Set.Icc d₁ d₂}

p2m_export "AutomorphicForm.PseudoEisensteinDensity.SlabToGroup" "slab"

private abbrev slabHaar (d₁ d₂ : ℝ) : Measure (AdelicGL2 (𝓞 F) F) :=
  (adelicGLHaar (Fin 2) (𝓞 F) F).restrict (slab F d₁ d₂)

private abbrev pins (Φ : Set (AdelicGL2 (𝓞 F) F)) : CarrierPins F :=
  productionPinsOf F Φ (fun N => levelOne (𝓞 F) F N) (fun v => heckeGen (𝓞 F) F v) (adelicBox F)

private abbrev Γ : Subgroup (AdelicGL2 (𝓞 F) F) := (globalPoints (𝓞 F) F).range

private theorem central_transform_of_isAutomorphicFnAt (Φ : Set (AdelicGL2 (𝓞 F) F)) (ξ : (pins F Φ).Z →* ℂˣ)
    {u : AdelicGL2 (𝓞 F) F → ℂ} (hu : IsAutomorphicFnAt F (pins F Φ) ξ u) (z : (pins F Φ).Z)
    (g : AdelicGL2 (𝓞 F) F) :
    u (centralScalar (𝓞 F) F (z : (AdeleRing (𝓞 F) F)ˣ) * g) = ((ξ z : ℂˣ) : ℂ) * u g :=
  ((lsXiMemberAt_iff (𝓞 F) F (pins F Φ).μ (pins F Φ).Z ξ (pins F Φ).D u).mp hu).1.central_transform z g

private theorem centralScalar_mul_unipotentGL2_comm (z : (AdeleRing (𝓞 F) F)ˣ) (q : AdeleRing (𝓞 F) F) :
    centralScalar (𝓞 F) F z * unipotentGL2 q = unipotentGL2 q * centralScalar (𝓞 F) F z := by
  apply Units.ext
  simp only [Units.val_mul, centralScalar, Matrix.GeneralLinearGroup.scalar, Units.coe_map, MonoidHom.coe_coe,
    RingHom.toMonoidHom_eq_coe]
  exact (Matrix.scalar_commute (z : AdeleRing (𝓞 F) F) (fun _ => Commute.all _ _) _).eq

private theorem constantTerm_centralScalar_mul (Φ : Set (AdelicGL2 (𝓞 F) F)) (ξ : (pins F Φ).Z →* ℂˣ)
    (u : AdelicGL2 (𝓞 F) F → ℂ)
    (hcentral : ∀ (z : (pins F Φ).Z) (g : AdelicGL2 (𝓞 F) F),
      u (centralScalar (𝓞 F) F (z : (AdeleRing (𝓞 F) F)ˣ) * g) = ((ξ z : ℂˣ) : ℂ) * u g)
    (z : (pins F Φ).Z) (g : AdelicGL2 (𝓞 F) F) :
    constantTerm (pins F Φ).ν unipotentGL2 u (centralScalar (𝓞 F) F (z : (AdeleRing (𝓞 F) F)ˣ) * g)
      = ((ξ z : ℂˣ) : ℂ) * constantTerm (pins F Φ).ν unipotentGL2 u g := by
  simp only [constantTerm, constantTermIntegrand]
  rw [← integral_const_mul]
  congr 1
  funext q
  rw [← mul_assoc, ← centralScalar_mul_unipotentGL2_comm, mul_assoc, hcentral]

private theorem ae_haar_of_ae_slabHaar_of_central (d₁ d₂ : ℝ) (Φ : Set (AdelicGL2 (𝓞 F) F))
    (hcover : ∃ z : ℕ → (pins F Φ).Z, ∀ᵐ g ∂(adelicGLHaar (Fin 2) (𝓞 F) F), ∃ n,
        centralScalar (𝓞 F) F ((z n : (AdeleRing (𝓞 F) F)ˣ))⁻¹ * g ∈ slab F d₁ d₂)
    (P : AdelicGL2 (𝓞 F) F → Prop)
    (hP : ∀ w : (AdeleRing (𝓞 F) F)ˣ, w ∈ (pins F Φ).Z → ∀ g : AdelicGL2 (𝓞 F) F,
      P (centralScalar (𝓞 F) F w * g) → P g)
    (hslabae : ∀ᵐ g ∂(slabHaar F d₁ d₂), P g) : ∀ᵐ g ∂(adelicGLHaar (Fin 2) (𝓞 F) F), P g := by
  obtain ⟨z, hz⟩ := hcover
  haveI := isHaarMeasure_adelicGLHaar (Fin 2) (𝓞 F) F
  have h1 : ∀ᵐ g ∂(adelicGLHaar (Fin 2) (𝓞 F) F), g ∈ slab F d₁ d₂ → P g := ae_imp_of_ae_restrict hslabae
  have h2 : ∀ n : ℕ, ∀ᵐ g ∂(adelicGLHaar (Fin 2) (𝓞 F) F),
      centralScalar (𝓞 F) F ((z n : (AdeleRing (𝓞 F) F)ˣ))⁻¹ * g ∈ slab F d₁ d₂ →
        P (centralScalar (𝓞 F) F ((z n : (AdeleRing (𝓞 F) F)ˣ))⁻¹ * g) := by
    intro n
    have hmp := measurePreserving_mul_left (adelicGLHaar (Fin 2) (𝓞 F) F)
      (centralScalar (𝓞 F) F ((z n : (AdeleRing (𝓞 F) F)ˣ))⁻¹)
    have hq := hmp.quasiMeasurePreserving
    exact hq.ae (p := fun g => g ∈ slab F d₁ d₂ → P g) h1
  filter_upwards [hz, ae_all_iff.mpr h2] with g hg hg'
  obtain ⟨n, hn⟩ := hg
  exact hP _ ((pins F Φ).Z.inv_mem (z n).2) g (hg' n hn)

private theorem ae_constantTerm_eq_zero_of_ae_restrict_slab
    (d₁ d₂ : ℝ) (Φ : Set (AdelicGL2 (𝓞 F) F))
    (hcover : ∃ z : ℕ → (pins F Φ).Z, ∀ᵐ g ∂(adelicGLHaar (Fin 2) (𝓞 F) F), ∃ n,
        centralScalar (𝓞 F) F ((z n : (AdeleRing (𝓞 F) F)ˣ))⁻¹ * g ∈ slab F d₁ d₂)
    (ξ : (pins F Φ).Z →* ℂˣ) (u : AdelicGL2 (𝓞 F) F → ℂ)
    (hcentral : ∀ (z : (pins F Φ).Z) (g : AdelicGL2 (𝓞 F) F),
      u (centralScalar (𝓞 F) F (z : (AdeleRing (𝓞 F) F)ˣ) * g) = ((ξ z : ℂˣ) : ℂ) * u g)
    (hslabae : ∀ᵐ g ∂(slabHaar F d₁ d₂), constantTerm (pins F Φ).ν unipotentGL2 u g = 0) :
    ∀ᵐ g ∂(adelicGLHaar (Fin 2) (𝓞 F) F), constantTerm (pins F Φ).ν unipotentGL2 u g = 0 := by
  refine ae_haar_of_ae_slabHaar_of_central F d₁ d₂ Φ hcover _ ?_ hslabae
  intro w hw g h
  have h' : constantTerm (pins F Φ).ν unipotentGL2 u (centralScalar (𝓞 F) F w * g)
      = ((ξ ⟨w, hw⟩ : ℂˣ) : ℂ) * constantTerm (pins F Φ).ν unipotentGL2 u g :=
    constantTerm_centralScalar_mul F Φ ξ u hcentral ⟨w, hw⟩ g
  rw [h'] at h
  exact (mul_eq_zero.mp h).resolve_left (Units.ne_zero _)

private theorem ideleNorm_one_eq : NumberField.TateGlobal.ideleNorm F 1 = 1 := by
  have h := NumberField.TateGlobal.ideleNorm_mul (F := F) 1 1
  rw [one_mul] at h
  have h' : NumberField.TateGlobal.ideleNorm F 1 * 1
      = NumberField.TateGlobal.ideleNorm F 1 * NumberField.TateGlobal.ideleNorm F 1 := by
    rw [mul_one]
    exact h
  exact (mul_left_cancel₀ (NumberField.TateGlobal.ideleNorm_pos (F := F) 1).ne' h').symm

private theorem ideleNorm_inv_eq (w : (AdeleRing (𝓞 F) F)ˣ) :
    NumberField.TateGlobal.ideleNorm F w⁻¹ = (NumberField.TateGlobal.ideleNorm F w)⁻¹ := by
  have h := NumberField.TateGlobal.ideleNorm_mul (F := F) w w⁻¹
  rw [mul_inv_cancel, ideleNorm_one_eq] at h
  exact eq_inv_of_mul_eq_one_right h.symm

private theorem det_centralScalar_eq (w : (AdeleRing (𝓞 F) F)ˣ) :
    Matrix.GeneralLinearGroup.det (centralScalar (𝓞 F) F w) = w ^ 2 := by
  rw [show centralScalar (𝓞 F) F = Matrix.GeneralLinearGroup.scalar (Fin 2) from rfl,
    Matrix.GeneralLinearGroup.det_scalar, Fintype.card_fin]

private theorem ideleNorm_det_centralScalar_inv_mul (w : (AdeleRing (𝓞 F) F)ˣ) (g : AdelicGL2 (𝓞 F) F) :
    NumberField.TateGlobal.ideleNorm F (Matrix.GeneralLinearGroup.det (centralScalar (𝓞 F) F w⁻¹ * g))
      = (NumberField.TateGlobal.ideleNorm F w)⁻¹ * (NumberField.TateGlobal.ideleNorm F w)⁻¹
          * NumberField.TateGlobal.ideleNorm F (Matrix.GeneralLinearGroup.det g) := by
  rw [map_mul, NumberField.TateGlobal.ideleNorm_mul, det_centralScalar_eq, sq, NumberField.TateGlobal.ideleNorm_mul,
    ideleNorm_inv_eq]

private theorem globalPoints_mul_mem_slab_iff (a b : ℝ)
    (hpf : ∀ x : Matrix.GeneralLinearGroup (Fin 2) F,
      NumberField.TateGlobal.ideleNorm F (Matrix.GeneralLinearGroup.det (globalPoints (𝓞 F) F x)) = 1)
    (γ : Γ F) (g : AdelicGL2 (𝓞 F) F) : (γ : AdelicGL2 (𝓞 F) F) * g ∈ slab F a b ↔ g ∈ slab F a b := by
  obtain ⟨x, hx⟩ := γ.2
  have hdet : NumberField.TateGlobal.ideleNorm F (Matrix.GeneralLinearGroup.det ((γ : AdelicGL2 (𝓞 F) F) * g))
      = NumberField.TateGlobal.ideleNorm F (Matrix.GeneralLinearGroup.det g) := by
    rw [map_mul, NumberField.TateGlobal.ideleNorm_mul, ← hx, hpf x, one_mul]
  show NumberField.TateGlobal.ideleNorm F (Matrix.GeneralLinearGroup.det ((γ : AdelicGL2 (𝓞 F) F) * g)) ∈ Set.Icc a b ↔
    NumberField.TateGlobal.ideleNorm F (Matrix.GeneralLinearGroup.det g) ∈ Set.Icc a b
  rw [hdet]

private theorem smulInvariantMeasure_slabHaar (a b : ℝ) (hslab : MeasurableSet (slab F a b))
    (hpf : ∀ x : Matrix.GeneralLinearGroup (Fin 2) F,
      NumberField.TateGlobal.ideleNorm F (Matrix.GeneralLinearGroup.det (globalPoints (𝓞 F) F x)) = 1) :
    SMulInvariantMeasure (Γ F) (AdelicGL2 (𝓞 F) F) (slabHaar F a b) := by
  have _ := hslab
  haveI := isHaarMeasure_adelicGLHaar (Fin 2) (𝓞 F) F
  refine ⟨fun γ s hs => ?_⟩
  have hpre : (fun x : AdelicGL2 (𝓞 F) F => γ • x) ⁻¹' slab F a b = slab F a b := by
    ext g
    exact globalPoints_mul_mem_slab_iff F a b hpf γ g
  have hmeas : MeasurableSet ((fun x : AdelicGL2 (𝓞 F) F => γ • x) ⁻¹' s) :=
    measurable_const_mul (γ : AdelicGL2 (𝓞 F) F) hs
  calc slabHaar F a b ((fun x : AdelicGL2 (𝓞 F) F => γ • x) ⁻¹' s)
      = adelicGLHaar (Fin 2) (𝓞 F) F ((fun x : AdelicGL2 (𝓞 F) F => γ • x) ⁻¹' s ∩ slab F a b) :=
        Measure.restrict_apply hmeas
    _ = adelicGLHaar (Fin 2) (𝓞 F) F ((fun x : AdelicGL2 (𝓞 F) F => γ • x) ⁻¹' (s ∩ slab F a b)) := by
        rw [Set.preimage_inter, hpre]
    _ = adelicGLHaar (Fin 2) (𝓞 F) F (s ∩ slab F a b) :=
        measure_preimage_mul (adelicGLHaar (Fin 2) (𝓞 F) F) (γ : AdelicGL2 (𝓞 F) F) _
    _ = slabHaar F a b s := (Measure.restrict_apply hs).symm

private theorem exists_central_cover_slab (d₁ d₂ : ℝ) (hd₁ : 0 < d₁) (hd : d₁ < d₂) (Φ : Set (AdelicGL2 (𝓞 F) F))
    (hnorm : ∀ t : ℝ, 0 < t → ∃ z : (AdeleRing (𝓞 F) F)ˣ, NumberField.TateGlobal.ideleNorm F z = t) :
    ∃ z : ℕ → (pins F Φ).Z, ∀ᵐ g ∂(adelicGLHaar (Fin 2) (𝓞 F) F), ∃ n,
      centralScalar (𝓞 F) F ((z n : (AdeleRing (𝓞 F) F)ˣ))⁻¹ * g ∈ slab F d₁ d₂ := by
  have hρ0 : 0 < d₂ / d₁ := div_pos (hd₁.trans hd) hd₁
  have hρ1 : 1 < d₂ / d₁ := (one_lt_div hd₁).mpr hd
  have hρd : d₂ / d₁ * d₁ = d₂ := div_mul_cancel₀ d₂ hd₁.ne'
  choose zk hzk using fun k : ℤ => hnorm (Real.sqrt ((d₂ / d₁) ^ k)) (Real.sqrt_pos.mpr (zpow_pos hρ0 k))
  have hmem : ∀ w : (AdeleRing (𝓞 F) F)ˣ, w ∈ (pins F Φ).Z := fun w => Subgroup.mem_top w
  refine ⟨fun n => ⟨zk ((Denumerable.eqv ℤ).symm n), hmem _⟩, Filter.Eventually.of_forall fun g => ?_⟩
  have ht : 0 < NumberField.TateGlobal.ideleNorm F (Matrix.GeneralLinearGroup.det g) :=
    NumberField.TateGlobal.ideleNorm_pos (F := F) _
  obtain ⟨k, hk⟩ := exists_mem_Ico_zpow (div_pos ht hd₁) hρ1
  refine ⟨Denumerable.eqv ℤ k, ?_⟩
  simp only [Equiv.symm_apply_apply]
  have hρk : 0 < (d₂ / d₁) ^ k := zpow_pos hρ0 k
  have hval : NumberField.TateGlobal.ideleNorm F (Matrix.GeneralLinearGroup.det (centralScalar (𝓞 F) F (zk k)⁻¹ * g))
      = NumberField.TateGlobal.ideleNorm F (Matrix.GeneralLinearGroup.det g) / (d₂ / d₁) ^ k := by
    rw [ideleNorm_det_centralScalar_inv_mul, hzk, ← mul_inv, Real.mul_self_sqrt hρk.le, inv_mul_eq_div]
  show NumberField.TateGlobal.ideleNorm F (Matrix.GeneralLinearGroup.det (centralScalar (𝓞 F) F (zk k)⁻¹ * g))
    ∈ Set.Icc d₁ d₂
  rw [hval]
  have h1 : (d₂ / d₁) ^ k * d₁ ≤ NumberField.TateGlobal.ideleNorm F (Matrix.GeneralLinearGroup.det g) :=
    (le_div_iff₀ hd₁).mp hk.1
  have h2 : NumberField.TateGlobal.ideleNorm F (Matrix.GeneralLinearGroup.det g) < (d₂ / d₁) ^ (k + 1) * d₁ :=
    (div_lt_iff₀ hd₁).mp hk.2
  rw [zpow_add_one₀ hρ0.ne', mul_assoc, hρd] at h2
  constructor
  · rw [le_div_iff₀ hρk]
    linarith
  · rw [div_le_iff₀ hρk]
    linarith

private theorem ae_slabHaar_eq_zero_of_ae_restrict_inter (d₁ d₂ : ℝ) (Γ' : Subgroup (AdelicGL2 (𝓞 F) F))
    [Countable Γ'] (S : Set (AdelicGL2 (𝓞 F) F))
    (hS : IsFundamentalDomain Γ' S (adelicGLHaar (Fin 2) (𝓞 F) F))
    (hΓslab : ∀ γ : Γ', ∀ g : AdelicGL2 (𝓞 F) F, g ∈ slab F d₁ d₂ → (γ : AdelicGL2 (𝓞 F) F) * g ∈ slab F d₁ d₂)
    (c : AdelicGL2 (𝓞 F) F → ℂ) (hc : ∀ γ : Γ', ∀ g : AdelicGL2 (𝓞 F) F, c ((γ : AdelicGL2 (𝓞 F) F) * g) = c g)
    (h0 : ∀ᵐ g ∂((adelicGLHaar (Fin 2) (𝓞 F) F).restrict (S ∩ slab F d₁ d₂)), c g = 0) :
    ∀ᵐ g ∂(slabHaar F d₁ d₂), c g = 0 := by
  haveI := isHaarMeasure_adelicGLHaar (Fin 2) (𝓞 F) F
  have h1 : ∀ᵐ g ∂(adelicGLHaar (Fin 2) (𝓞 F) F), g ∈ S ∩ slab F d₁ d₂ → c g = 0 := ae_imp_of_ae_restrict h0
  have h2 : ∀ γ : Γ', ∀ᵐ g ∂(adelicGLHaar (Fin 2) (𝓞 F) F),
      (γ : AdelicGL2 (𝓞 F) F) * g ∈ S ∩ slab F d₁ d₂ → c ((γ : AdelicGL2 (𝓞 F) F) * g) = 0 := fun γ =>
    (measurePreserving_mul_left (adelicGLHaar (Fin 2) (𝓞 F) F)
      (γ : AdelicGL2 (𝓞 F) F)).quasiMeasurePreserving.ae (p := fun g => g ∈ S ∩ slab F d₁ d₂ → c g = 0) h1
  rw [ae_restrict_iff' (NumberField.TateGlobal.measurableSet_setOf_ideleNorm_det_mem_Icc F d₁ d₂)]
  filter_upwards [hS.ae_covers, ae_all_iff.mpr h2] with g hg hg' hgslab
  obtain ⟨γ, hγ⟩ := hg
  have hmem : (γ : AdelicGL2 (𝓞 F) F) * g ∈ S ∩ slab F d₁ d₂ := ⟨(by first | simpa using hγ | (simpa using (hγ :)) | (simpa [Function.comp_def] using hγ) | exact hγ | (have h__ := hγ; (try simp at h__); (try simp); exact h__)), hΓslab γ g hgslab⟩
  have h := hg' γ hmem
  rwa [hc γ g] at h

private theorem ae_constantTerm_eq_zero_of_ae_restrict_inter (d₁ d₂ : ℝ) (hd₁ : 0 < d₁) (hd : d₁ < d₂)
    (Φ : Set (AdelicGL2 (𝓞 F) F)) (ξ : (pins F Φ).Z →* ℂˣ) (u : AdelicGL2 (𝓞 F) F → ℂ)
    (hu : IsAutomorphicFnAt F (pins F Φ) ξ u)
    (Γ' : Subgroup (AdelicGL2 (𝓞 F) F)) [Countable Γ'] (hΓ' : Γ' ≤ Γ F)
    (S : Set (AdelicGL2 (𝓞 F) F)) (hS : IsFundamentalDomain Γ' S (adelicGLHaar (Fin 2) (𝓞 F) F))
    (hcinv : ∀ γ : Γ', ∀ g : AdelicGL2 (𝓞 F) F,
      constantTerm (pins F Φ).ν unipotentGL2 u ((γ : AdelicGL2 (𝓞 F) F) * g)
        = constantTerm (pins F Φ).ν unipotentGL2 u g)
    (h0 : ∀ᵐ g ∂((adelicGLHaar (Fin 2) (𝓞 F) F).restrict (S ∩ slab F d₁ d₂)),
      constantTerm (pins F Φ).ν unipotentGL2 u g = 0) :
    ∀ᵐ g ∂(adelicGLHaar (Fin 2) (𝓞 F) F), constantTerm (pins F Φ).ν unipotentGL2 u g = 0 := by
  have hnorm : ∀ t : ℝ, 0 < t → ∃ z : (AdeleRing (𝓞 F) F)ˣ, NumberField.TateGlobal.ideleNorm F z = t := by
    intro t ht
    obtain ⟨s, -, hs, -⟩ := NumberField.TateGlobal.exists_continuous_monoidHom_ideleNorm_apply_eq F
    have hr0 : (0 : NNReal) < ⟨t, ht.le⟩ := by exact_mod_cast ht
    refine ⟨s (Units.mk0 ⟨t, ht.le⟩ hr0.ne'), ?_⟩
    exact (hs _).trans rfl
  refine ae_constantTerm_eq_zero_of_ae_restrict_slab F d₁ d₂ Φ (exists_central_cover_slab F d₁ d₂ hd₁ hd Φ hnorm)
    ξ u (central_transform_of_isAutomorphicFnAt F Φ ξ hu) ?_
  refine ae_slabHaar_eq_zero_of_ae_restrict_inter F d₁ d₂ Γ' S hS ?_ _ hcinv h0
  intro γ g hg
  exact (globalPoints_mul_mem_slab_iff F d₁ d₂ (fun x => ideleNorm_det_globalPoints x) ⟨γ, hΓ' γ.2⟩ g).2 hg

end AutomorphicForm.PseudoEisensteinDensity.SlabToGroup
p2m_reactivate "P2MW.S_AutomorphicForm_exists_isSlabProfile_eLpNorm_sub_pseudoEisenstein_lt_of_forall_setIntegral_eq_zero_slab.SlabPairingDescent P2MW.S_AutomorphicForm_exists_isSlabProfile_eLpNorm_sub_pseudoEisenstein_lt_of_forall_setIntegral_eq_zero_slab.AutomorphicForm P2MW.S_AutomorphicForm_exists_isSlabProfile_eLpNorm_sub_pseudoEisenstein_lt_of_forall_setIntegral_eq_zero_slab.AutomorphicForm.TwistedCentralAverage"
p2m_reactivate "P2MW.S_AutomorphicForm_exists_isSlabProfile_eLpNorm_sub_pseudoEisenstein_lt_of_forall_setIntegral_eq_zero_slab.SlabPairingDescent P2MW.S_AutomorphicForm_exists_isSlabProfile_eLpNorm_sub_pseudoEisenstein_lt_of_forall_setIntegral_eq_zero_slab.AutomorphicForm P2MW.S_AutomorphicForm_exists_isSlabProfile_eLpNorm_sub_pseudoEisenstein_lt_of_forall_setIntegral_eq_zero_slab.AutomorphicForm.TwistedCentralAverage"
p2m_reactivate "P2MW.S_AutomorphicForm_exists_isSlabProfile_eLpNorm_sub_pseudoEisenstein_lt_of_forall_setIntegral_eq_zero_slab.SlabPairingDescent P2MW.S_AutomorphicForm_exists_isSlabProfile_eLpNorm_sub_pseudoEisenstein_lt_of_forall_setIntegral_eq_zero_slab.AutomorphicForm P2MW.S_AutomorphicForm_exists_isSlabProfile_eLpNorm_sub_pseudoEisenstein_lt_of_forall_setIntegral_eq_zero_slab.AutomorphicForm.TwistedCentralAverage"

end
p2m_reactivate "P2MW.S_AutomorphicForm_exists_isSlabProfile_eLpNorm_sub_pseudoEisenstein_lt_of_forall_setIntegral_eq_zero_slab.SlabPairingDescent P2MW.S_AutomorphicForm_exists_isSlabProfile_eLpNorm_sub_pseudoEisenstein_lt_of_forall_setIntegral_eq_zero_slab.AutomorphicForm P2MW.S_AutomorphicForm_exists_isSlabProfile_eLpNorm_sub_pseudoEisenstein_lt_of_forall_setIntegral_eq_zero_slab.AutomorphicForm.TwistedCentralAverage"

end
p2m_reactivate "P2MW.S_AutomorphicForm_exists_isSlabProfile_eLpNorm_sub_pseudoEisenstein_lt_of_forall_setIntegral_eq_zero_slab.SlabPairingDescent P2MW.S_AutomorphicForm_exists_isSlabProfile_eLpNorm_sub_pseudoEisenstein_lt_of_forall_setIntegral_eq_zero_slab.AutomorphicForm P2MW.S_AutomorphicForm_exists_isSlabProfile_eLpNorm_sub_pseudoEisenstein_lt_of_forall_setIntegral_eq_zero_slab.AutomorphicForm.TwistedCentralAverage"
end
p2m_reactivate "P2MW.S_AutomorphicForm_exists_isSlabProfile_eLpNorm_sub_pseudoEisenstein_lt_of_forall_setIntegral_eq_zero_slab.SlabPairingDescent P2MW.S_AutomorphicForm_exists_isSlabProfile_eLpNorm_sub_pseudoEisenstein_lt_of_forall_setIntegral_eq_zero_slab.AutomorphicForm P2MW.S_AutomorphicForm_exists_isSlabProfile_eLpNorm_sub_pseudoEisenstein_lt_of_forall_setIntegral_eq_zero_slab.AutomorphicForm.TwistedCentralAverage"

section

set_option autoImplicit false

open MeasureTheory

namespace AutomorphicForm
p2m_export "AutomorphicForm" "lsXiMemberAt_iff IsAutomorphicFnAt CarrierPins productionPinsOf AdelicGL2 globalPoints centralScalar IsLsXiFunction unipotentGL2 unipotentGL2_coe constantTermIntegrand constantTerm IsSlabProfile pseudoEisenstein pseudoEisenstein_apply isSlabProfile_zero pseudoEisenstein_zero borelSubgroup mem_borelSubgroup_iff globalPoints_apply gl2Weyl adelicWeyl WindowedSiegel.rowNormSq WindowedSiegel.localHeight WindowedSiegel.archHeight WindowedSiegel.archHeight_scalar_entries_mul finite_support_pseudoEisenstein_summand isAutomorphicFnAt_pseudoEisenstein_slab aestronglyMeasurable_adelicGLHaar_of_isAutomorphicFnAt_slab setIntegral_pseudoEisenstein_mul_conj_eq_setIntegral_rationalTorusUnipotentQuotient_slab rationalTorusUnipotent RationalTorusUnipotentQuotient rationalTorusUnipotentHaar rationalTorusUnipotentQuotientMeasure toAdelicUnipotent adelicMaximalCompact isCompact_adelicMaximalCompact maximalCompactHaar constantTerm_adelicBox_globalPoints_mul_of_mem_borelSubgroup constantTerm_adelicBox_unipotentGL2_mul continuous_unipotentGL2 exists_isFundamentalDomain_globalPoints_range exists_lintegral_rationalTorusUnipotentQuotientMeasure_eq_mul_setLIntegral_iwasawa ideleNorm_det_globalPoints isClosed_rationalTorusUnipotent isFundamentalDomain_boxSheet_rationalTorusUnipotent isHaarMeasure_rationalTorusUnipotentHaar_and_isMulRightInvariant"
namespace PseudoEisensteinDensity
namespace Inputs
p2m_open "AutomorphicForm"

variable {G : Type*} [Group G] [MeasurableSpace G] [MeasurableMul G]

private theorem measurableSet_setOf_forall_mul_eq (Γ : Subgroup G) [Countable Γ] {f : G → ℂ} (hf : Measurable f) :
    MeasurableSet {g : G | ∀ γ : Γ, f ((γ : G) * g) = f g} := by
  have : {g : G | ∀ γ : Γ, f ((γ : G) * g) = f g} = ⋂ γ : Γ, {g : G | f ((γ : G) * g) = f g} := by
    ext g; simp
  rw [this]
  exact MeasurableSet.iInter fun γ => measurableSet_eq_fun (hf.comp (measurable_const_mul (γ : G))) hf

omit [MeasurableSpace G] [MeasurableMul G] in

private theorem mul_mem_setOf_forall_mul_eq_iff (Γ : Subgroup G) (f : G → ℂ) (δ : Γ) (g : G) :
    (δ : G) * g ∈ {g : G | ∀ γ : Γ, f ((γ : G) * g) = f g} ↔ g ∈ {g : G | ∀ γ : Γ, f ((γ : G) * g) = f g} := by
  simp only [Set.mem_setOf_eq]
  constructor
  · intro h γ
    have h₁ := h (γ * δ⁻¹)
    have h₂ := h δ⁻¹
    simp only [Subgroup.coe_mul, Subgroup.coe_inv, mul_assoc, inv_mul_cancel_left] at h₁ h₂
    rw [h₁, h₂]
  · intro h γ
    have h₁ := h (γ * δ)
    have h₂ := h δ
    simp only [Subgroup.coe_mul, mul_assoc] at h₁ h₂
    rw [h₁, h₂]

private theorem exists_measurable_forall_mul_eq_and_ae_eq (μ : Measure G) [μ.IsMulLeftInvariant] (Γ : Subgroup G)
    [Countable Γ] (f : G → ℂ) (hfΓ : ∀ γ ∈ Γ, ∀ g : G, f (γ * g) = f g) (hf : AEStronglyMeasurable f μ) :
    ∃ f' : G → ℂ, Measurable f' ∧ (∀ γ ∈ Γ, ∀ g : G, f' (γ * g) = f' g) ∧ f' =ᵐ[μ] f := by
  set f₁ : G → ℂ := hf.mk f with hf₁
  have hf₁m : Measurable f₁ := hf.measurable_mk
  have hf₁e : f₁ =ᵐ[μ] f := hf.ae_eq_mk.symm
  set E : Set G := {g : G | ∀ γ : Γ, f₁ ((γ : G) * g) = f₁ g} with hE
  have hEm : MeasurableSet E := measurableSet_setOf_forall_mul_eq Γ hf₁m
  refine ⟨E.indicator f₁, hf₁m.indicator hEm, ?_, ?_⟩
  · intro γ hγ g
    by_cases hg : g ∈ E
    · have hγg : γ * g ∈ E := (mul_mem_setOf_forall_mul_eq_iff Γ f₁ ⟨γ, hγ⟩ g).2 hg
      rw [Set.indicator_of_mem hγg, Set.indicator_of_mem hg]
      exact hg ⟨γ, hγ⟩
    · have hγg : γ * g ∉ E := fun h => hg ((mul_mem_setOf_forall_mul_eq_iff Γ f₁ ⟨γ, hγ⟩ g).1 h)
      rw [Set.indicator_of_notMem hγg, Set.indicator_of_notMem hg]
  ·
    have hγ : ∀ γ : Γ, (fun g => f₁ ((γ : G) * g)) =ᵐ[μ] fun g => f ((γ : G) * g) := fun γ =>
      (measurePreserving_mul_left μ (γ : G)).quasiMeasurePreserving.ae_eq hf₁e
    have hall : ∀ᵐ g ∂μ, ∀ γ : Γ, f₁ ((γ : G) * g) = f ((γ : G) * g) := ae_all_iff.2 hγ
    filter_upwards [hall, hf₁e] with g hg hg₁
    have hgE : g ∈ E := fun γ => by rw [hg γ, hfΓ γ γ.2 g, hg₁]
    rw [Set.indicator_of_mem hgE, hg₁]

end AutomorphicForm.PseudoEisensteinDensity.Inputs
p2m_reactivate "P2MW.S_AutomorphicForm_exists_isSlabProfile_eLpNorm_sub_pseudoEisenstein_lt_of_forall_setIntegral_eq_zero_slab.SlabPairingDescent P2MW.S_AutomorphicForm_exists_isSlabProfile_eLpNorm_sub_pseudoEisenstein_lt_of_forall_setIntegral_eq_zero_slab.AutomorphicForm P2MW.S_AutomorphicForm_exists_isSlabProfile_eLpNorm_sub_pseudoEisenstein_lt_of_forall_setIntegral_eq_zero_slab.AutomorphicForm.TwistedCentralAverage"
p2m_reactivate "P2MW.S_AutomorphicForm_exists_isSlabProfile_eLpNorm_sub_pseudoEisenstein_lt_of_forall_setIntegral_eq_zero_slab.SlabPairingDescent P2MW.S_AutomorphicForm_exists_isSlabProfile_eLpNorm_sub_pseudoEisenstein_lt_of_forall_setIntegral_eq_zero_slab.AutomorphicForm P2MW.S_AutomorphicForm_exists_isSlabProfile_eLpNorm_sub_pseudoEisenstein_lt_of_forall_setIntegral_eq_zero_slab.AutomorphicForm.TwistedCentralAverage"
p2m_reactivate "P2MW.S_AutomorphicForm_exists_isSlabProfile_eLpNorm_sub_pseudoEisenstein_lt_of_forall_setIntegral_eq_zero_slab.SlabPairingDescent P2MW.S_AutomorphicForm_exists_isSlabProfile_eLpNorm_sub_pseudoEisenstein_lt_of_forall_setIntegral_eq_zero_slab.AutomorphicForm P2MW.S_AutomorphicForm_exists_isSlabProfile_eLpNorm_sub_pseudoEisenstein_lt_of_forall_setIntegral_eq_zero_slab.AutomorphicForm.TwistedCentralAverage"

section

open MeasureTheory NumberField
open NumberField.AdelicHaar NumberField.AdelicLevel NumberField.AdelicBox
p2m_open "AutomorphicForm P2MW.S_AutomorphicForm_exists_isSlabProfile_eLpNorm_sub_pseudoEisenstein_lt_of_forall_setIntegral_eq_zero_slab.AutomorphicForm"
open scoped Pointwise

attribute [local instance] NumberField.AdelicHaar.glBorel NumberField.AdelicHaar.adeleBorel
attribute [local instance] NumberField.AdelicHaar.borelSpace_glBorel NumberField.AdelicHaar.borelSpace_adeleBorel

noncomputable section

namespace AutomorphicForm
p2m_export "AutomorphicForm" "lsXiMemberAt_iff IsAutomorphicFnAt CarrierPins productionPinsOf AdelicGL2 globalPoints centralScalar IsLsXiFunction unipotentGL2 unipotentGL2_coe constantTermIntegrand constantTerm IsSlabProfile pseudoEisenstein pseudoEisenstein_apply isSlabProfile_zero pseudoEisenstein_zero borelSubgroup mem_borelSubgroup_iff globalPoints_apply gl2Weyl adelicWeyl WindowedSiegel.rowNormSq WindowedSiegel.localHeight WindowedSiegel.archHeight WindowedSiegel.archHeight_scalar_entries_mul finite_support_pseudoEisenstein_summand isAutomorphicFnAt_pseudoEisenstein_slab aestronglyMeasurable_adelicGLHaar_of_isAutomorphicFnAt_slab setIntegral_pseudoEisenstein_mul_conj_eq_setIntegral_rationalTorusUnipotentQuotient_slab rationalTorusUnipotent RationalTorusUnipotentQuotient rationalTorusUnipotentHaar rationalTorusUnipotentQuotientMeasure toAdelicUnipotent adelicMaximalCompact isCompact_adelicMaximalCompact maximalCompactHaar constantTerm_adelicBox_globalPoints_mul_of_mem_borelSubgroup constantTerm_adelicBox_unipotentGL2_mul continuous_unipotentGL2 exists_isFundamentalDomain_globalPoints_range exists_lintegral_rationalTorusUnipotentQuotientMeasure_eq_mul_setLIntegral_iwasawa ideleNorm_det_globalPoints isClosed_rationalTorusUnipotent isFundamentalDomain_boxSheet_rationalTorusUnipotent isHaarMeasure_rationalTorusUnipotentHaar_and_isMulRightInvariant"
namespace PseudoEisensteinDensity
namespace Inputs
p2m_open "AutomorphicForm"

variable (F : Type) [Field F] [NumberField F]

private abbrev _root_.AutomorphicForm.PseudoEisensteinDensity.Inputs.slab (d₁ d₂ : ℝ) : Set (AdelicGL2 (𝓞 F) F) :=
  {g | NumberField.TateGlobal.ideleNorm F (Matrix.GeneralLinearGroup.det g) ∈ Set.Icc d₁ d₂}

p2m_export "AutomorphicForm.PseudoEisensteinDensity.Inputs" "slab"

private abbrev slabHaar (d₁ d₂ : ℝ) : Measure (AdelicGL2 (𝓞 F) F) :=
  (adelicGLHaar (Fin 2) (𝓞 F) F).restrict (slab F d₁ d₂)

private abbrev pins (Φ : Set (AdelicGL2 (𝓞 F) F)) : CarrierPins F :=
  productionPinsOf F Φ (fun N => levelOne (𝓞 F) F N) (fun v => heckeGen (𝓞 F) F v) (adelicBox F)

private abbrev Γ : Subgroup (AdelicGL2 (𝓞 F) F) := (globalPoints (𝓞 F) F).range

private abbrev shear : AdeleRing (𝓞 F) F × AdelicGL2 (𝓞 F) F → AdelicGL2 (𝓞 F) F :=
  fun p => unipotentGL2 p.1 * p.2

private theorem _root_.AutomorphicForm.PseudoEisensteinDensity.Inputs.central_transform_of_isAutomorphicFnAt (Φ : Set (AdelicGL2 (𝓞 F) F)) (ξ : (pins F Φ).Z →* ℂˣ)
    {u : AdelicGL2 (𝓞 F) F → ℂ} (hu : IsAutomorphicFnAt F (pins F Φ) ξ u) (z : (pins F Φ).Z)
    (g : AdelicGL2 (𝓞 F) F) :
    u (centralScalar (𝓞 F) F (z : (AdeleRing (𝓞 F) F)ˣ) * g) = ((ξ z : ℂˣ) : ℂ) * u g :=
  ((lsXiMemberAt_iff (𝓞 F) F (pins F Φ).μ (pins F Φ).Z ξ (pins F Φ).D u).mp hu).1.central_transform z g

p2m_export "AutomorphicForm.PseudoEisensteinDensity.Inputs" "central_transform_of_isAutomorphicFnAt"

private theorem left_invariant_of_isAutomorphicFnAt (Φ : Set (AdelicGL2 (𝓞 F) F)) (ξ : (pins F Φ).Z →* ℂˣ)
    {u : AdelicGL2 (𝓞 F) F → ℂ} (hu : IsAutomorphicFnAt F (pins F Φ) ξ u) (γ : Γ F)
    (g : AdelicGL2 (𝓞 F) F) : u ((γ : AdelicGL2 (𝓞 F) F) * g) = u g := by
  obtain ⟨γ₀, hγ₀⟩ := γ.2
  have h := ((lsXiMemberAt_iff (𝓞 F) F (pins F Φ).μ (pins F Φ).Z ξ (pins F Φ).D u).mp hu).1.left_invariant γ₀ g
  rwa [hγ₀] at h

private theorem memLp_restrict_Φ_of_isAutomorphicFnAt (Φ : Set (AdelicGL2 (𝓞 F) F)) (ξ : (pins F Φ).Z →* ℂˣ)
    {u : AdelicGL2 (𝓞 F) F → ℂ} (hu : IsAutomorphicFnAt F (pins F Φ) ξ u) :
    MemLp u 2 ((adelicGLHaar (Fin 2) (𝓞 F) F).restrict Φ) :=
  ((lsXiMemberAt_iff (𝓞 F) F (pins F Φ).μ (pins F Φ).Z ξ (pins F Φ).D u).mp hu).2

private theorem det_unipotentGL2_mul (q : AdeleRing (𝓞 F) F) (g : AdelicGL2 (𝓞 F) F) :
    Matrix.GeneralLinearGroup.det (unipotentGL2 q * g) = Matrix.GeneralLinearGroup.det g := by
  have h1 : Matrix.GeneralLinearGroup.det (unipotentGL2 (R := AdeleRing (𝓞 F) F) q) = 1 := by
    ext
    simp [Matrix.GeneralLinearGroup.val_det_apply, Matrix.det_fin_two_of]
  rw [map_mul, h1, one_mul]

private theorem preimage_unipotentGL2_mul_slab (d₁ d₂ : ℝ) (q : AdeleRing (𝓞 F) F) :
    (fun g : AdelicGL2 (𝓞 F) F => unipotentGL2 q * g) ⁻¹' slab F d₁ d₂ = slab F d₁ d₂ := by
  ext g
  show NumberField.TateGlobal.ideleNorm F (Matrix.GeneralLinearGroup.det (unipotentGL2 q * g)) ∈ Set.Icc d₁ d₂
    ↔ NumberField.TateGlobal.ideleNorm F (Matrix.GeneralLinearGroup.det g) ∈ Set.Icc d₁ d₂
  rw [det_unipotentGL2_mul]

private theorem measurePreserving_unipotentGL2_mul_slabHaar (d₁ d₂ : ℝ) (q : AdeleRing (𝓞 F) F) :
    MeasurePreserving (fun g : AdelicGL2 (𝓞 F) F => unipotentGL2 q * g) (slabHaar F d₁ d₂) (slabHaar F d₁ d₂) := by
  haveI := borelSpace_glBorel (Fin 2) (𝓞 F) F
  haveI := isHaarMeasure_adelicGLHaar (Fin 2) (𝓞 F) F
  have hmeas : Measurable (fun g : AdelicGL2 (𝓞 F) F => unipotentGL2 q * g) := measurable_const_mul _
  refine ⟨hmeas, ?_⟩
  ext t ht
  rw [Measure.map_apply hmeas ht, Measure.restrict_apply (hmeas ht), Measure.restrict_apply ht]
  conv_lhs => rw [← preimage_unipotentGL2_mul_slab F d₁ d₂ q, ← Set.preimage_inter]
  exact measure_preimage_mul _ _ _

private theorem shear_mem_slab (d₁ d₂ : ℝ) (q : AdeleRing (𝓞 F) F) {g : AdelicGL2 (𝓞 F) F}
    (hg : g ∈ slab F d₁ d₂) : unipotentGL2 q * g ∈ slab F d₁ d₂ := by
  show NumberField.TateGlobal.ideleNorm F (Matrix.GeneralLinearGroup.det (unipotentGL2 q * g)) ∈ Set.Icc d₁ d₂
  rw [det_unipotentGL2_mul]
  exact hg

private theorem setLIntegral_le_mul_setLIntegral_of_invariant
    (d₁ d₂ : ℝ) (Φ : Set (AdelicGL2 (𝓞 F) F))
    [Countable (Γ F)] [MeasurableConstSMul (Γ F) (AdelicGL2 (𝓞 F) F)]
    [SMulInvariantMeasure (Γ F) (AdelicGL2 (𝓞 F) F) (slabHaar F d₁ d₂)]
    (hΦ : IsFundamentalDomain (Γ F) Φ (slabHaar F d₁ d₂))
    (C : Set (AdelicGL2 (𝓞 F) F)) (hC : MeasurableSet C)
    (m : ℕ) (hm : ∀ g : AdelicGL2 (𝓞 F) F, {γ : Γ F | (γ : AdelicGL2 (𝓞 F) F) * g ∈ C}.encard ≤ m)
    (φ : AdelicGL2 (𝓞 F) F → ENNReal) (hφ : AEMeasurable φ (slabHaar F d₁ d₂))
    (hφinv : ∀ (γ : Γ F) (g : AdelicGL2 (𝓞 F) F), φ ((γ : AdelicGL2 (𝓞 F) F) * g) = φ g) :
    ∫⁻ g in C, φ g ∂(slabHaar F d₁ d₂) ≤ (m : ENNReal) * ∫⁻ g in Φ, φ g ∂(slabHaar F d₁ d₂) := by
  classical
  have hkey : ∀ γ : Γ F,
      ∫⁻ x in C ∩ γ • Φ, φ x ∂(slabHaar F d₁ d₂)
        = ∫⁻ y in Φ, C.indicator φ ((γ : AdelicGL2 (𝓞 F) F) * y) ∂(slabHaar F d₁ d₂) := by
    intro γ
    have h1 := (measurePreserving_smul γ (slabHaar F d₁ d₂)).setLIntegral_comp_emb
      (measurableEmbedding_const_smul γ) (C.indicator φ) Φ
    rw [Set.image_smul, lintegral_indicator hC, Measure.restrict_restrict hC] at h1
    exact h1.symm
  have hmeas : ∀ γ : Γ F, AEMeasurable (fun y => C.indicator φ ((γ : AdelicGL2 (𝓞 F) F) * y))
      ((slabHaar F d₁ d₂).restrict Φ) :=
    fun γ => (AEMeasurable.comp_quasiMeasurePreserving (hφ.indicator hC)
      (measurePreserving_smul γ (slabHaar F d₁ d₂)).quasiMeasurePreserving).mono_measure Measure.restrict_le_self
  have h2 := lintegral_tsum hmeas
  rw [hΦ.setLIntegral_eq_tsum φ C]
  simp_rw [hkey]
  refine h2.symm.trans_le ?_
  rw [← lintegral_const_mul' (m : ENNReal) φ (ENNReal.natCast_ne_top m)]
  refine lintegral_mono fun y => ?_
  have hpt : ∀ γ : Γ F, C.indicator φ ((γ : AdelicGL2 (𝓞 F) F) * y)
      = {γ : Γ F | (γ : AdelicGL2 (𝓞 F) F) * y ∈ C}.indicator (fun _ => φ y) γ := by
    intro γ
    by_cases hγ : (γ : AdelicGL2 (𝓞 F) F) * y ∈ C
    · have hγ' : γ ∈ {γ : Γ F | (γ : AdelicGL2 (𝓞 F) F) * y ∈ C} := hγ
      simp only [Set.indicator_of_mem hγ, Set.indicator_of_mem hγ', hφinv γ y]
    · have hγ' : γ ∉ {γ : Γ F | (γ : AdelicGL2 (𝓞 F) F) * y ∈ C} := hγ
      simp only [Set.indicator_apply, hγ, hγ', if_false]
  simp_rw [hpt]
  rw [← tsum_subtype, ENNReal.tsum_set_const]
  calc ({γ : Γ F | (γ : AdelicGL2 (𝓞 F) F) * y ∈ C}.encard : ENNReal) * φ y
      ≤ ((m : ENat) : ENNReal) * φ y := by
        gcongr
        exact_mod_cast hm y
    _ = (m : ENNReal) * φ y := by simp

private theorem quasiMeasurePreserving_shear_prod (d₁ d₂ : ℝ) (Φ : Set (AdelicGL2 (𝓞 F) F))
    (hshear : Measurable (shear F)) (ρ : Measure (AdelicGL2 (𝓞 F) F)) [SFinite ρ]
    (hρ : ρ ≤ slabHaar F d₁ d₂) :
    Measure.QuasiMeasurePreserving
      (fun p : AdelicGL2 (𝓞 F) F × AdeleRing (𝓞 F) F => unipotentGL2 p.2 * p.1) (ρ.prod (pins F Φ).ν)
      (slabHaar F d₁ d₂) := by
  haveI : IsProbabilityMeasure (pins F Φ).ν := isProbabilityMeasure_cond_adelicBox F
  have hmeas' := hshear.comp measurable_swap
  have hmeas : Measurable (fun p : AdelicGL2 (𝓞 F) F × AdeleRing (𝓞 F) F => unipotentGL2 p.2 * p.1) := hmeas'
  refine ⟨hmeas, Measure.AbsolutelyContinuous.mk fun N hN hN0 => ?_⟩
  have hsec : ∀ q : AdeleRing (𝓞 F) F,
      ρ ((fun g : AdelicGL2 (𝓞 F) F => (g, q)) ⁻¹'
        ((fun p : AdelicGL2 (𝓞 F) F × AdeleRing (𝓞 F) F => unipotentGL2 p.2 * p.1) ⁻¹' N)) = 0 := by
    intro q
    refine nonpos_iff_eq_zero.mp ?_
    calc ρ ((fun g : AdelicGL2 (𝓞 F) F => (g, q)) ⁻¹'
            ((fun p : AdelicGL2 (𝓞 F) F × AdeleRing (𝓞 F) F => unipotentGL2 p.2 * p.1) ⁻¹' N))
        ≤ slabHaar F d₁ d₂ ((fun g : AdelicGL2 (𝓞 F) F => unipotentGL2 q * g) ⁻¹' N) := Measure.le_iff'.mp hρ _
      _ = slabHaar F d₁ d₂ N :=
          (measurePreserving_unipotentGL2_mul_slabHaar F d₁ d₂ q).measure_preimage hN.nullMeasurableSet
      _ = 0 := hN0
  calc (ρ.prod (pins F Φ).ν).map (fun p : AdelicGL2 (𝓞 F) F × AdeleRing (𝓞 F) F => unipotentGL2 p.2 * p.1) N
      = ρ.prod (pins F Φ).ν
          ((fun p : AdelicGL2 (𝓞 F) F × AdeleRing (𝓞 F) F => unipotentGL2 p.2 * p.1) ⁻¹' N) :=
        Measure.map_apply hmeas hN
    _ = ∫⁻ q, ρ ((fun g : AdelicGL2 (𝓞 F) F => (g, q)) ⁻¹'
          ((fun p : AdelicGL2 (𝓞 F) F × AdeleRing (𝓞 F) F => unipotentGL2 p.2 * p.1) ⁻¹' N))
            ∂(pins F Φ).ν :=
        Measure.prod_apply_symm (hmeas hN)
    _ = 0 := by simp only [hsec, lintegral_zero]

private theorem constantTerm_congr_ae
    (d₁ d₂ : ℝ) (Φ : Set (AdelicGL2 (𝓞 F) F)) [SigmaCompactSpace (AdelicGL2 (𝓞 F) F)]
    (hslab : MeasurableSet (slab F d₁ d₂)) (hshear : Measurable (shear F))
    (u v : AdelicGL2 (𝓞 F) F → ℂ) (huv : u =ᵐ[slabHaar F d₁ d₂] v) :
    (fun g => constantTerm (pins F Φ).ν unipotentGL2 u g)
      =ᵐ[slabHaar F d₁ d₂] fun g => constantTerm (pins F Φ).ν unipotentGL2 v g := by
  have _ := hslab
  haveI := isHaarMeasure_adelicGLHaar (Fin 2) (𝓞 F) F
  haveI : IsProbabilityMeasure (pins F Φ).ν := isProbabilityMeasure_cond_adelicBox F
  have hq := quasiMeasurePreserving_shear_prod F d₁ d₂ Φ hshear (slabHaar F d₁ d₂) le_rfl
  have h1 : (fun p : AdelicGL2 (𝓞 F) F × AdeleRing (𝓞 F) F => u (unipotentGL2 p.2 * p.1))
      =ᵐ[(slabHaar F d₁ d₂).prod (pins F Φ).ν]
        (fun p : AdelicGL2 (𝓞 F) F × AdeleRing (𝓞 F) F => v (unipotentGL2 p.2 * p.1)) := hq.ae_eq huv
  have h2 : ∀ᵐ g ∂(slabHaar F d₁ d₂), ∀ᵐ q ∂(pins F Φ).ν, u (unipotentGL2 q * g) = v (unipotentGL2 q * g) :=
    Measure.ae_ae_of_ae_prod h1
  filter_upwards [h2] with g hg
  simp only [constantTerm, constantTermIntegrand]
  exact integral_congr_ae hg

private theorem measurable_unipotentGL2_fst_mul_snd [SecondCountableTopology (AdelicGL2 (𝓞 F) F)]
    (hcont : Continuous fun q : AdeleRing (𝓞 F) F => unipotentGL2 (R := AdeleRing (𝓞 F) F) q) :
    Measurable fun p : AdeleRing (𝓞 F) F × AdelicGL2 (𝓞 F) F => unipotentGL2 p.1 * p.2 :=
  ((hcont.comp continuous_fst).mul continuous_snd).measurable

private theorem centralScalar_principal_eq_globalPoints (a : Fˣ) :
    centralScalar (𝓞 F) F (Units.map (algebraMap F (AdeleRing (𝓞 F) F) : F →* AdeleRing (𝓞 F) F) a)
      = globalPoints (𝓞 F) F (Matrix.GeneralLinearGroup.scalar (Fin 2) a) := by
  apply Units.ext
  ext i j
  by_cases hij : i = j
  · subst hij
    simp [centralScalar, globalPoints, Matrix.GeneralLinearGroup.scalar, Matrix.GeneralLinearGroup.map,
      Matrix.scalar_apply, Matrix.diagonal_apply_eq]
  · simp [centralScalar, globalPoints, Matrix.GeneralLinearGroup.scalar, Matrix.GeneralLinearGroup.map,
      Matrix.scalar_apply, hij]

private theorem forall_principal_eq_one_or_eq_zero (Φ : Set (AdelicGL2 (𝓞 F) F)) (ξ : (pins F Φ).Z →* ℂˣ)
    {u : AdelicGL2 (𝓞 F) F → ℂ} (hu : IsAutomorphicFnAt F (pins F Φ) ξ u) :
    (∀ γ ∈ M4aHerbrand.principalIdeles (𝓞 F) F, ∀ hγ : γ ∈ (pins F Φ).Z, ξ ⟨γ, hγ⟩ = 1)
      ∨ ∀ g : AdelicGL2 (𝓞 F) F, u g = 0 := by
  by_cases h : ∀ γ ∈ M4aHerbrand.principalIdeles (𝓞 F) F, ∀ hγ : γ ∈ (pins F Φ).Z, ξ ⟨γ, hγ⟩ = 1
  · exact Or.inl h
  right
  obtain ⟨γ, hγ⟩ := not_forall.mp h
  obtain ⟨hγP, hγ'⟩ := Classical.not_imp.mp hγ
  obtain ⟨hγZ, hne⟩ := not_forall.mp hγ'
  obtain ⟨a, rfl⟩ := MonoidHom.mem_range.mp hγP
  intro g
  have h1 := central_transform_of_isAutomorphicFnAt F Φ ξ hu ⟨_, hγZ⟩ g
  have h2 : u (centralScalar (𝓞 F) F
      (Units.map (algebraMap F (AdeleRing (𝓞 F) F) : F →* AdeleRing (𝓞 F) F) a) * g) = u g := by
    rw [centralScalar_principal_eq_globalPoints]
    exact left_invariant_of_isAutomorphicFnAt F Φ ξ hu ⟨_, MonoidHom.mem_range.mpr ⟨_, rfl⟩⟩ g
  have h3 : (((ξ ⟨_, hγZ⟩ : ℂˣ) : ℂ) - 1) * u g = 0 := by
    rw [sub_mul, one_mul, ← h1, h2, sub_self]
  refine (mul_eq_zero.mp h3).resolve_left (sub_ne_zero.mpr fun h4 => hne (Units.ext ?_))
  simpa using h4

private theorem constantTerm_congr_ae_restrict (d₁ d₂ : ℝ) (Φ : Set (AdelicGL2 (𝓞 F) F))
    (S' : Set (AdelicGL2 (𝓞 F) F)) (hS's : S' ⊆ slab F d₁ d₂) (u v : AdelicGL2 (𝓞 F) F → ℂ)
    (huv : u =ᵐ[adelicGLHaar (Fin 2) (𝓞 F) F] v) :
    (fun g => constantTerm (pins F Φ).ν unipotentGL2 u g)
      =ᵐ[(adelicGLHaar (Fin 2) (𝓞 F) F).restrict S'] fun g => constantTerm (pins F Φ).ν unipotentGL2 v g := by
  haveI : SecondCountableTopology (AdelicGL2 (𝓞 F) F) :=
    NumberField.AdeleRing.secondCountableTopology_generalLinearGroup_finTwo F
  haveI := isHaarMeasure_adelicGLHaar (Fin 2) (𝓞 F) F
  haveI : SigmaCompactSpace (AdelicGL2 (𝓞 F) F) := inferInstance
  have hcont : Continuous fun q : AdeleRing (𝓞 F) F => unipotentGL2 (R := AdeleRing (𝓞 F) F) q :=
    continuous_unipotentGL2
  have hshear : Measurable (shear F) := measurable_unipotentGL2_fst_mul_snd F hcont
  exact ae_restrict_of_ae_restrict_of_subset hS's (constantTerm_congr_ae F d₁ d₂ Φ
    (NumberField.TateGlobal.measurableSet_setOf_ideleNorm_det_mem_Icc F d₁ d₂) hshear u v (ae_restrict_of_ae huv))

end AutomorphicForm.PseudoEisensteinDensity.Inputs
p2m_reactivate "P2MW.S_AutomorphicForm_exists_isSlabProfile_eLpNorm_sub_pseudoEisenstein_lt_of_forall_setIntegral_eq_zero_slab.SlabPairingDescent P2MW.S_AutomorphicForm_exists_isSlabProfile_eLpNorm_sub_pseudoEisenstein_lt_of_forall_setIntegral_eq_zero_slab.AutomorphicForm P2MW.S_AutomorphicForm_exists_isSlabProfile_eLpNorm_sub_pseudoEisenstein_lt_of_forall_setIntegral_eq_zero_slab.AutomorphicForm.TwistedCentralAverage"
p2m_reactivate "P2MW.S_AutomorphicForm_exists_isSlabProfile_eLpNorm_sub_pseudoEisenstein_lt_of_forall_setIntegral_eq_zero_slab.SlabPairingDescent P2MW.S_AutomorphicForm_exists_isSlabProfile_eLpNorm_sub_pseudoEisenstein_lt_of_forall_setIntegral_eq_zero_slab.AutomorphicForm P2MW.S_AutomorphicForm_exists_isSlabProfile_eLpNorm_sub_pseudoEisenstein_lt_of_forall_setIntegral_eq_zero_slab.AutomorphicForm.TwistedCentralAverage"
p2m_reactivate "P2MW.S_AutomorphicForm_exists_isSlabProfile_eLpNorm_sub_pseudoEisenstein_lt_of_forall_setIntegral_eq_zero_slab.SlabPairingDescent P2MW.S_AutomorphicForm_exists_isSlabProfile_eLpNorm_sub_pseudoEisenstein_lt_of_forall_setIntegral_eq_zero_slab.AutomorphicForm P2MW.S_AutomorphicForm_exists_isSlabProfile_eLpNorm_sub_pseudoEisenstein_lt_of_forall_setIntegral_eq_zero_slab.AutomorphicForm.TwistedCentralAverage"

end
p2m_reactivate "P2MW.S_AutomorphicForm_exists_isSlabProfile_eLpNorm_sub_pseudoEisenstein_lt_of_forall_setIntegral_eq_zero_slab.SlabPairingDescent P2MW.S_AutomorphicForm_exists_isSlabProfile_eLpNorm_sub_pseudoEisenstein_lt_of_forall_setIntegral_eq_zero_slab.AutomorphicForm P2MW.S_AutomorphicForm_exists_isSlabProfile_eLpNorm_sub_pseudoEisenstein_lt_of_forall_setIntegral_eq_zero_slab.AutomorphicForm.TwistedCentralAverage"

end
p2m_reactivate "P2MW.S_AutomorphicForm_exists_isSlabProfile_eLpNorm_sub_pseudoEisenstein_lt_of_forall_setIntegral_eq_zero_slab.SlabPairingDescent P2MW.S_AutomorphicForm_exists_isSlabProfile_eLpNorm_sub_pseudoEisenstein_lt_of_forall_setIntegral_eq_zero_slab.AutomorphicForm P2MW.S_AutomorphicForm_exists_isSlabProfile_eLpNorm_sub_pseudoEisenstein_lt_of_forall_setIntegral_eq_zero_slab.AutomorphicForm.TwistedCentralAverage"
end
p2m_reactivate "P2MW.S_AutomorphicForm_exists_isSlabProfile_eLpNorm_sub_pseudoEisenstein_lt_of_forall_setIntegral_eq_zero_slab.SlabPairingDescent P2MW.S_AutomorphicForm_exists_isSlabProfile_eLpNorm_sub_pseudoEisenstein_lt_of_forall_setIntegral_eq_zero_slab.AutomorphicForm P2MW.S_AutomorphicForm_exists_isSlabProfile_eLpNorm_sub_pseudoEisenstein_lt_of_forall_setIntegral_eq_zero_slab.AutomorphicForm.TwistedCentralAverage"

section

set_option autoImplicit false

section

open MeasureTheory NumberField
open NumberField.AdelicHaar NumberField.AdelicLevel NumberField.AdelicBox
p2m_open "AutomorphicForm P2MW.S_AutomorphicForm_exists_isSlabProfile_eLpNorm_sub_pseudoEisenstein_lt_of_forall_setIntegral_eq_zero_slab.AutomorphicForm"
open scoped Pointwise ENNReal

attribute [local instance] NumberField.AdelicHaar.glBorel NumberField.AdelicHaar.adeleBorel
attribute [local instance] NumberField.AdelicHaar.borelSpace_glBorel NumberField.AdelicHaar.borelSpace_adeleBorel
attribute [local instance] NumberField.AdelicHaar.isHaarMeasure_adelicGLHaar

noncomputable section

namespace AutomorphicForm
p2m_export "AutomorphicForm" "lsXiMemberAt_iff IsAutomorphicFnAt CarrierPins productionPinsOf AdelicGL2 globalPoints centralScalar IsLsXiFunction unipotentGL2 unipotentGL2_coe constantTermIntegrand constantTerm IsSlabProfile pseudoEisenstein pseudoEisenstein_apply isSlabProfile_zero pseudoEisenstein_zero borelSubgroup mem_borelSubgroup_iff globalPoints_apply gl2Weyl adelicWeyl WindowedSiegel.rowNormSq WindowedSiegel.localHeight WindowedSiegel.archHeight WindowedSiegel.archHeight_scalar_entries_mul finite_support_pseudoEisenstein_summand isAutomorphicFnAt_pseudoEisenstein_slab aestronglyMeasurable_adelicGLHaar_of_isAutomorphicFnAt_slab setIntegral_pseudoEisenstein_mul_conj_eq_setIntegral_rationalTorusUnipotentQuotient_slab rationalTorusUnipotent RationalTorusUnipotentQuotient rationalTorusUnipotentHaar rationalTorusUnipotentQuotientMeasure toAdelicUnipotent adelicMaximalCompact isCompact_adelicMaximalCompact maximalCompactHaar constantTerm_adelicBox_globalPoints_mul_of_mem_borelSubgroup constantTerm_adelicBox_unipotentGL2_mul continuous_unipotentGL2 exists_isFundamentalDomain_globalPoints_range exists_lintegral_rationalTorusUnipotentQuotientMeasure_eq_mul_setLIntegral_iwasawa ideleNorm_det_globalPoints isClosed_rationalTorusUnipotent isFundamentalDomain_boxSheet_rationalTorusUnipotent isHaarMeasure_rationalTorusUnipotentHaar_and_isMulRightInvariant"
namespace PseudoEisensteinDensity
namespace Integration
p2m_open "AutomorphicForm"

variable (F : Type) [Field F] [NumberField F]

private abbrev pins (Φ : Set (AdelicGL2 (𝓞 F) F)) : CarrierPins F :=
  productionPinsOf F Φ (fun N => levelOne (𝓞 F) F N) (fun v => heckeGen (𝓞 F) F v) (adelicBox F)

private abbrev borelImage : Subgroup (AdelicGL2 (𝓞 F) F) :=
  (borelSubgroup F).map (globalPoints (𝓞 F) F)

private theorem borelImage_le_range : borelImage F ≤ (globalPoints (𝓞 F) F).range :=
  Subgroup.map_le_range _ _

private theorem borelImage_invariant {w : AdelicGL2 (𝓞 F) F → ℂ}
    (hw : ∀ γ ∈ (globalPoints (𝓞 F) F).range, ∀ g : AdelicGL2 (𝓞 F) F, w (γ * g) = w g) :
    ∀ b ∈ borelImage F, ∀ g : AdelicGL2 (𝓞 F) F, w (b * g) = w g :=
  fun b hb g => hw b (borelImage_le_range F hb) g

private theorem lintegral_enorm_mul_conj_lt_top (d₁ d₂ : ℝ) (hd₁ : 0 < d₁)
    (S : Set (AdelicGL2 (𝓞 F) F))
    (hS : IsFundamentalDomain (borelImage F) S (adelicGLHaar (Fin 2) (𝓞 F) F))
    {Z : Subgroup (AdeleRing (𝓞 F) F)ˣ} {ξ : Z →* ℂˣ}
    {φ : AdelicGL2 (𝓞 F) F → ℂ} (hφ : IsSlabProfile F Z ξ φ) (h : AdelicGL2 (𝓞 F) F → ℂ) (C : ℝ)
    (hC : ∀ᵐ g ∂((adelicGLHaar (Fin 2) (𝓞 F) F).restrict (S ∩ SlabPairingDescent.slab F d₁ d₂)),
      ‖φ g * (starRingEnd ℂ) (h g)‖ ≤ C) :
    ∫⁻ g in S ∩ SlabPairingDescent.slab F d₁ d₂, ‖φ g * (starRingEnd ℂ) (h g)‖ₑ
        ∂(adelicGLHaar (Fin 2) (𝓞 F) F) < ∞ := by
  obtain ⟨a, b, ha, hband⟩ := hφ.height_band
  set band : Set (AdelicGL2 (𝓞 F) F) := {g | NumberField.AdelicHeight.adelicHeight F g ∈ Set.Icc a b}
    with hband_def
  have hle : ∀ᵐ g ∂((adelicGLHaar (Fin 2) (𝓞 F) F).restrict (S ∩ SlabPairingDescent.slab F d₁ d₂)),
      ‖φ g * (starRingEnd ℂ) (h g)‖ₑ ≤ band.indicator (fun _ => ENNReal.ofReal C) g := by
    filter_upwards [hC] with g hg
    by_cases hgb : g ∈ band
    · rw [Set.indicator_of_mem hgb, ← ofReal_norm]
      exact ENNReal.ofReal_le_ofReal hg
    · have hφ0 : φ g = 0 := by
        by_contra hne
        exact hgb (hband g hne)
      simp [hφ0]
  have hSm : NullMeasurableSet (S ∩ SlabPairingDescent.slab F d₁ d₂) (adelicGLHaar (Fin 2) (𝓞 F) F) :=
    hS.nullMeasurableSet.inter
      (NumberField.TateGlobal.measurableSet_setOf_ideleNorm_det_mem_Icc F d₁ d₂).nullMeasurableSet
  calc ∫⁻ g in S ∩ SlabPairingDescent.slab F d₁ d₂, ‖φ g * (starRingEnd ℂ) (h g)‖ₑ
          ∂(adelicGLHaar (Fin 2) (𝓞 F) F)
      ≤ ∫⁻ g in S ∩ SlabPairingDescent.slab F d₁ d₂, band.indicator (fun _ => ENNReal.ofReal C) g
          ∂(adelicGLHaar (Fin 2) (𝓞 F) F) := lintegral_mono_ae hle
    _ ≤ ENNReal.ofReal C *
          ((adelicGLHaar (Fin 2) (𝓞 F) F).restrict (S ∩ SlabPairingDescent.slab F d₁ d₂)) band :=
        lintegral_indicator_const_le _ _
    _ = ENNReal.ofReal C *
          adelicGLHaar (Fin 2) (𝓞 F) F (S ∩ SlabPairingDescent.slab F d₁ d₂ ∩ band) := by
        rw [Measure.restrict_apply₀' hSm, Set.inter_comm]
    _ < ∞ := by
        refine ENNReal.mul_lt_top ENNReal.ofReal_lt_top ?_
        exact SlabBandVolume.adelicGLHaar_inter_setOf_ideleNorm_det_mem_Icc_inter_setOf_adelicHeight_mem_Icc_lt_top
          F (TwistedCentralAverage.adelicHeight_unipotentGL2_mul F)
          (TwistedCentralAverage.adelicHeight_centralScalar_mul F) d₁ d₂ hd₁ a b ha S hS

private theorem main
    (d₁ d₂ : ℝ) (hd₁ : 0 < d₁) (hd : d₁ < d₂)
    (Φ : Set (AdelicGL2 (𝓞 F) F))
    (hΦs : Φ ⊆ {g | NumberField.TateGlobal.ideleNorm F (Matrix.GeneralLinearGroup.det g) ∈ Set.Icc d₁ d₂})
    (hΦ : IsFundamentalDomain (globalPoints (𝓞 F) F).range Φ
      ((adelicGLHaar (Fin 2) (𝓞 F) F).restrict {g | NumberField.TateGlobal.ideleNorm F
          (Matrix.GeneralLinearGroup.det g) ∈ Set.Icc d₁ d₂}))
    (ξ : (pins F Φ).Z →* ℂˣ) (hξ : Continuous ξ)
    (u : AdelicGL2 (𝓞 F) F → ℂ) (hu : IsAutomorphicFnAt F (pins F Φ) ξ u)
    (horth : ∀ φ : AdelicGL2 (𝓞 F) F → ℂ, IsSlabProfile F (pins F Φ).Z ξ φ →
      ∫ g in Φ, pseudoEisenstein F φ g * (starRingEnd ℂ) (u g) ∂(adelicGLHaar (Fin 2) (𝓞 F) F) = 0) :
    ∀ᵐ g ∂(adelicGLHaar (Fin 2) (𝓞 F) F), constantTerm (pins F Φ).ν unipotentGL2 u g = 0 := by
  rcases Inputs.forall_principal_eq_one_or_eq_zero F Φ ξ hu with hξF | hu0
  swap
  · refine Filter.Eventually.of_forall fun g => ?_
    simp only [constantTerm, constantTermIntegrand, hu0, integral_zero]
  have hmeas : AEStronglyMeasurable u (adelicGLHaar (Fin 2) (𝓞 F) F) :=
    aestronglyMeasurable_adelicGLHaar_of_isAutomorphicFnAt_slab F d₁ d₂ hd₁ hd Φ hΦs hΦ ξ u hu
  haveI : Countable (globalPoints (𝓞 F) F).range := SlabPairingDescent.countable_globalPoints_range F
  obtain ⟨w, hwm, hwinv, hwu⟩ := Inputs.exists_measurable_forall_mul_eq_and_ae_eq
    (adelicGLHaar (Fin 2) (𝓞 F) F) (globalPoints (𝓞 F) F).range u
    (fun γ hγ g => Inputs.left_invariant_of_isAutomorphicFnAt F Φ ξ hu ⟨γ, hγ⟩ g) hmeas
  obtain ⟨S, hS⟩ := SlabPairingDescent.exists_isFundamentalDomain_borelImage F
  have hctm : Measurable fun g => constantTerm (SlabPairingDescent.boxCond F) (fun x => unipotentGL2 x) w g :=
    SlabPairingDescent.measurable_constantTerm_boxCond F w hwm
  have hctB : ∀ b ∈ borelImage F, ∀ g : AdelicGL2 (𝓞 F) F,
      constantTerm (SlabPairingDescent.boxCond F) (fun x => unipotentGL2 x) w (b * g)
        = constantTerm (SlabPairingDescent.boxCond F) (fun x => unipotentGL2 x) w g := by
    intro b hb g
    obtain ⟨γ, hγ, rfl⟩ := Subgroup.mem_map.mp hb
    exact constantTerm_adelicBox_globalPoints_mul_of_mem_borelSubgroup F
      (fun γ' _ g' => hwinv (globalPoints (𝓞 F) F γ') ⟨γ', rfl⟩ g') hγ g
  have hpair : ∀ φ : AdelicGL2 (𝓞 F) F → ℂ, IsSlabProfile F (pins F Φ).Z ξ φ →
      (∃ C : ℝ, ∀ᵐ g ∂((adelicGLHaar (Fin 2) (𝓞 F) F).restrict (S ∩ SlabPairingDescent.slab F d₁ d₂)),
        ‖φ g * (starRingEnd ℂ) (constantTerm (SlabPairingDescent.boxCond F) (fun x => unipotentGL2 x) w g)‖
          ≤ C) →
      ∫ g in S ∩ SlabPairingDescent.slab F d₁ d₂,
          φ g * (starRingEnd ℂ) (constantTerm (SlabPairingDescent.boxCond F) (fun x => unipotentGL2 x) w g)
        ∂(adelicGLHaar (Fin 2) (𝓞 F) F) = 0 := by
    intro φ hφ hCbound
    obtain ⟨C, hC⟩ := hCbound
    have hfin := lintegral_enorm_mul_conj_lt_top F d₁ d₂ hd₁ S hS hφ
      (fun g => constantTerm (SlabPairingDescent.boxCond F) (fun x => unipotentGL2 x) w g) C hC
    have hφB : ∀ b ∈ borelImage F, ∀ g : AdelicGL2 (𝓞 F) F, φ (b * g) = φ g := by
      intro b hb g
      obtain ⟨γ, hγ, rfl⟩ := Subgroup.mem_map.mp hb
      exact hφ.borel_mul γ hγ g
    rw [SlabPairingDescent.setIntegral_inter_slab_mul_conj_eq_setIntegral_quotient F d₁ d₂ S hS φ
      hφ.measurable hφB hφ.unipotent_mul _ hctm hctB hfin]
    have hdesc := SlabPairingDescent.ae_constantTerm_out_eq_of_ae_eq F w u hwu
    have hrat : ∀ (k : F) (g : AdelicGL2 (𝓞 F) F), w (globalPoints (𝓞 F) F (unipotentGL2 k) * g) = w g :=
      fun k g => hwinv _ ⟨unipotentGL2 k, rfl⟩ g
    calc ∫ q in {q : RationalTorusUnipotentQuotient F | q.out ∈ SlabPairingDescent.slab F d₁ d₂},
            φ q.out * (starRingEnd ℂ) (constantTerm (SlabPairingDescent.boxCond F) (fun x => unipotentGL2 x)
              (fun g => constantTerm (SlabPairingDescent.boxCond F) (fun x => unipotentGL2 x) w g) q.out)
          ∂(rationalTorusUnipotentQuotientMeasure F)
        = ∫ q in {q : RationalTorusUnipotentQuotient F | q.out ∈ SlabPairingDescent.slab F d₁ d₂},
            φ q.out * (starRingEnd ℂ) (constantTerm (SlabPairingDescent.boxCond F) (fun x => unipotentGL2 x)
              u q.out)
          ∂(rationalTorusUnipotentQuotientMeasure F) := by
          refine integral_congr_ae (ae_restrict_of_ae ?_)
          filter_upwards [hdesc] with q hq
          rw [SlabPairingDescent.constantTerm_boxCond_constantTerm_boxCond F w hrat q.out, hq]
      _ = ∫ g in Φ, pseudoEisenstein F φ g * (starRingEnd ℂ) (u g) ∂(adelicGLHaar (Fin 2) (𝓞 F) F) :=
          (setIntegral_pseudoEisenstein_mul_conj_eq_setIntegral_rationalTorusUnipotentQuotient_slab
            F d₁ d₂ hd₁ hd Φ hΦs hΦ ξ u hu φ hφ).symm
      _ = 0 := horth φ hφ
  have hfinite : ∀ a b : ℝ, 0 < a →
      adelicGLHaar (Fin 2) (𝓞 F) F (S ∩ SlabPairingDescent.slab F d₁ d₂ ∩
        {g | NumberField.AdelicHeight.adelicHeight F g ∈ Set.Icc a b}) < ∞ :=
    fun a b ha =>
      SlabBandVolume.adelicGLHaar_inter_setOf_ideleNorm_det_mem_Icc_inter_setOf_adelicHeight_mem_Icc_lt_top
        F (TwistedCentralAverage.adelicHeight_unipotentGL2_mul F)
        (TwistedCentralAverage.adelicHeight_centralScalar_mul F) d₁ d₂ hd₁ a b ha S hS
  have huLs : IsLsXiFunction (𝓞 F) F (pins F Φ).Z ξ u :=
    ⟨fun γ g => Inputs.left_invariant_of_isAutomorphicFnAt F Φ ξ hu ⟨globalPoints (𝓞 F) F γ, ⟨γ, rfl⟩⟩ g,
      fun z g => SlabToGroup.central_transform_of_isAutomorphicFnAt F Φ ξ hu z g⟩
  have hSm : NullMeasurableSet (S ∩ SlabPairingDescent.slab F d₁ d₂) (adelicGLHaar (Fin 2) (𝓞 F) F) :=
    hS.nullMeasurableSet.inter
      (NumberField.TateGlobal.measurableSet_setOf_ideleNorm_det_mem_Icc F d₁ d₂).nullMeasurableSet
  have hw0 := TwistedCentralAverage.ae_constantTerm_eq_zero_of_forall_isSlabProfile_setIntegral_mul_conj_eq_zero
    (pins F Φ).Z ξ u huLs w hwm (fun γ g => hwinv (globalPoints (𝓞 F) F γ) ⟨γ, rfl⟩ g) hwu hξ rfl hξF
    d₁ d₂ hd₁ (hd₁.trans hd) (S ∩ SlabPairingDescent.slab F d₁ d₂) hSm Set.inter_subset_right hfinite hpair
  have h0 : ∀ᵐ g ∂((adelicGLHaar (Fin 2) (𝓞 F) F).restrict (S ∩ SlabPairingDescent.slab F d₁ d₂)),
      constantTerm (pins F Φ).ν unipotentGL2 u g = 0 := by
    have hbr := Inputs.constantTerm_congr_ae_restrict F d₁ d₂ Φ (S ∩ SlabPairingDescent.slab F d₁ d₂)
      Set.inter_subset_right w u hwu
    filter_upwards [hw0, hbr] with g hg hg'
    rw [← hg']
    exact hg
  haveI : Countable (borelImage F) := (Subgroup.inclusion_injective (borelImage_le_range F)).countable
  refine SlabToGroup.ae_constantTerm_eq_zero_of_ae_restrict_inter F d₁ d₂ hd₁ hd Φ ξ u hu (borelImage F)
    (borelImage_le_range F) S hS ?_ h0
  intro γ g
  obtain ⟨γ₀, hγ₀, hγeq⟩ := Subgroup.mem_map.mp γ.2
  rw [← hγeq]
  exact constantTerm_adelicBox_globalPoints_mul_of_mem_borelSubgroup F
    (fun γ' _ g' => Inputs.left_invariant_of_isAutomorphicFnAt F Φ ξ hu ⟨globalPoints (𝓞 F) F γ', ⟨γ', rfl⟩⟩ g')
    hγ₀ g

end AutomorphicForm.PseudoEisensteinDensity.Integration
p2m_reactivate "P2MW.S_AutomorphicForm_exists_isSlabProfile_eLpNorm_sub_pseudoEisenstein_lt_of_forall_setIntegral_eq_zero_slab.SlabPairingDescent P2MW.S_AutomorphicForm_exists_isSlabProfile_eLpNorm_sub_pseudoEisenstein_lt_of_forall_setIntegral_eq_zero_slab.AutomorphicForm P2MW.S_AutomorphicForm_exists_isSlabProfile_eLpNorm_sub_pseudoEisenstein_lt_of_forall_setIntegral_eq_zero_slab.AutomorphicForm.TwistedCentralAverage"
p2m_reactivate "P2MW.S_AutomorphicForm_exists_isSlabProfile_eLpNorm_sub_pseudoEisenstein_lt_of_forall_setIntegral_eq_zero_slab.SlabPairingDescent P2MW.S_AutomorphicForm_exists_isSlabProfile_eLpNorm_sub_pseudoEisenstein_lt_of_forall_setIntegral_eq_zero_slab.AutomorphicForm P2MW.S_AutomorphicForm_exists_isSlabProfile_eLpNorm_sub_pseudoEisenstein_lt_of_forall_setIntegral_eq_zero_slab.AutomorphicForm.TwistedCentralAverage"
p2m_reactivate "P2MW.S_AutomorphicForm_exists_isSlabProfile_eLpNorm_sub_pseudoEisenstein_lt_of_forall_setIntegral_eq_zero_slab.SlabPairingDescent P2MW.S_AutomorphicForm_exists_isSlabProfile_eLpNorm_sub_pseudoEisenstein_lt_of_forall_setIntegral_eq_zero_slab.AutomorphicForm P2MW.S_AutomorphicForm_exists_isSlabProfile_eLpNorm_sub_pseudoEisenstein_lt_of_forall_setIntegral_eq_zero_slab.AutomorphicForm.TwistedCentralAverage"

end
p2m_reactivate "P2MW.S_AutomorphicForm_exists_isSlabProfile_eLpNorm_sub_pseudoEisenstein_lt_of_forall_setIntegral_eq_zero_slab.SlabPairingDescent P2MW.S_AutomorphicForm_exists_isSlabProfile_eLpNorm_sub_pseudoEisenstein_lt_of_forall_setIntegral_eq_zero_slab.AutomorphicForm P2MW.S_AutomorphicForm_exists_isSlabProfile_eLpNorm_sub_pseudoEisenstein_lt_of_forall_setIntegral_eq_zero_slab.AutomorphicForm.TwistedCentralAverage"

end
p2m_reactivate "P2MW.S_AutomorphicForm_exists_isSlabProfile_eLpNorm_sub_pseudoEisenstein_lt_of_forall_setIntegral_eq_zero_slab.SlabPairingDescent P2MW.S_AutomorphicForm_exists_isSlabProfile_eLpNorm_sub_pseudoEisenstein_lt_of_forall_setIntegral_eq_zero_slab.AutomorphicForm P2MW.S_AutomorphicForm_exists_isSlabProfile_eLpNorm_sub_pseudoEisenstein_lt_of_forall_setIntegral_eq_zero_slab.AutomorphicForm.TwistedCentralAverage"
end
p2m_reactivate "P2MW.S_AutomorphicForm_exists_isSlabProfile_eLpNorm_sub_pseudoEisenstein_lt_of_forall_setIntegral_eq_zero_slab.SlabPairingDescent P2MW.S_AutomorphicForm_exists_isSlabProfile_eLpNorm_sub_pseudoEisenstein_lt_of_forall_setIntegral_eq_zero_slab.AutomorphicForm P2MW.S_AutomorphicForm_exists_isSlabProfile_eLpNorm_sub_pseudoEisenstein_lt_of_forall_setIntegral_eq_zero_slab.AutomorphicForm.TwistedCentralAverage"

section

set_option autoImplicit false

open MeasureTheory Filter Topology
open scoped Classical NumberField

noncomputable section

namespace AutomorphicForm
p2m_export "AutomorphicForm" "lsXiMemberAt_iff IsAutomorphicFnAt CarrierPins productionPinsOf AdelicGL2 globalPoints centralScalar IsLsXiFunction unipotentGL2 unipotentGL2_coe constantTermIntegrand constantTerm IsSlabProfile pseudoEisenstein pseudoEisenstein_apply isSlabProfile_zero pseudoEisenstein_zero borelSubgroup mem_borelSubgroup_iff globalPoints_apply gl2Weyl adelicWeyl WindowedSiegel.rowNormSq WindowedSiegel.localHeight WindowedSiegel.archHeight WindowedSiegel.archHeight_scalar_entries_mul finite_support_pseudoEisenstein_summand isAutomorphicFnAt_pseudoEisenstein_slab aestronglyMeasurable_adelicGLHaar_of_isAutomorphicFnAt_slab setIntegral_pseudoEisenstein_mul_conj_eq_setIntegral_rationalTorusUnipotentQuotient_slab rationalTorusUnipotent RationalTorusUnipotentQuotient rationalTorusUnipotentHaar rationalTorusUnipotentQuotientMeasure toAdelicUnipotent adelicMaximalCompact isCompact_adelicMaximalCompact maximalCompactHaar constantTerm_adelicBox_globalPoints_mul_of_mem_borelSubgroup constantTerm_adelicBox_unipotentGL2_mul continuous_unipotentGL2 exists_isFundamentalDomain_globalPoints_range exists_lintegral_rationalTorusUnipotentQuotientMeasure_eq_mul_setLIntegral_iwasawa ideleNorm_det_globalPoints isClosed_rationalTorusUnipotent isFundamentalDomain_boxSheet_rationalTorusUnipotent isHaarMeasure_rationalTorusUnipotentHaar_and_isMulRightInvariant"
namespace PseudoEisensteinDensity
p2m_open "AutomorphicForm"

private def seqLimitOrZero (s : ℕ → ℂ) : ℂ :=
  if ∃ L : ℂ, Tendsto s atTop (𝓝 L) then limUnder atTop s else 0

private theorem seqLimitOrZero_eq_of_tendsto {s : ℕ → ℂ} {L : ℂ} (h : Tendsto s atTop (𝓝 L)) :
    seqLimitOrZero s = L := by
  rw [seqLimitOrZero, if_pos ⟨L, h⟩]
  exact h.limUnder_eq

private theorem seqLimitOrZero_const_mul (c : ℂ) (hc : c ≠ 0) (s : ℕ → ℂ) :
    seqLimitOrZero (fun n => c * s n) = c * seqLimitOrZero s := by
  by_cases h : ∃ L : ℂ, Tendsto s atTop (𝓝 L)
  · obtain ⟨L, hL⟩ := h
    rw [seqLimitOrZero_eq_of_tendsto hL, seqLimitOrZero_eq_of_tendsto (hL.const_mul c)]
  · have h' : ¬ ∃ L : ℂ, Tendsto (fun n => c * s n) atTop (𝓝 L) := by
      rintro ⟨L, hL⟩
      refine h ⟨c⁻¹ * L, ?_⟩
      have := hL.const_mul c⁻¹
      simpa [inv_mul_cancel_left₀ hc] using this
    simp only [seqLimitOrZero, if_neg h, if_neg h', mul_zero]

variable (F : Type) [Field F] [NumberField F]

private theorem isAutomorphicFnAt_iff_isLsXiFunction_and_memLp (pins : CarrierPins F) (ξ : pins.Z →* ℂˣ)
    (φ : AdelicGL2 (𝓞 F) F → ℂ) :
    IsAutomorphicFnAt F pins ξ φ ↔
      letI := pins.mS
      IsLsXiFunction (𝓞 F) F pins.Z ξ φ ∧ MemLp φ 2 (pins.μ.restrict pins.D) := by
  letI := pins.mS
  exact lsXiMemberAt_iff (𝓞 F) F pins.μ pins.Z ξ pins.D φ

private theorem exists_isAutomorphicFnAt_of_ae_tendsto (pins : CarrierPins F) (ξ : pins.Z →* ℂˣ)
    (u : ℕ → AdelicGL2 (𝓞 F) F → ℂ) (hu : ∀ n, IsAutomorphicFnAt F pins ξ (u n))
    (v : AdelicGL2 (𝓞 F) F → ℂ)
    (hv : letI := pins.mS; MemLp v 2 (pins.μ.restrict pins.D))
    (hlim : letI := pins.mS;
      ∀ᵐ g ∂(pins.μ.restrict pins.D), Tendsto (fun n => u n g) atTop (𝓝 (v g))) :
    ∃ U : AdelicGL2 (𝓞 F) F → ℂ, IsAutomorphicFnAt F pins ξ U ∧
      (letI := pins.mS; U =ᵐ[pins.μ.restrict pins.D] v) := by
  letI := pins.mS
  have hu' : ∀ n, IsLsXiFunction (𝓞 F) F pins.Z ξ (u n) := fun n =>
    ((isAutomorphicFnAt_iff_isLsXiFunction_and_memLp F pins ξ (u n)).1 (hu n)).1
  set U : AdelicGL2 (𝓞 F) F → ℂ := fun g => seqLimitOrZero (fun n => u n g) with hUdef
  have hUv : U =ᵐ[pins.μ.restrict pins.D] v :=
    hlim.mono fun g hg => seqLimitOrZero_eq_of_tendsto hg
  refine ⟨U, (isAutomorphicFnAt_iff_isLsXiFunction_and_memLp F pins ξ U).2 ⟨⟨?_, ?_⟩, ?_⟩, hUv⟩
  · intro γ g
    simp only [hUdef]
    congr 1
    funext n
    exact (hu' n).left_invariant γ g
  · intro z g
    simp only [hUdef]
    have hz : ((ξ z : ℂˣ) : ℂ) ≠ 0 := Units.ne_zero (ξ z)
    rw [← seqLimitOrZero_const_mul _ hz]
    congr 1
    funext n
    exact (hu' n).central_transform z g
  · exact hv.ae_eq hUv.symm

private theorem exists_isAutomorphicFnAt_of_tendsto_eLpNorm (pins : CarrierPins F) (ξ : pins.Z →* ℂˣ)
    (u : ℕ → AdelicGL2 (𝓞 F) F → ℂ) (hu : ∀ n, IsAutomorphicFnAt F pins ξ (u n))
    (v : AdelicGL2 (𝓞 F) F → ℂ)
    (hv : letI := pins.mS; MemLp v 2 (pins.μ.restrict pins.D))
    (hconv : letI := pins.mS;
      Tendsto (fun n => eLpNorm (u n - v) 2 (pins.μ.restrict pins.D)) atTop (𝓝 0)) :
    ∃ U : AdelicGL2 (𝓞 F) F → ℂ, IsAutomorphicFnAt F pins ξ U ∧
      (letI := pins.mS; U =ᵐ[pins.μ.restrict pins.D] v) := by
  letI := pins.mS
  have hmeas : ∀ n, AEStronglyMeasurable (u n) (pins.μ.restrict pins.D) := fun n =>
    ((isAutomorphicFnAt_iff_isLsXiFunction_and_memLp F pins ξ (u n)).1 (hu n)).2.1
  have hinm : TendstoInMeasure (pins.μ.restrict pins.D) u atTop v :=
    tendstoInMeasure_of_tendsto_eLpNorm (by norm_num) hmeas hv.1 hconv
  obtain ⟨ns, -, hae⟩ := hinm.exists_seq_tendsto_ae
  exact exists_isAutomorphicFnAt_of_ae_tendsto F pins ξ (fun i => u (ns i)) (fun i => hu (ns i))
    v hv hae

end AutomorphicForm.PseudoEisensteinDensity
p2m_reactivate "P2MW.S_AutomorphicForm_exists_isSlabProfile_eLpNorm_sub_pseudoEisenstein_lt_of_forall_setIntegral_eq_zero_slab.SlabPairingDescent P2MW.S_AutomorphicForm_exists_isSlabProfile_eLpNorm_sub_pseudoEisenstein_lt_of_forall_setIntegral_eq_zero_slab.AutomorphicForm P2MW.S_AutomorphicForm_exists_isSlabProfile_eLpNorm_sub_pseudoEisenstein_lt_of_forall_setIntegral_eq_zero_slab.AutomorphicForm.TwistedCentralAverage"
p2m_reactivate "P2MW.S_AutomorphicForm_exists_isSlabProfile_eLpNorm_sub_pseudoEisenstein_lt_of_forall_setIntegral_eq_zero_slab.SlabPairingDescent P2MW.S_AutomorphicForm_exists_isSlabProfile_eLpNorm_sub_pseudoEisenstein_lt_of_forall_setIntegral_eq_zero_slab.AutomorphicForm P2MW.S_AutomorphicForm_exists_isSlabProfile_eLpNorm_sub_pseudoEisenstein_lt_of_forall_setIntegral_eq_zero_slab.AutomorphicForm.TwistedCentralAverage"

end
p2m_reactivate "P2MW.S_AutomorphicForm_exists_isSlabProfile_eLpNorm_sub_pseudoEisenstein_lt_of_forall_setIntegral_eq_zero_slab.SlabPairingDescent P2MW.S_AutomorphicForm_exists_isSlabProfile_eLpNorm_sub_pseudoEisenstein_lt_of_forall_setIntegral_eq_zero_slab.AutomorphicForm P2MW.S_AutomorphicForm_exists_isSlabProfile_eLpNorm_sub_pseudoEisenstein_lt_of_forall_setIntegral_eq_zero_slab.AutomorphicForm.TwistedCentralAverage"

end
p2m_reactivate "P2MW.S_AutomorphicForm_exists_isSlabProfile_eLpNorm_sub_pseudoEisenstein_lt_of_forall_setIntegral_eq_zero_slab.SlabPairingDescent P2MW.S_AutomorphicForm_exists_isSlabProfile_eLpNorm_sub_pseudoEisenstein_lt_of_forall_setIntegral_eq_zero_slab.AutomorphicForm P2MW.S_AutomorphicForm_exists_isSlabProfile_eLpNorm_sub_pseudoEisenstein_lt_of_forall_setIntegral_eq_zero_slab.AutomorphicForm.TwistedCentralAverage"

section

open MeasureTheory NumberField Filter Topology
open NumberField.AdelicHaar NumberField.AdelicLevel NumberField.AdelicBox
p2m_open "AutomorphicForm P2MW.S_AutomorphicForm_exists_isSlabProfile_eLpNorm_sub_pseudoEisenstein_lt_of_forall_setIntegral_eq_zero_slab.AutomorphicForm"

attribute [local instance] NumberField.AdelicHaar.glBorel NumberField.AdelicHaar.adeleBorel
attribute [local instance] NumberField.AdelicHaar.borelSpace_glBorel NumberField.AdelicHaar.borelSpace_adeleBorel

noncomputable section

set_option autoImplicit false

namespace AutomorphicForm
p2m_export "AutomorphicForm" "lsXiMemberAt_iff IsAutomorphicFnAt CarrierPins productionPinsOf AdelicGL2 globalPoints centralScalar IsLsXiFunction unipotentGL2 unipotentGL2_coe constantTermIntegrand constantTerm IsSlabProfile pseudoEisenstein pseudoEisenstein_apply isSlabProfile_zero pseudoEisenstein_zero borelSubgroup mem_borelSubgroup_iff globalPoints_apply gl2Weyl adelicWeyl WindowedSiegel.rowNormSq WindowedSiegel.localHeight WindowedSiegel.archHeight WindowedSiegel.archHeight_scalar_entries_mul finite_support_pseudoEisenstein_summand isAutomorphicFnAt_pseudoEisenstein_slab aestronglyMeasurable_adelicGLHaar_of_isAutomorphicFnAt_slab setIntegral_pseudoEisenstein_mul_conj_eq_setIntegral_rationalTorusUnipotentQuotient_slab rationalTorusUnipotent RationalTorusUnipotentQuotient rationalTorusUnipotentHaar rationalTorusUnipotentQuotientMeasure toAdelicUnipotent adelicMaximalCompact isCompact_adelicMaximalCompact maximalCompactHaar constantTerm_adelicBox_globalPoints_mul_of_mem_borelSubgroup constantTerm_adelicBox_unipotentGL2_mul continuous_unipotentGL2 exists_isFundamentalDomain_globalPoints_range exists_lintegral_rationalTorusUnipotentQuotientMeasure_eq_mul_setLIntegral_iwasawa ideleNorm_det_globalPoints isClosed_rationalTorusUnipotent isFundamentalDomain_boxSheet_rationalTorusUnipotent isHaarMeasure_rationalTorusUnipotentHaar_and_isMulRightInvariant"
namespace PseudoEisensteinDensity
p2m_open "AutomorphicForm"

variable (F : Type) [Field F] [NumberField F]

private abbrev pins (Φ : Set (AdelicGL2 (𝓞 F) F)) : CarrierPins F :=
  productionPinsOf F Φ (fun N => levelOne (𝓞 F) F N) (fun v => heckeGen (𝓞 F) F v) (adelicBox F)

private abbrev bruhatTerm (φ : AdelicGL2 (𝓞 F) F → ℂ) (g : AdelicGL2 (𝓞 F) F) (β : F) : ℂ :=
  φ (adelicWeyl (𝓞 F) F * unipotentGL2 (algebraMap F (AdeleRing (𝓞 F) F) β) * g)

section Automorphic

variable (Φ : Set (AdelicGL2 (𝓞 F) F)) (ξ : (pins F Φ).Z →* ℂˣ)

private theorem isLsXiFunction_of_isAutomorphicFnAt (u : AdelicGL2 (𝓞 F) F → ℂ)
    (hu : IsAutomorphicFnAt F (pins F Φ) ξ u) : IsLsXiFunction (𝓞 F) F (pins F Φ).Z ξ u :=
  ((lsXiMemberAt_iff (𝓞 F) F (pins F Φ).μ (pins F Φ).Z ξ (pins F Φ).D u).1 hu).1

private theorem memLp_of_isAutomorphicFnAt (u : AdelicGL2 (𝓞 F) F → ℂ)
    (hu : IsAutomorphicFnAt F (pins F Φ) ξ u) : MemLp u 2 ((adelicGLHaar (Fin 2) (𝓞 F) F).restrict Φ) :=
  ((lsXiMemberAt_iff (𝓞 F) F (pins F Φ).μ (pins F Φ).Z ξ (pins F Φ).D u).1 hu).2

private theorem isAutomorphicFnAt_of_isLsXiFunction_of_memLp (u : AdelicGL2 (𝓞 F) F → ℂ)
    (h1 : IsLsXiFunction (𝓞 F) F (pins F Φ).Z ξ u)
    (h2 : MemLp u 2 ((adelicGLHaar (Fin 2) (𝓞 F) F).restrict Φ)) : IsAutomorphicFnAt F (pins F Φ) ξ u :=
  (lsXiMemberAt_iff (𝓞 F) F (pins F Φ).μ (pins F Φ).Z ξ (pins F Φ).D u).2 ⟨h1, h2⟩

private theorem isAutomorphicFnAt_add (v w : AdelicGL2 (𝓞 F) F → ℂ) (hv : IsAutomorphicFnAt F (pins F Φ) ξ v)
    (hw : IsAutomorphicFnAt F (pins F Φ) ξ w) : IsAutomorphicFnAt F (pins F Φ) ξ (v + w) := by
  have hvL := isLsXiFunction_of_isAutomorphicFnAt F Φ ξ v hv
  have hwL := isLsXiFunction_of_isAutomorphicFnAt F Φ ξ w hw
  refine isAutomorphicFnAt_of_isLsXiFunction_of_memLp F Φ ξ _ ⟨fun γ g => ?_, fun z g => ?_⟩
    ((memLp_of_isAutomorphicFnAt F Φ ξ v hv).add (memLp_of_isAutomorphicFnAt F Φ ξ w hw))
  · simp only [Pi.add_apply, hvL.left_invariant, hwL.left_invariant]
  · simp only [Pi.add_apply, hvL.central_transform, hwL.central_transform, mul_add]

private theorem isAutomorphicFnAt_smul (c : ℂ) (v : AdelicGL2 (𝓞 F) F → ℂ)
    (hv : IsAutomorphicFnAt F (pins F Φ) ξ v) : IsAutomorphicFnAt F (pins F Φ) ξ (c • v) := by
  have hvL := isLsXiFunction_of_isAutomorphicFnAt F Φ ξ v hv
  refine isAutomorphicFnAt_of_isLsXiFunction_of_memLp F Φ ξ _ ⟨fun γ g => ?_, fun z g => ?_⟩
    ((memLp_of_isAutomorphicFnAt F Φ ξ v hv).const_smul c)
  · simp only [Pi.smul_apply, hvL.left_invariant]
  · simp only [Pi.smul_apply, hvL.central_transform, smul_eq_mul]
    ring

private theorem isAutomorphicFnAt_sub (v w : AdelicGL2 (𝓞 F) F → ℂ) (hv : IsAutomorphicFnAt F (pins F Φ) ξ v)
    (hw : IsAutomorphicFnAt F (pins F Φ) ξ w) : IsAutomorphicFnAt F (pins F Φ) ξ (v - w) := by
  have h := isAutomorphicFnAt_add F Φ ξ v ((-1 : ℂ) • w) hv (isAutomorphicFnAt_smul F Φ ξ (-1) w hw)
  have heq : v + (-1 : ℂ) • w = v - w := by
    funext g
    simp only [Pi.add_apply, Pi.smul_apply, Pi.sub_apply, smul_eq_mul]
    ring
  rw [heq] at h
  exact h

end Automorphic
p2m_reactivate "P2MW.S_AutomorphicForm_exists_isSlabProfile_eLpNorm_sub_pseudoEisenstein_lt_of_forall_setIntegral_eq_zero_slab.SlabPairingDescent P2MW.S_AutomorphicForm_exists_isSlabProfile_eLpNorm_sub_pseudoEisenstein_lt_of_forall_setIntegral_eq_zero_slab.AutomorphicForm P2MW.S_AutomorphicForm_exists_isSlabProfile_eLpNorm_sub_pseudoEisenstein_lt_of_forall_setIntegral_eq_zero_slab.AutomorphicForm.TwistedCentralAverage"

section Profiles

variable {F}

private theorem isSlabProfile_zero' (Z : Subgroup (AdeleRing (𝓞 F) F)ˣ) (ξ : Z →* ℂˣ) :
    IsSlabProfile F Z ξ (0 : AdelicGL2 (𝓞 F) F → ℂ) :=
  isSlabProfile_zero Z ξ

private theorem isSlabProfile_add {Z : Subgroup (AdeleRing (𝓞 F) F)ˣ} {ξ : Z →* ℂˣ}
    {φ ψ : AdelicGL2 (𝓞 F) F → ℂ} (hφ : IsSlabProfile F Z ξ φ) (hψ : IsSlabProfile F Z ξ ψ) :
    IsSlabProfile F Z ξ (φ + ψ) where
  measurable := hφ.measurable.add hψ.measurable
  unipotent_mul := fun x g => by simp only [Pi.add_apply, hφ.unipotent_mul x g, hψ.unipotent_mul x g]
  borel_mul := fun γ hγ g => by simp only [Pi.add_apply, hφ.borel_mul γ hγ g, hψ.borel_mul γ hγ g]
  central_transform := fun z g => by
    simp only [Pi.add_apply, hφ.central_transform z g, hψ.central_transform z g, mul_add]
  bounded_on_slab := by
    intro d₁ d₂ hd₁
    obtain ⟨C₁, hC₁⟩ := hφ.bounded_on_slab d₁ d₂ hd₁
    obtain ⟨C₂, hC₂⟩ := hψ.bounded_on_slab d₁ d₂ hd₁
    exact ⟨C₁ + C₂, fun g hg => (norm_add_le (φ g) (ψ g)).trans (add_le_add (hC₁ g hg) (hC₂ g hg))⟩
  height_band := by
    obtain ⟨a₁, b₁, ha₁, h₁⟩ := hφ.height_band
    obtain ⟨a₂, b₂, ha₂, h₂⟩ := hψ.height_band
    refine ⟨min a₁ a₂, max b₁ b₂, lt_min ha₁ ha₂, fun g hg => ?_⟩
    by_cases hφg : φ g = 0
    · have hψg : ψ g ≠ 0 := fun hψ0 => hg (by simp only [Pi.add_apply, hφg, hψ0, add_zero])
      obtain ⟨hl, hu⟩ := h₂ g hψg
      exact ⟨(min_le_right a₁ a₂).trans hl, hu.trans (le_max_right b₁ b₂)⟩
    · obtain ⟨hl, hu⟩ := h₁ g hφg
      exact ⟨(min_le_left a₁ a₂).trans hl, hu.trans (le_max_left b₁ b₂)⟩

private theorem isSlabProfile_smul {Z : Subgroup (AdeleRing (𝓞 F) F)ˣ} {ξ : Z →* ℂˣ} (c : ℂ)
    {φ : AdelicGL2 (𝓞 F) F → ℂ} (hφ : IsSlabProfile F Z ξ φ) : IsSlabProfile F Z ξ (c • φ) where
  measurable := hφ.measurable.const_smul c
  unipotent_mul := fun x g => by simp only [Pi.smul_apply, hφ.unipotent_mul x g]
  borel_mul := fun γ hγ g => by simp only [Pi.smul_apply, hφ.borel_mul γ hγ g]
  central_transform := fun z g => by
    simp only [Pi.smul_apply, hφ.central_transform z g, smul_eq_mul]
    ring
  bounded_on_slab := by
    intro d₁ d₂ hd₁
    obtain ⟨C, hC⟩ := hφ.bounded_on_slab d₁ d₂ hd₁
    refine ⟨‖c‖ * C, fun g hg => ?_⟩
    simp only [Pi.smul_apply, smul_eq_mul, norm_mul]
    exact mul_le_mul_of_nonneg_left (hC g hg) (norm_nonneg c)
  height_band := by
    obtain ⟨a, b, ha, h⟩ := hφ.height_band
    refine ⟨a, b, ha, fun g hg => h g fun h0 => hg ?_⟩
    simp only [Pi.smul_apply, h0, smul_zero]

variable (F)

private theorem pseudoEisenstein_zero' : pseudoEisenstein F (0 : AdelicGL2 (𝓞 F) F → ℂ) = 0 :=
  pseudoEisenstein_zero

private theorem pseudoEisenstein_add (φ ψ : AdelicGL2 (𝓞 F) F → ℂ)
    (hφ : ∀ g : AdelicGL2 (𝓞 F) F, (Function.support (bruhatTerm F φ g)).Finite)
    (hψ : ∀ g : AdelicGL2 (𝓞 F) F, (Function.support (bruhatTerm F ψ g)).Finite) :
    pseudoEisenstein F (φ + ψ) = pseudoEisenstein F φ + pseudoEisenstein F ψ := by
  funext g
  have hφs : Summable (bruhatTerm F φ g) := summable_of_hasFiniteSupport (hφ g)
  have hψs : Summable (bruhatTerm F ψ g) := summable_of_hasFiniteSupport (hψ g)
  simp only [Pi.add_apply, pseudoEisenstein_apply]
  rw [hφs.tsum_add hψs]
  ring

private theorem pseudoEisenstein_smul (c : ℂ) (φ : AdelicGL2 (𝓞 F) F → ℂ) :
    pseudoEisenstein F (c • φ) = c • pseudoEisenstein F φ := by
  funext g
  simp only [Pi.smul_apply, pseudoEisenstein_apply, smul_eq_mul, tsum_mul_left, mul_add]

end Profiles
p2m_reactivate "P2MW.S_AutomorphicForm_exists_isSlabProfile_eLpNorm_sub_pseudoEisenstein_lt_of_forall_setIntegral_eq_zero_slab.SlabPairingDescent P2MW.S_AutomorphicForm_exists_isSlabProfile_eLpNorm_sub_pseudoEisenstein_lt_of_forall_setIntegral_eq_zero_slab.AutomorphicForm P2MW.S_AutomorphicForm_exists_isSlabProfile_eLpNorm_sub_pseudoEisenstein_lt_of_forall_setIntegral_eq_zero_slab.AutomorphicForm.TwistedCentralAverage"

section Hilbert

variable (Φ : Set (AdelicGL2 (𝓞 F) F)) (ξ : (pins F Φ).Z →* ℂˣ)

private theorem inner_eq_setIntegral (φ ψ : Lp ℂ 2 ((adelicGLHaar (Fin 2) (𝓞 F) F).restrict Φ))
    (v w : AdelicGL2 (𝓞 F) F → ℂ)
    (hv : (φ : AdelicGL2 (𝓞 F) F → ℂ) =ᵐ[(adelicGLHaar (Fin 2) (𝓞 F) F).restrict Φ] v)
    (hw : (ψ : AdelicGL2 (𝓞 F) F → ℂ) =ᵐ[(adelicGLHaar (Fin 2) (𝓞 F) F).restrict Φ] w) :
    inner ℂ ψ φ = ∫ g in Φ, v g * (starRingEnd ℂ) (w g) ∂(adelicGLHaar (Fin 2) (𝓞 F) F) := by
  rw [MeasureTheory.L2.inner_def]
  refine integral_congr_ae ?_
  filter_upwards [hv, hw] with g hgv hgw
  rw [RCLike.inner_apply, hgv, hgw]

private def pseudoEisensteinSubmodule
    (hfin : ∀ φ : AdelicGL2 (𝓞 F) F → ℂ, IsSlabProfile F (pins F Φ).Z ξ φ →
      ∀ g : AdelicGL2 (𝓞 F) F, (Function.support (bruhatTerm F φ g)).Finite) :
    Submodule ℂ (Lp ℂ 2 ((adelicGLHaar (Fin 2) (𝓞 F) F).restrict Φ)) where
  carrier := {x | ∃ φ : AdelicGL2 (𝓞 F) F → ℂ, IsSlabProfile F (pins F Φ).Z ξ φ ∧
    (x : AdelicGL2 (𝓞 F) F → ℂ) =ᵐ[(adelicGLHaar (Fin 2) (𝓞 F) F).restrict Φ] pseudoEisenstein F φ}
  zero_mem' := ⟨0, isSlabProfile_zero' (pins F Φ).Z ξ, by
    rw [pseudoEisenstein_zero' F]
    exact Lp.coeFn_zero _ _ _⟩
  add_mem' := by
    rintro x y ⟨φ, hφ, hxφ⟩ ⟨ψ, hψ, hyψ⟩
    refine ⟨φ + ψ, isSlabProfile_add hφ hψ, (Lp.coeFn_add x y).trans ((hxφ.add hyψ).trans ?_)⟩
    exact Filter.EventuallyEq.of_eq (pseudoEisenstein_add F φ ψ (hfin φ hφ) (hfin ψ hψ)).symm
  smul_mem' := by
    rintro c x ⟨φ, hφ, hxφ⟩
    refine ⟨c • φ, isSlabProfile_smul c hφ, (Lp.coeFn_smul c x).trans ?_⟩
    rw [pseudoEisenstein_smul F c φ]
    exact hxφ.mono fun g hg => by simp only [Pi.smul_apply, hg]

private theorem mem_pseudoEisensteinSubmodule_iff
    (hfin : ∀ φ : AdelicGL2 (𝓞 F) F → ℂ, IsSlabProfile F (pins F Φ).Z ξ φ →
      ∀ g : AdelicGL2 (𝓞 F) F, (Function.support (bruhatTerm F φ g)).Finite)
    (x : Lp ℂ 2 ((adelicGLHaar (Fin 2) (𝓞 F) F).restrict Φ)) :
    x ∈ pseudoEisensteinSubmodule F Φ ξ hfin ↔ ∃ φ : AdelicGL2 (𝓞 F) F → ℂ,
      IsSlabProfile F (pins F Φ).Z ξ φ ∧
        (x : AdelicGL2 (𝓞 F) F → ℂ) =ᵐ[(adelicGLHaar (Fin 2) (𝓞 F) F).restrict Φ] pseudoEisenstein F φ :=
  Iff.rfl

private theorem exists_isSlabProfile_eLpNorm_sub_pseudoEisenstein_lt
    (hfin : ∀ φ : AdelicGL2 (𝓞 F) F → ℂ, IsSlabProfile F (pins F Φ).Z ξ φ →
      ∀ g : AdelicGL2 (𝓞 F) F, (Function.support (bruhatTerm F φ g)).Finite)
    (hcomplete : ∀ (useq : ℕ → AdelicGL2 (𝓞 F) F → ℂ) (v : AdelicGL2 (𝓞 F) F → ℂ),
      (∀ n, IsAutomorphicFnAt F (pins F Φ) ξ (useq n)) →
      MemLp v 2 ((adelicGLHaar (Fin 2) (𝓞 F) F).restrict Φ) →
      Tendsto (fun n => eLpNorm (useq n - v) 2 ((adelicGLHaar (Fin 2) (𝓞 F) F).restrict Φ)) atTop (𝓝 0) →
      ∃ U, IsAutomorphicFnAt F (pins F Φ) ξ U ∧ U =ᵐ[(adelicGLHaar (Fin 2) (𝓞 F) F).restrict Φ] v)
    (htheta : ∀ φ : AdelicGL2 (𝓞 F) F → ℂ, IsSlabProfile F (pins F Φ).Z ξ φ →
      IsAutomorphicFnAt F (pins F Φ) ξ (pseudoEisenstein F φ))
    (hcusp : ∀ u : AdelicGL2 (𝓞 F) F → ℂ, IsAutomorphicFnAt F (pins F Φ) ξ u →
      (∀ φ : AdelicGL2 (𝓞 F) F → ℂ, IsSlabProfile F (pins F Φ).Z ξ φ →
        ∫ g in Φ, pseudoEisenstein F φ g * (starRingEnd ℂ) (u g) ∂(adelicGLHaar (Fin 2) (𝓞 F) F) = 0) →
      ∀ᵐ g ∂(adelicGLHaar (Fin 2) (𝓞 F) F), constantTerm (pins F Φ).ν unipotentGL2 u g = 0)
    (fe : AdelicGL2 (𝓞 F) F → ℂ) (hfe : IsAutomorphicFnAt F (pins F Φ) ξ fe)
    (hperp : ∀ u : AdelicGL2 (𝓞 F) F → ℂ, IsAutomorphicFnAt F (pins F Φ) ξ u →
      (∀ᵐ g ∂(adelicGLHaar (Fin 2) (𝓞 F) F), constantTerm (pins F Φ).ν unipotentGL2 u g = 0) →
      ∫ g in Φ, fe g * (starRingEnd ℂ) (u g) ∂(adelicGLHaar (Fin 2) (𝓞 F) F) = 0)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ φ : AdelicGL2 (𝓞 F) F → ℂ, IsSlabProfile F (pins F Φ).Z ξ φ ∧
      eLpNorm (fe - pseudoEisenstein F φ) 2 ((adelicGLHaar (Fin 2) (𝓞 F) F).restrict Φ) < ENNReal.ofReal ε := by

  let T := pseudoEisensteinSubmodule F Φ ξ hfin
  let M := T.topologicalClosure
  haveI : CompleteSpace M := (Submodule.isClosed_topologicalClosure _).completeSpace_coe

  have hfeM := memLp_of_isAutomorphicFnAt F Φ ξ fe hfe
  let feL : Lp ℂ 2 ((adelicGLHaar (Fin 2) (𝓞 F) F).restrict Φ) := hfeM.toLp fe
  have hfeL : (feL : AdelicGL2 (𝓞 F) F → ℂ) =ᵐ[(adelicGLHaar (Fin 2) (𝓞 F) F).restrict Φ] fe := hfeM.coeFn_toLp
  let m : Lp ℂ 2 ((adelicGLHaar (Fin 2) (𝓞 F) F).restrict Φ) := ↑(M.orthogonalProjection feL)
  have hmM : m ∈ M := (M.orthogonalProjection feL).2
  have hrem : feL - m ∈ Mᗮ := by
    have h := Submodule.sub_starProjection_mem_orthogonal (K := M) feL
    rwa [Submodule.starProjection_apply] at h
  have hmcl : m ∈ closure (T : Set (Lp ℂ 2 ((adelicGLHaar (Fin 2) (𝓞 F) F).restrict Φ))) := by
    rw [← Submodule.topologicalClosure_coe]
    exact hmM

  obtain ⟨yseq, hy, hym⟩ := mem_closure_iff_seq_limit.1 hmcl
  have hy' : ∀ n, ∃ φ : AdelicGL2 (𝓞 F) F → ℂ, IsSlabProfile F (pins F Φ).Z ξ φ ∧
      ((yseq n : Lp ℂ 2 _) : AdelicGL2 (𝓞 F) F → ℂ) =ᵐ[(adelicGLHaar (Fin 2) (𝓞 F) F).restrict Φ]
        pseudoEisenstein F φ :=
    fun n => hy n
  choose φseq hφseq hyφ using hy'
  have h1 := (Lp.tendsto_Lp_iff_tendsto_eLpNorm' yseq m).1 hym
  have h2 : Tendsto (fun n => eLpNorm (pseudoEisenstein F (φseq n) - (m : AdelicGL2 (𝓞 F) F → ℂ)) 2
      ((adelicGLHaar (Fin 2) (𝓞 F) F).restrict Φ)) atTop (𝓝 0) := by
    refine (Filter.tendsto_congr fun n => ?_).1 h1
    exact eLpNorm_congr_ae ((hyφ n).sub Filter.EventuallyEq.rfl)
  obtain ⟨V, hV, hVm⟩ :=
    hcomplete (fun n => pseudoEisenstein F (φseq n)) m (fun n => htheta _ (hφseq n)) (Lp.memLp m) h2

  have hu : IsAutomorphicFnAt F (pins F Φ) ξ (fe - V) := isAutomorphicFnAt_sub F Φ ξ fe V hfe hV
  have huL : ((feL - m : Lp ℂ 2 _) : AdelicGL2 (𝓞 F) F → ℂ) =ᵐ[(adelicGLHaar (Fin 2) (𝓞 F) F).restrict Φ]
      fe - V :=
    (Lp.coeFn_sub feL m).trans (hfeL.sub hVm.symm)
  have horth : ∀ φ : AdelicGL2 (𝓞 F) F → ℂ, IsSlabProfile F (pins F Φ).Z ξ φ →
      ∫ g in Φ, pseudoEisenstein F φ g * (starRingEnd ℂ) ((fe - V) g) ∂(adelicGLHaar (Fin 2) (𝓞 F) F) = 0 := by
    intro φ hφ
    have hθM := memLp_of_isAutomorphicFnAt F Φ ξ _ (htheta φ hφ)
    let θL : Lp ℂ 2 ((adelicGLHaar (Fin 2) (𝓞 F) F).restrict Φ) := hθM.toLp (pseudoEisenstein F φ)
    have hθL : (θL : AdelicGL2 (𝓞 F) F → ℂ) =ᵐ[(adelicGLHaar (Fin 2) (𝓞 F) F).restrict Φ] pseudoEisenstein F φ :=
      hθM.coeFn_toLp
    have hθM' : θL ∈ M := Submodule.le_topologicalClosure _ ⟨φ, hφ, hθL⟩
    rw [← inner_eq_setIntegral F Φ θL (feL - m) (pseudoEisenstein F φ) (fe - V) hθL huL]
    exact Submodule.inner_left_of_mem_orthogonal hθM' hrem
  have hcuspu := hcusp (fe - V) hu horth

  have hA : inner ℂ (feL - m) feL = 0 := by
    rw [inner_eq_setIntegral F Φ feL (feL - m) fe (fe - V) hfeL huL]
    exact hperp (fe - V) hu hcuspu
  have hB : inner ℂ (feL - m) m = 0 := Submodule.inner_left_of_mem_orthogonal hmM hrem
  have hzero : feL - m = 0 := by
    rw [← inner_self_eq_zero (𝕜 := ℂ), inner_sub_right, hA, hB, sub_zero]
  have hfem : (m : AdelicGL2 (𝓞 F) F → ℂ) =ᵐ[(adelicGLHaar (Fin 2) (𝓞 F) F).restrict Φ] fe := by
    rw [← sub_eq_zero.1 hzero]
    exact hfeL

  obtain ⟨y, hyT, hdist⟩ := Metric.mem_closure_iff.1 hmcl ε hε
  obtain ⟨φ, hφ, hyφ'⟩ := hyT
  refine ⟨φ, hφ, ?_⟩
  have hne : eLpNorm ((m : AdelicGL2 (𝓞 F) F → ℂ) - (y : AdelicGL2 (𝓞 F) F → ℂ)) 2
      ((adelicGLHaar (Fin 2) (𝓞 F) F).restrict Φ) ≠ ⊤ := ((Lp.memLp m).sub (Lp.memLp y)).eLpNorm_ne_top
  have heq : eLpNorm (fe - pseudoEisenstein F φ) 2 ((adelicGLHaar (Fin 2) (𝓞 F) F).restrict Φ) =
      eLpNorm ((m : AdelicGL2 (𝓞 F) F → ℂ) - (y : AdelicGL2 (𝓞 F) F → ℂ)) 2
        ((adelicGLHaar (Fin 2) (𝓞 F) F).restrict Φ) :=
    eLpNorm_congr_ae (hfem.symm.sub hyφ'.symm)
  rw [heq, ENNReal.lt_ofReal_iff_toReal_lt hne, ← Lp.dist_def]
  exact hdist

end Hilbert
p2m_reactivate "P2MW.S_AutomorphicForm_exists_isSlabProfile_eLpNorm_sub_pseudoEisenstein_lt_of_forall_setIntegral_eq_zero_slab.SlabPairingDescent P2MW.S_AutomorphicForm_exists_isSlabProfile_eLpNorm_sub_pseudoEisenstein_lt_of_forall_setIntegral_eq_zero_slab.AutomorphicForm P2MW.S_AutomorphicForm_exists_isSlabProfile_eLpNorm_sub_pseudoEisenstein_lt_of_forall_setIntegral_eq_zero_slab.AutomorphicForm.TwistedCentralAverage"

end AutomorphicForm.PseudoEisensteinDensity
p2m_reactivate "P2MW.S_AutomorphicForm_exists_isSlabProfile_eLpNorm_sub_pseudoEisenstein_lt_of_forall_setIntegral_eq_zero_slab.SlabPairingDescent P2MW.S_AutomorphicForm_exists_isSlabProfile_eLpNorm_sub_pseudoEisenstein_lt_of_forall_setIntegral_eq_zero_slab.AutomorphicForm P2MW.S_AutomorphicForm_exists_isSlabProfile_eLpNorm_sub_pseudoEisenstein_lt_of_forall_setIntegral_eq_zero_slab.AutomorphicForm.TwistedCentralAverage"
p2m_reactivate "P2MW.S_AutomorphicForm_exists_isSlabProfile_eLpNorm_sub_pseudoEisenstein_lt_of_forall_setIntegral_eq_zero_slab.SlabPairingDescent P2MW.S_AutomorphicForm_exists_isSlabProfile_eLpNorm_sub_pseudoEisenstein_lt_of_forall_setIntegral_eq_zero_slab.AutomorphicForm P2MW.S_AutomorphicForm_exists_isSlabProfile_eLpNorm_sub_pseudoEisenstein_lt_of_forall_setIntegral_eq_zero_slab.AutomorphicForm.TwistedCentralAverage"

end
p2m_reactivate "P2MW.S_AutomorphicForm_exists_isSlabProfile_eLpNorm_sub_pseudoEisenstein_lt_of_forall_setIntegral_eq_zero_slab.SlabPairingDescent P2MW.S_AutomorphicForm_exists_isSlabProfile_eLpNorm_sub_pseudoEisenstein_lt_of_forall_setIntegral_eq_zero_slab.AutomorphicForm P2MW.S_AutomorphicForm_exists_isSlabProfile_eLpNorm_sub_pseudoEisenstein_lt_of_forall_setIntegral_eq_zero_slab.AutomorphicForm.TwistedCentralAverage"

end
p2m_reactivate "P2MW.S_AutomorphicForm_exists_isSlabProfile_eLpNorm_sub_pseudoEisenstein_lt_of_forall_setIntegral_eq_zero_slab.SlabPairingDescent P2MW.S_AutomorphicForm_exists_isSlabProfile_eLpNorm_sub_pseudoEisenstein_lt_of_forall_setIntegral_eq_zero_slab.AutomorphicForm P2MW.S_AutomorphicForm_exists_isSlabProfile_eLpNorm_sub_pseudoEisenstein_lt_of_forall_setIntegral_eq_zero_slab.AutomorphicForm.TwistedCentralAverage"

section

open MeasureTheory NumberField Filter Topology
open NumberField.AdelicHaar NumberField.AdelicLevel NumberField.AdelicBox
p2m_open "AutomorphicForm P2MW.S_AutomorphicForm_exists_isSlabProfile_eLpNorm_sub_pseudoEisenstein_lt_of_forall_setIntegral_eq_zero_slab.AutomorphicForm P2MW.S_AutomorphicForm_exists_isSlabProfile_eLpNorm_sub_pseudoEisenstein_lt_of_forall_setIntegral_eq_zero_slab.AutomorphicForm.PseudoEisensteinDensity"

attribute [local instance] NumberField.AdelicHaar.glBorel NumberField.AdelicHaar.adeleBorel

noncomputable section

set_option autoImplicit false

namespace AutomorphicForm
p2m_export "AutomorphicForm" "lsXiMemberAt_iff IsAutomorphicFnAt CarrierPins productionPinsOf AdelicGL2 globalPoints centralScalar IsLsXiFunction unipotentGL2 unipotentGL2_coe constantTermIntegrand constantTerm IsSlabProfile pseudoEisenstein pseudoEisenstein_apply isSlabProfile_zero pseudoEisenstein_zero borelSubgroup mem_borelSubgroup_iff globalPoints_apply gl2Weyl adelicWeyl WindowedSiegel.rowNormSq WindowedSiegel.localHeight WindowedSiegel.archHeight WindowedSiegel.archHeight_scalar_entries_mul finite_support_pseudoEisenstein_summand isAutomorphicFnAt_pseudoEisenstein_slab aestronglyMeasurable_adelicGLHaar_of_isAutomorphicFnAt_slab setIntegral_pseudoEisenstein_mul_conj_eq_setIntegral_rationalTorusUnipotentQuotient_slab rationalTorusUnipotent RationalTorusUnipotentQuotient rationalTorusUnipotentHaar rationalTorusUnipotentQuotientMeasure toAdelicUnipotent adelicMaximalCompact isCompact_adelicMaximalCompact maximalCompactHaar constantTerm_adelicBox_globalPoints_mul_of_mem_borelSubgroup constantTerm_adelicBox_unipotentGL2_mul continuous_unipotentGL2 exists_isFundamentalDomain_globalPoints_range exists_lintegral_rationalTorusUnipotentQuotientMeasure_eq_mul_setLIntegral_iwasawa ideleNorm_det_globalPoints isClosed_rationalTorusUnipotent isFundamentalDomain_boxSheet_rationalTorusUnipotent isHaarMeasure_rationalTorusUnipotentHaar_and_isMulRightInvariant"
namespace PseudoEisensteinDensity
p2m_open "AutomorphicForm"

private theorem ae_constantTerm_eq_zero_of_forall_setIntegral_pseudoEisenstein_mul_conj_eq_zero
    (F : Type) [Field F] [NumberField F]
    (d₁ d₂ : ℝ) (_hd₁ : 0 < d₁) (_hd : d₁ < d₂)
    (Φ : Set (AdelicGL2 (𝓞 F) F))
    (_hΦs : Φ ⊆ {g | NumberField.TateGlobal.ideleNorm F (Matrix.GeneralLinearGroup.det g) ∈ Set.Icc d₁ d₂})
    (_hΦ : IsFundamentalDomain (globalPoints (𝓞 F) F).range Φ
      ((adelicGLHaar (Fin 2) (𝓞 F) F).restrict {g | NumberField.TateGlobal.ideleNorm F
          (Matrix.GeneralLinearGroup.det g) ∈ Set.Icc d₁ d₂}))
    (ξ : (pins F Φ).Z →* ℂˣ) (_hξ : Continuous ξ)
    (u : AdelicGL2 (𝓞 F) F → ℂ) (_hu : IsAutomorphicFnAt F (pins F Φ) ξ u)
    (_horth : ∀ φ : AdelicGL2 (𝓞 F) F → ℂ, IsSlabProfile F (pins F Φ).Z ξ φ →
      ∫ g in Φ, pseudoEisenstein F φ g * (starRingEnd ℂ) (u g) ∂(adelicGLHaar (Fin 2) (𝓞 F) F) = 0) :
    ∀ᵐ g ∂(adelicGLHaar (Fin 2) (𝓞 F) F), constantTerm (pins F Φ).ν unipotentGL2 u g = 0 :=
  Integration.main F d₁ d₂ _hd₁ _hd Φ _hΦs _hΦ ξ _hξ u _hu _horth

end AutomorphicForm.PseudoEisensteinDensity
p2m_reactivate "P2MW.S_AutomorphicForm_exists_isSlabProfile_eLpNorm_sub_pseudoEisenstein_lt_of_forall_setIntegral_eq_zero_slab.SlabPairingDescent P2MW.S_AutomorphicForm_exists_isSlabProfile_eLpNorm_sub_pseudoEisenstein_lt_of_forall_setIntegral_eq_zero_slab.AutomorphicForm P2MW.S_AutomorphicForm_exists_isSlabProfile_eLpNorm_sub_pseudoEisenstein_lt_of_forall_setIntegral_eq_zero_slab.AutomorphicForm.TwistedCentralAverage"
p2m_reactivate "P2MW.S_AutomorphicForm_exists_isSlabProfile_eLpNorm_sub_pseudoEisenstein_lt_of_forall_setIntegral_eq_zero_slab.SlabPairingDescent P2MW.S_AutomorphicForm_exists_isSlabProfile_eLpNorm_sub_pseudoEisenstein_lt_of_forall_setIntegral_eq_zero_slab.AutomorphicForm P2MW.S_AutomorphicForm_exists_isSlabProfile_eLpNorm_sub_pseudoEisenstein_lt_of_forall_setIntegral_eq_zero_slab.AutomorphicForm.TwistedCentralAverage"

end
p2m_reactivate "P2MW.S_AutomorphicForm_exists_isSlabProfile_eLpNorm_sub_pseudoEisenstein_lt_of_forall_setIntegral_eq_zero_slab.SlabPairingDescent P2MW.S_AutomorphicForm_exists_isSlabProfile_eLpNorm_sub_pseudoEisenstein_lt_of_forall_setIntegral_eq_zero_slab.AutomorphicForm P2MW.S_AutomorphicForm_exists_isSlabProfile_eLpNorm_sub_pseudoEisenstein_lt_of_forall_setIntegral_eq_zero_slab.AutomorphicForm.TwistedCentralAverage"

end
p2m_reactivate "P2MW.S_AutomorphicForm_exists_isSlabProfile_eLpNorm_sub_pseudoEisenstein_lt_of_forall_setIntegral_eq_zero_slab.SlabPairingDescent P2MW.S_AutomorphicForm_exists_isSlabProfile_eLpNorm_sub_pseudoEisenstein_lt_of_forall_setIntegral_eq_zero_slab.AutomorphicForm P2MW.S_AutomorphicForm_exists_isSlabProfile_eLpNorm_sub_pseudoEisenstein_lt_of_forall_setIntegral_eq_zero_slab.AutomorphicForm.TwistedCentralAverage"

section

open MeasureTheory NumberField
open NumberField.AdelicHaar NumberField.AdelicLevel NumberField.AdelicBox
attribute [local instance] NumberField.AdelicHaar.glBorel
p2m_open "MeasureTheory Filter Topology AutomorphicForm P2MW.S_AutomorphicForm_exists_isSlabProfile_eLpNorm_sub_pseudoEisenstein_lt_of_forall_setIntegral_eq_zero_slab.AutomorphicForm"
open AutomorphicForm.PseudoEisensteinDensity

attribute [local instance] NumberField.AdelicHaar.adeleBorel

noncomputable section

set_option autoImplicit false

private theorem exists_isSlabProfile_eLpNorm_sub_pseudoEisenstein_lt_of_forall_setIntegral_mul_conj_cuspidal_eq_zero
    (F : Type) [Field F] [NumberField F]
    (d₁ d₂ : ℝ) (_hd₁ : 0 < d₁) (_hd : d₁ < d₂)
    (Φ : Set (AdelicGL2 (𝓞 F) F))
    (_hΦs : Φ ⊆ {g | NumberField.TateGlobal.ideleNorm F (Matrix.GeneralLinearGroup.det g) ∈ Set.Icc d₁ d₂})
    (_hΦ : IsFundamentalDomain (globalPoints (𝓞 F) F).range Φ
      ((adelicGLHaar (Fin 2) (𝓞 F) F).restrict {g | NumberField.TateGlobal.ideleNorm F
          (Matrix.GeneralLinearGroup.det g) ∈ Set.Icc d₁ d₂}))
    (ξ : (productionPinsOf F Φ (fun N => levelOne (𝓞 F) F N) (fun v => heckeGen (𝓞 F) F v) (adelicBox F)).Z →* ℂˣ)
    (hξ : Continuous ξ)
    (fe : AdelicGL2 (𝓞 F) F → ℂ)
    (_hfe : IsAutomorphicFnAt F
      (productionPinsOf F Φ (fun N => levelOne (𝓞 F) F N) (fun v => heckeGen (𝓞 F) F v) (adelicBox F)) ξ fe)
    (_hperp :
      letI := (productionPinsOf F Φ (fun N => levelOne (𝓞 F) F N) (fun v => heckeGen (𝓞 F) F v) (adelicBox F)).mS
      letI := (productionPinsOf F Φ (fun N => levelOne (𝓞 F) F N) (fun v => heckeGen (𝓞 F) F v) (adelicBox F)).nS
      ∀ u : AdelicGL2 (𝓞 F) F → ℂ,
        IsAutomorphicFnAt F (productionPinsOf F Φ (fun N => levelOne (𝓞 F) F N) (fun v => heckeGen (𝓞 F) F v)
            (adelicBox F)) ξ u →
        (∀ᵐ g ∂(productionPinsOf F Φ (fun N => levelOne (𝓞 F) F N) (fun v => heckeGen (𝓞 F) F v) (adelicBox F)).μ,
            constantTerm (productionPinsOf F Φ (fun N => levelOne (𝓞 F) F N) (fun v => heckeGen (𝓞 F) F v)
                (adelicBox F)).ν unipotentGL2 u g = 0) →
        ∫ g in (productionPinsOf F Φ (fun N => levelOne (𝓞 F) F N) (fun v => heckeGen (𝓞 F) F v) (adelicBox F)).D,
            fe g * starRingEnd ℂ (u g)
          ∂(productionPinsOf F Φ (fun N => levelOne (𝓞 F) F N) (fun v => heckeGen (𝓞 F) F v) (adelicBox F)).μ = 0)
    (ε : ℝ) (_hε : 0 < ε) :
    letI := (productionPinsOf F Φ (fun N => levelOne (𝓞 F) F N) (fun v => heckeGen (𝓞 F) F v) (adelicBox F)).mS
    ∃ φ : AdelicGL2 (𝓞 F) F → ℂ, AutomorphicForm.IsSlabProfile F
        (productionPinsOf F Φ (fun N => levelOne (𝓞 F) F N) (fun v => heckeGen (𝓞 F) F v) (adelicBox F)).Z ξ φ ∧
      eLpNorm (fe - AutomorphicForm.pseudoEisenstein F φ) 2 ((productionPinsOf F Φ (fun N => levelOne (𝓞 F) F N)
          (fun v => heckeGen (𝓞 F) F v) (adelicBox F)).μ.restrict (productionPinsOf F Φ (fun N => levelOne (𝓞 F)
          F N) (fun v => heckeGen (𝓞 F) F v) (adelicBox F)).D) < ENNReal.ofReal ε := by
  have hfin : ∀ φ : AdelicGL2 (𝓞 F) F → ℂ, IsSlabProfile F (pins F Φ).Z ξ φ → ∀ g : AdelicGL2 (𝓞 F) F,
      (Function.support (bruhatTerm F φ g)).Finite :=
    fun φ hφ g => AutomorphicForm.finite_support_pseudoEisenstein_summand F (pins F Φ).Z ξ φ hφ g
  have htheta : ∀ φ : AdelicGL2 (𝓞 F) F → ℂ, IsSlabProfile F (pins F Φ).Z ξ φ →
      IsAutomorphicFnAt F (pins F Φ) ξ (pseudoEisenstein F φ) :=
    fun φ hφ => AutomorphicForm.isAutomorphicFnAt_pseudoEisenstein_slab F d₁ d₂ _hd₁ _hd Φ _hΦs _hΦ ξ φ hφ
  have hcomplete : ∀ (useq : ℕ → AdelicGL2 (𝓞 F) F → ℂ) (v : AdelicGL2 (𝓞 F) F → ℂ),
      (∀ n, IsAutomorphicFnAt F (pins F Φ) ξ (useq n)) →
      MemLp v 2 ((adelicGLHaar (Fin 2) (𝓞 F) F).restrict Φ) →
      Tendsto (fun n => eLpNorm (useq n - v) 2 ((adelicGLHaar (Fin 2) (𝓞 F) F).restrict Φ)) atTop (𝓝 0) →
      ∃ U, IsAutomorphicFnAt F (pins F Φ) ξ U ∧ U =ᵐ[(adelicGLHaar (Fin 2) (𝓞 F) F).restrict Φ] v :=
    fun useq v hu hv hconv => exists_isAutomorphicFnAt_of_tendsto_eLpNorm F (pins F Φ) ξ useq hu v hv hconv
  have hcusp : ∀ u : AdelicGL2 (𝓞 F) F → ℂ, IsAutomorphicFnAt F (pins F Φ) ξ u →
      (∀ φ : AdelicGL2 (𝓞 F) F → ℂ, IsSlabProfile F (pins F Φ).Z ξ φ →
        ∫ g in Φ, pseudoEisenstein F φ g * (starRingEnd ℂ) (u g) ∂(adelicGLHaar (Fin 2) (𝓞 F) F) = 0) →
      ∀ᵐ g ∂(adelicGLHaar (Fin 2) (𝓞 F) F), constantTerm (pins F Φ).ν unipotentGL2 u g = 0 :=
    fun u hu horth => ae_constantTerm_eq_zero_of_forall_setIntegral_pseudoEisenstein_mul_conj_eq_zero F d₁ d₂
      _hd₁ _hd Φ _hΦs _hΦ ξ hξ u hu horth
  have hperp : ∀ u : AdelicGL2 (𝓞 F) F → ℂ, IsAutomorphicFnAt F (pins F Φ) ξ u →
      (∀ᵐ g ∂(adelicGLHaar (Fin 2) (𝓞 F) F), constantTerm (pins F Φ).ν unipotentGL2 u g = 0) →
      ∫ g in Φ, fe g * (starRingEnd ℂ) (u g) ∂(adelicGLHaar (Fin 2) (𝓞 F) F) = 0 :=
    fun u hu hc => _hperp u hu hc
  exact exists_isSlabProfile_eLpNorm_sub_pseudoEisenstein_lt F Φ ξ hfin hcomplete htheta hcusp fe _hfe hperp ε _hε

end
p2m_reactivate "P2MW.S_AutomorphicForm_exists_isSlabProfile_eLpNorm_sub_pseudoEisenstein_lt_of_forall_setIntegral_eq_zero_slab.SlabPairingDescent P2MW.S_AutomorphicForm_exists_isSlabProfile_eLpNorm_sub_pseudoEisenstein_lt_of_forall_setIntegral_eq_zero_slab.AutomorphicForm P2MW.S_AutomorphicForm_exists_isSlabProfile_eLpNorm_sub_pseudoEisenstein_lt_of_forall_setIntegral_eq_zero_slab.AutomorphicForm.TwistedCentralAverage"

end
p2m_reactivate "P2MW.S_AutomorphicForm_exists_isSlabProfile_eLpNorm_sub_pseudoEisenstein_lt_of_forall_setIntegral_eq_zero_slab.SlabPairingDescent P2MW.S_AutomorphicForm_exists_isSlabProfile_eLpNorm_sub_pseudoEisenstein_lt_of_forall_setIntegral_eq_zero_slab.AutomorphicForm P2MW.S_AutomorphicForm_exists_isSlabProfile_eLpNorm_sub_pseudoEisenstein_lt_of_forall_setIntegral_eq_zero_slab.AutomorphicForm.TwistedCentralAverage"
set_option autoImplicit false

open MeasureTheory NumberField
open NumberField.AdelicHaar NumberField.AdelicLevel NumberField.AdelicBox

attribute [local instance] NumberField.AdelicHaar.glBorel

noncomputable section

p2m_open "AutomorphicForm P2MW.S_AutomorphicForm_exists_isSlabProfile_eLpNorm_sub_pseudoEisenstein_lt_of_forall_setIntegral_eq_zero_slab.AutomorphicForm"

theorem solution
    (F : Type) [Field F] [NumberField F]
    (d₁ d₂ : ℝ) (_hd₁ : 0 < d₁) (_hd : d₁ < d₂)
    (Φ : Set (AdelicGL2 (𝓞 F) F))
    (_hΦs : Φ ⊆ {g | NumberField.TateGlobal.ideleNorm F (Matrix.GeneralLinearGroup.det g) ∈ Set.Icc d₁ d₂})
    (_hΦ : IsFundamentalDomain (globalPoints (𝓞 F) F).range Φ
      ((adelicGLHaar (Fin 2) (𝓞 F) F).restrict {g | NumberField.TateGlobal.ideleNorm F
          (Matrix.GeneralLinearGroup.det g) ∈ Set.Icc d₁ d₂}))
    (ξ : (productionPinsOf F Φ (fun N => levelOne (𝓞 F) F N) (fun v => heckeGen (𝓞 F) F v) (adelicBox F)).Z →* ℂˣ)
    (hξ : Continuous ξ)
    (fe : AdelicGL2 (𝓞 F) F → ℂ)
    (_hfe : IsAutomorphicFnAt F
      (productionPinsOf F Φ (fun N => levelOne (𝓞 F) F N) (fun v => heckeGen (𝓞 F) F v) (adelicBox F)) ξ fe)
    (_hperp :
      letI := (productionPinsOf F Φ (fun N => levelOne (𝓞 F) F N) (fun v => heckeGen (𝓞 F) F v) (adelicBox F)).mS
      letI := (productionPinsOf F Φ (fun N => levelOne (𝓞 F) F N) (fun v => heckeGen (𝓞 F) F v) (adelicBox F)).nS
      ∀ u : AdelicGL2 (𝓞 F) F → ℂ,
        IsAutomorphicFnAt F (productionPinsOf F Φ (fun N => levelOne (𝓞 F) F N) (fun v => heckeGen (𝓞 F) F v)
            (adelicBox F)) ξ u →
        (∀ᵐ g ∂(productionPinsOf F Φ (fun N => levelOne (𝓞 F) F N) (fun v => heckeGen (𝓞 F) F v) (adelicBox F)).μ,
            constantTerm (productionPinsOf F Φ (fun N => levelOne (𝓞 F) F N) (fun v => heckeGen (𝓞 F) F v)
                (adelicBox F)).ν unipotentGL2 u g = 0) →
        ∫ g in (productionPinsOf F Φ (fun N => levelOne (𝓞 F) F N) (fun v => heckeGen (𝓞 F) F v) (adelicBox F)).D,
            fe g * starRingEnd ℂ (u g)
          ∂(productionPinsOf F Φ (fun N => levelOne (𝓞 F) F N) (fun v => heckeGen (𝓞 F) F v) (adelicBox F)).μ = 0)
    (ε : ℝ) (_hε : 0 < ε) :
    letI := (productionPinsOf F Φ (fun N => levelOne (𝓞 F) F N) (fun v => heckeGen (𝓞 F) F v) (adelicBox F)).mS
    ∃ φ : AdelicGL2 (𝓞 F) F → ℂ, AutomorphicForm.IsSlabProfile F
        (productionPinsOf F Φ (fun N => levelOne (𝓞 F) F N) (fun v => heckeGen (𝓞 F) F v) (adelicBox F)).Z ξ φ ∧
      eLpNorm (fe - AutomorphicForm.pseudoEisenstein F φ) 2 ((productionPinsOf F Φ (fun N => levelOne (𝓞 F) F N)
          (fun v => heckeGen (𝓞 F) F v) (adelicBox F)).μ.restrict (productionPinsOf F Φ (fun N => levelOne (𝓞 F)
          F N) (fun v => heckeGen (𝓞 F) F v) (adelicBox F)).D) < ENNReal.ofReal ε := by
  exact exists_isSlabProfile_eLpNorm_sub_pseudoEisenstein_lt_of_forall_setIntegral_mul_conj_cuspidal_eq_zero F
    d₁ d₂ _hd₁ _hd Φ _hΦs _hΦ ξ hξ fe _hfe _hperp ε _hε

end
p2m_reactivate "P2MW.S_AutomorphicForm_exists_isSlabProfile_eLpNorm_sub_pseudoEisenstein_lt_of_forall_setIntegral_eq_zero_slab.SlabPairingDescent P2MW.S_AutomorphicForm_exists_isSlabProfile_eLpNorm_sub_pseudoEisenstein_lt_of_forall_setIntegral_eq_zero_slab.AutomorphicForm P2MW.S_AutomorphicForm_exists_isSlabProfile_eLpNorm_sub_pseudoEisenstein_lt_of_forall_setIntegral_eq_zero_slab.AutomorphicForm.TwistedCentralAverage"

end S_AutomorphicForm_exists_isSlabProfile_eLpNorm_sub_pseudoEisenstein_lt_of_forall_setIntegral_eq_zero_slab
end P2MW
export P2MW.S_AutomorphicForm_exists_isSlabProfile_eLpNorm_sub_pseudoEisenstein_lt_of_forall_setIntegral_eq_zero_slab (solution)
