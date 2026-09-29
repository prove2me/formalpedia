-- Prove2me | solution 1 for AutomorphicForm.setIntegral_rightConv_mul_conj_eq_setIntegral_mul_conj_rightConv_flat_of_isLsXiFunction_of_isFundamentalDomain_slab
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:05.340288+00:00
-- url     : https://prove2.me/submissions/85d430aa-f4d5-509c-b118-54c1cb631713

import Theorems.Thm_NumberField_AdelicHaar_isMulRightInvariant_adelicGLHaar
import Theorems.Thm_NumberField_AdeleRing_secondCountableTopology_generalLinearGroup_finTwo
import Theorems.Thm_NumberField_TateGlobal_exists_ideleNorm_eq_and_snd_eq_one
import Theorems.Thm_NumberField_TateGlobal_measurableSet_setOf_ideleNorm_det_mem_Icc
import Theorems.Thm_AutomorphicForm_ideleNorm_det_globalPoints
import Theorems.Thm_NumberField_TateGlobal_continuous_ideleNorm_det
import Definitions.Def_AutomorphicForm_RightConvolution
import Definitions.Def_AutomorphicForm_AdelicLsXi
import Definitions.Def_NumberField_TateGlobalZeta
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Group.FundamentalDomain
import Mathlib.MeasureTheory.Group.Integral
import Mathlib.MeasureTheory.Measure.Haar.Unique
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AutomorphicForm_setIntegral_rightConv_mul_conj_eq_setIntegral_mul_conj_rightConv_flat_of_isLsXiFunction_of_isFundamentalDomain_slab
p2m_attr_erase "instance" "instCountableOfNumberField_definitions RestrictedProduct.SecondCountableTopology_of_principal instCountableElemSetSetsCofinite_definitions FLT.SmoothVectors.RightTranslationFn.instAddCommMonoid FLT.SmoothVectors.RightTranslationFn.instMulAction FLT.SmoothVectors.RightTranslationFn.instDistribMulAction instContinuousSMulOfDiscreteTopologyOfContinuousSMulDiscrete HeckePair.instSMulCommClassSubtypeForallMemSubmoduleHeckeAlgebra HeckePair.instAlgebraSubtypeForallMemSubmoduleHeckeAlgebra HeckePair.instOneSubtypeForallMemSubmoduleHeckeAlgebra HeckePair.instIsScalarTowerSubtypeForallMemSubmoduleHeckeAlgebra HeckePair.instRingSubtypeForallMemSubmoduleHeckeAlgebra HeckePair.instMulSubtypeForallMemSubmoduleHeckeAlgebra FixedPoints.instMulActionElemFixedPointsOfSMulCommClass_definitions FixedPoints.module FixedPoints.instSMulElemFixedPointsOfSMulCommClass_definitions FixedPoints.instAddCommMonoidElemFixedPoints_definitions instFiniteResidueFieldAdicCompletionRingOfIntegersWithZeroMultiplicativeInt_definitions NumberField.instCompactSpaceAdicCompletionIntegers Rat.adicCompletion.locallyCompactSpace NumberField.instFiniteResidueFieldAdicCompletionIntegers instWeaklyLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions"
p2m_attr_erase "simp" "ContinuousAddEquiv.restrictedProductPi_apply RestrictedProduct.flatten_homeomorph_apply RestrictedProduct.flatten_homeomorph'_symm_apply ContinuousMulEquiv.restrictedProductPi_symm_apply RestrictedProduct.flatten_homeomorph'_apply RestrictedProduct.flatten_homeomorph_symm_apply ContinuousMulEquiv.restrictedProductPi_apply ContinuousAddEquiv.restrictedProductPi_symm_apply RingEquiv.restrictedProductCongr_symm_apply RingEquiv.restrictedProductCongrRight_apply MulEquiv.restrictedProductCongrRight_apply Equiv.restrictedProductProd_symm_apply_coe Equiv.restrictedProductCongrRight_apply AddEquiv.restrictedProductCongr_apply Equiv.restrictedProductCongrLeft'_symm_apply_apply Equiv.restrictedProductCongr_apply_apply Equiv.restrictedProductCongrLeft_apply_apply RestrictedProduct.flatten_equiv'_apply AddEquiv.restrictedProductCongrRight_apply Equiv.restrictedProductCongr_symm_apply Equiv.restrictedProductCongrRight_symm_apply RestrictedProduct.flatten_equiv'_symm_apply AddEquiv.restrictedProductCongrLeft'_apply Equiv.restrictedProductCongrLeft'_apply RestrictedProduct.flatten_apply RingEquiv.restrictedProductCongr_apply_apply RingEquiv.restrictedProductCongrLeft'_apply Equiv.restrictedProductProd_apply RestrictedProduct.flatten_equiv_apply RestrictedProduct.flatten_equiv_symm_apply LinearEquiv.restrictedProductCongrLeft'_apply RestrictedProduct.not_mem_support RestrictedProduct.mem_structureSubring_iff RestrictedProduct.not_mem_mulSupport RestrictedProduct.support_neg RestrictedProduct.mem_indexSupport_iff RestrictedProduct.mulSupport_inv RestrictedProduct.mapAlongLinearMap_apply AutomorphicForm.classSq_apply AutomorphicForm.classRepEmbedding_one"
p2m_attr_erase "simp" "AutomorphicForm.finIdeleExponentAt_one AutomorphicForm.classRepFinIdele_one AutomorphicForm.productionPinsGeneralOf_D AutomorphicForm.productionPinsGeneral_D AutomorphicForm.productionPinsGeneralOf_μ AutomorphicForm.productionPinsGeneralOf_U AutomorphicForm.productionPinsCompact_ν AutomorphicForm.productionPinsCompact_U AutomorphicForm.productionPinsCompact_D AutomorphicForm.productionPinsCompact_nS AutomorphicForm.productionPinsCompact_gen AutomorphicForm.productionPinsCompact_Z AutomorphicForm.productionPinsCompact_mS AutomorphicForm.productionPinsCompact_μ AutomorphicForm.productionPins_nS AutomorphicForm.productionPins_mS AutomorphicForm.productionPins_ν AutomorphicForm.productionPins_Z AutomorphicForm.productionPins_U AutomorphicForm.productionPins_μ AutomorphicForm.productionPins_gen AutomorphicForm.productionPins_D AutomorphicForm.SiegelCoordinates.upperUnit_apply_zero_zero AutomorphicForm.SiegelCoordinates.upperUnit_apply_one_zero AutomorphicForm.SiegelCoordinates.upperUnit_apply_one_one AutomorphicForm.SiegelCoordinates.upperUnit_apply_zero_one AutomorphicForm.unipotentGL2_zero AutomorphicForm.constantTerm_const AutomorphicForm.constantTerm_zero AutomorphicForm.unipotentGL2_coe FLT.SmoothVectors.RightTranslationFn.toFun_smul FLT.SmoothVectors.RightTranslationFn.mk_toFun FLT.SmoothVectors.RightTranslationFn.toFun_mk FLT.SmoothVectors.mem_smoothVectors_iff AutomorphicForm.HeckeEigensystem.ofRawCentral_toRawCentral AutomorphicForm.HeckeEigensystem.toRawCentral_ofRawCentral AutomorphicForm.HeckeEigensystem.ofRawCentral_a AutomorphicForm.HeckeEigensystem.ofRawCentral_b AutomorphicForm.HeckeEigensystem.toRawCentral_level AutomorphicForm.HeckeEigensystem.toRawCentral_a"
p2m_attr_erase "simp" "AutomorphicForm.HeckeEigensystem.ofRawCentral_level AutomorphicForm.HeckeEigensystem.toRawCentral_b AutomorphicForm.SmoothCuspRealizationAt.mk.injEq AutomorphicForm.degenerateEigensystem_a AutomorphicForm.SmoothCuspRealizationAt.mk.sizeOf_spec AutomorphicForm.degenerateEigensystem_b AutomorphicForm.HeckeEigensystem.map_b AutomorphicForm.HeckeEigensystem.map_a AutomorphicForm.HeckeEigensystem.map_level AutomorphicForm.CuspidalityNotion.mk.injEq AutomorphicForm.HeckeEigensystem.twist_b AutomorphicForm.satakePow_zero AutomorphicForm.HeckeEigensystem.twist_a AutomorphicForm.HeckeEigensystem.mk.injEq AutomorphicForm.HeckeEigensystem.mk.sizeOf_spec AutomorphicForm.DescentPackage.mk.injEq AutomorphicForm.DescentPackage.mk.sizeOf_spec AutomorphicForm.CuspidalityNotion.mk.sizeOf_spec AutomorphicForm.satakePow_one HeckePair.convTerm_mk HeckePair.coe_apply_add HeckePair.coe_apply_smul FixedPoints.coe_zero FixedPoints.coe_smul FixedPoints.coe_add"

set_option autoImplicit false

noncomputable section

namespace R4UwAdj

open MeasureTheory NumberField NumberField.AdelicHaar NumberField.TateGlobal
open scoped ComplexConjugate ENNReal Pointwise
open MeasureTheory.Measure
open AutomorphicForm

attribute [local instance] NumberField.AdelicHaar.glBorel

variable (K : Type) [Field K] [NumberField K]

abbrev μ : Measure (AdelicGL2 (𝓞 K) K) := adelicGLHaar (Fin 2) (𝓞 K) K

abbrev Γ : Subgroup (AdelicGL2 (𝓞 K) K) := (globalPoints (𝓞 K) K).range

def slab (a b : ℝ) : Set (AdelicGL2 (𝓞 K) K) :=
  {g | ideleNorm K (Matrix.GeneralLinearGroup.det g) ∈ Set.Icc a b}

variable {K}

scoped instance instBorelGL : BorelSpace (AdelicGL2 (𝓞 K) K) := borelSpace_glBorel (Fin 2) (𝓞 K) K

scoped instance instHaarμ : (μ K).IsHaarMeasure := isHaarMeasure_adelicGLHaar (Fin 2) (𝓞 K) K

scoped instance instRightInv : (μ K).IsMulRightInvariant := isMulRightInvariant_adelicGLHaar K

scoped instance instSecondCountableGL : SecondCountableTopology (AdelicGL2 (𝓞 K) K) :=
  NumberField.AdeleRing.secondCountableTopology_generalLinearGroup_finTwo K

scoped instance instRegular : (μ K).Regular := by
  show (adelicGLHaar (Fin 2) (𝓞 K) K).Regular
  unfold adelicGLHaar
  exact regular_haarMeasure

scoped instance instInvInvariant : (μ K).IsInvInvariant := by
  constructor
  let c : ℝ≥0∞ := haarScalarFactor (μ K).inv (μ K)
  have hc : (μ K).inv = c • μ K := isMulLeftInvariant_eq_smul_of_regular (μ K).inv (μ K)
  have h1 : map Inv.inv (map Inv.inv (μ K)) = c ^ 2 • μ K := by
    rw [← inv_def (μ K), hc, Measure.map_smul, ← inv_def (μ K), hc, smul_smul, pow_two]
  have μeq : μ K = c ^ 2 • μ K := by
    rw [map_map continuous_inv.measurable continuous_inv.measurable] at h1
    simpa only [inv_involutive, Function.Involutive.comp_self, Measure.map_id] using h1
  have K₀ : TopologicalSpace.PositiveCompacts (AdelicGL2 (𝓞 K) K) := Classical.arbitrary _
  have h2 : c ^ 2 * μ K K₀ = 1 ^ 2 * μ K K₀ := by
    conv_rhs => rw [μeq]
    simp
  have h3 : c ^ 2 = 1 ^ 2 :=
    (ENNReal.mul_left_inj (measure_pos_of_nonempty_interior _ K₀.interior_nonempty).ne'
      K₀.isCompact.measure_lt_top.ne).1 h2
  have h4 : c = 1 := (ENNReal.pow_right_strictMono two_ne_zero).injective h3
  rw [hc, h4, one_smul]

theorem normDet_mul (x z : AdelicGL2 (𝓞 K) K) :
    ideleNorm K (Matrix.GeneralLinearGroup.det (x * z)) =
      ideleNorm K (Matrix.GeneralLinearGroup.det x) * ideleNorm K (Matrix.GeneralLinearGroup.det z) := by
  rw [map_mul, ideleNorm_mul]

theorem normDet_one : ideleNorm K (Matrix.GeneralLinearGroup.det (1 : AdelicGL2 (𝓞 K) K)) = 1 := by
  rw [map_one]
  simp [ideleNorm]

theorem normDet_inv (x : AdelicGL2 (𝓞 K) K) :
    ideleNorm K (Matrix.GeneralLinearGroup.det x⁻¹) = (ideleNorm K (Matrix.GeneralLinearGroup.det x))⁻¹ := by
  have h := normDet_mul x⁻¹ x
  rw [inv_mul_cancel, normDet_one] at h
  exact eq_inv_of_mul_eq_one_left h.symm

theorem det_centralScalar (a : (AdeleRing (𝓞 K) K)ˣ) :
    Matrix.GeneralLinearGroup.det (centralScalar (𝓞 K) K a) = a ^ 2 := by
  rw [show centralScalar (𝓞 K) K = Matrix.GeneralLinearGroup.scalar (Fin 2) from rfl,
    Matrix.GeneralLinearGroup.det_scalar, Fintype.card_fin]

theorem normDet_central (a : (AdeleRing (𝓞 K) K)ˣ) :
    ideleNorm K (Matrix.GeneralLinearGroup.det (centralScalar (𝓞 K) K a)) = ideleNorm K a ^ 2 := by
  rw [det_centralScalar, pow_two, ideleNorm_mul, pow_two]

theorem normDet_global (γ : Matrix.GeneralLinearGroup (Fin 2) K) (x : AdelicGL2 (𝓞 K) K) :
    ideleNorm K (Matrix.GeneralLinearGroup.det (globalPoints (𝓞 K) K γ * x)) =
      ideleNorm K (Matrix.GeneralLinearGroup.det x) := by
  rw [normDet_mul, ideleNorm_det_globalPoints, one_mul]

theorem central_comm (a : (AdeleRing (𝓞 K) K)ˣ) (X : AdelicGL2 (𝓞 K) K) :
    X * centralScalar (𝓞 K) K a = centralScalar (𝓞 K) K a * X := by
  refine Units.ext ?_
  show (X : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 K) K)) * Matrix.scalar (Fin 2) (a : AdeleRing (𝓞 K) K)
    = Matrix.scalar (Fin 2) (a : AdeleRing (𝓞 K) K) * (X : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 K) K))
  exact ((Matrix.scalar_commute _ (fun r' => Commute.all _ r') _).eq).symm

theorem exists_central_normDet_eq (t : ℝ) (ht : 0 < t) :
    ∃ a : (AdeleRing (𝓞 K) K)ˣ, ideleNorm K (Matrix.GeneralLinearGroup.det (centralScalar (𝓞 K) K a)) = t := by
  obtain ⟨a, -, ha⟩ := exists_ideleNorm_eq_and_snd_eq_one K (Real.sqrt t) (Real.sqrt_pos.2 ht)
  exact ⟨a, by rw [normDet_central, ha, Real.sq_sqrt ht.le]⟩

theorem slab_measurable (a b : ℝ) : MeasurableSet (slab K a b) :=
  measurableSet_setOf_ideleNorm_det_mem_Icc K a b

theorem Γ_smul (γ : Γ K) (x : AdelicGL2 (𝓞 K) K) : γ • x = (γ : AdelicGL2 (𝓞 K) K) * x := rfl

theorem Γ_smul_eq (γ : Γ K) :
    ∃ γ₀ : Matrix.GeneralLinearGroup (Fin 2) K, (γ : AdelicGL2 (𝓞 K) K) = globalPoints (𝓞 K) K γ₀ := by
  obtain ⟨γ₀, h⟩ := γ.2
  exact ⟨γ₀, h.symm⟩

theorem slab_Γ_stable (a b : ℝ) (γ : Γ K) (x : AdelicGL2 (𝓞 K) K) :
    γ • x ∈ slab K a b ↔ x ∈ slab K a b := by
  obtain ⟨γ₀, hγ₀⟩ := Γ_smul_eq γ
  show ideleNorm K (Matrix.GeneralLinearGroup.det (_ * x)) ∈ Set.Icc a b ↔ x ∈ slab K a b
  rw [hγ₀, normDet_global]
  exact Iff.rfl

scoped instance instMeasurableConstSMulΓ : MeasurableConstSMul (Γ K) (AdelicGL2 (𝓞 K) K) :=
  ⟨fun γ => measurable_const_mul (γ : AdelicGL2 (𝓞 K) K)⟩

theorem smulInvariant_restrict (S : Set (AdelicGL2 (𝓞 K) K))
    (hS : ∀ (γ : Γ K) (x : AdelicGL2 (𝓞 K) K), γ • x ∈ S ↔ x ∈ S) :
    SMulInvariantMeasure (Γ K) (AdelicGL2 (𝓞 K) K) ((μ K).restrict S) := by
  refine ⟨fun γ s hs => ?_⟩
  have hmeas : MeasurableSet ((fun x => γ • x) ⁻¹' s) := (measurable_const_mul (γ : AdelicGL2 (𝓞 K) K)) hs
  rw [Measure.restrict_apply hmeas, Measure.restrict_apply hs]
  have hset : (fun x => γ • x) ⁻¹' s ∩ S = (fun x => (γ : AdelicGL2 (𝓞 K) K) * x) ⁻¹' (s ∩ S) := by
    ext x
    simp only [Set.mem_inter_iff, Set.mem_preimage]
    rw [← Γ_smul γ x, hS γ x]
  rw [hset, measure_preimage_mul]

theorem countable_Γ : Countable (Γ K) := by
  haveI : Countable K := (Module.finBasis ℚ K).equivFun.injective.countable
  haveI : Countable (Matrix (Fin 2) (Fin 2) K) := inferInstanceAs (Countable (Fin 2 → Fin 2 → K))
  haveI : Countable (Matrix.GeneralLinearGroup (Fin 2) K) :=
    Function.Injective.countable fun _ _ h => Units.ext h
  have h : ((Γ K : Subgroup (AdelicGL2 (𝓞 K) K)) : Set (AdelicGL2 (𝓞 K) K)).Countable := by
    rw [MonoidHom.coe_range]
    exact Set.countable_range _
  exact h.to_subtype

theorem preimage_mulRight_slab (a b : ℝ) (z : AdelicGL2 (𝓞 K) K) :
    (fun x => x * z) ⁻¹' slab K (a * ideleNorm K (Matrix.GeneralLinearGroup.det z))
        (b * ideleNorm K (Matrix.GeneralLinearGroup.det z)) = slab K a b := by
  ext x
  have ht : 0 < ideleNorm K (Matrix.GeneralLinearGroup.det z) := ideleNorm_pos _
  simp only [slab, Set.mem_preimage, Set.mem_setOf_eq, Set.mem_Icc, normDet_mul]
  constructor
  · rintro ⟨h1, h2⟩
    exact ⟨le_of_mul_le_mul_right h1 ht, le_of_mul_le_mul_right h2 ht⟩
  · rintro ⟨h1, h2⟩
    exact ⟨mul_le_mul_of_nonneg_right h1 ht.le, mul_le_mul_of_nonneg_right h2 ht.le⟩

theorem measurePreserving_mulRight_slab (a b : ℝ) (z : AdelicGL2 (𝓞 K) K) :
    MeasurePreserving (fun x => x * z) ((μ K).restrict (slab K a b))
      ((μ K).restrict (slab K (a * ideleNorm K (Matrix.GeneralLinearGroup.det z))
        (b * ideleNorm K (Matrix.GeneralLinearGroup.det z)))) := by
  have h := (measurePreserving_mul_right (μ K) z).restrict_preimage
    (slab_measurable (K := K) (a * ideleNorm K (Matrix.GeneralLinearGroup.det z))
      (b * ideleNorm K (Matrix.GeneralLinearGroup.det z)))
  rwa [preimage_mulRight_slab] at h

theorem isFundamentalDomain_image_mulRight (a b : ℝ) {Φ₀ : Set (AdelicGL2 (𝓞 K) K)}
    (hFD : IsFundamentalDomain (Γ K) Φ₀ ((μ K).restrict (slab K a b))) (z : AdelicGL2 (𝓞 K) K) :
    IsFundamentalDomain (Γ K) ((fun x => x * z) '' Φ₀)
      ((μ K).restrict (slab K (a * ideleNorm K (Matrix.GeneralLinearGroup.det z))
        (b * ideleNorm K (Matrix.GeneralLinearGroup.det z)))) := by
  let e : AdelicGL2 (𝓞 K) K ≃ᵐ AdelicGL2 (𝓞 K) K := MeasurableEquiv.mulRight z
  have hmp := measurePreserving_mulRight_slab (K := K) a b z
  have hmp' : MeasurePreserving e ((μ K).restrict (slab K a b))
      ((μ K).restrict (slab K (a * ideleNorm K (Matrix.GeneralLinearGroup.det z))
        (b * ideleNorm K (Matrix.GeneralLinearGroup.det z)))) := hmp
  have himg : (fun x => x * z) '' Φ₀ = e.toEquiv '' Φ₀ := rfl
  rw [himg]
  refine hFD.image_of_equiv e.toEquiv ?_ (Equiv.refl _) fun γ x => ?_
  · exact (hmp'.symm e).quasiMeasurePreserving
  · show (γ • x) * z = γ • (x * z)
    rw [Γ_smul, Γ_smul, mul_assoc]

theorem setLIntegral_comp_mulRight_eq (a b : ℝ) {Φ₀ : Set (AdelicGL2 (𝓞 K) K)} (hΦ₀ : Φ₀ ⊆ slab K a b)
    (hFD : IsFundamentalDomain (Γ K) Φ₀ ((μ K).restrict (slab K a b)))
    (F : AdelicGL2 (𝓞 K) K → ℝ≥0∞) (hF : ∀ (γ : Γ K) (x : AdelicGL2 (𝓞 K) K), F (γ • x) = F x)
    (z c : AdelicGL2 (𝓞 K) K)
    (hzc : ideleNorm K (Matrix.GeneralLinearGroup.det c) = ideleNorm K (Matrix.GeneralLinearGroup.det z)) :
    ∫⁻ x in Φ₀, F (x * z) ∂(μ K) = ∫⁻ x in Φ₀, F (x * c) ∂(μ K) := by
  haveI := countable_Γ (K := K)
  set t := ideleNorm K (Matrix.GeneralLinearGroup.det z) with ht
  haveI : SMulInvariantMeasure (Γ K) (AdelicGL2 (𝓞 K) K) ((μ K).restrict (slab K (a * t) (b * t))) :=
    smulInvariant_restrict _ (slab_Γ_stable (a * t) (b * t))
  have hz := isFundamentalDomain_image_mulRight a b hFD z
  have hc := isFundamentalDomain_image_mulRight a b hFD c
  rw [hzc] at hc

  have hsub : ∀ y : AdelicGL2 (𝓞 K) K, ideleNorm K (Matrix.GeneralLinearGroup.det y) = t →
      (fun x => x * y) '' Φ₀ ⊆ slab K (a * t) (b * t) := by
    rintro y hy _ ⟨x, hx, rfl⟩
    have h := hΦ₀ hx
    simp only [slab, Set.mem_setOf_eq, Set.mem_Icc, normDet_mul, hy] at h ⊢
    have ht0 : 0 < t := by rw [ht]; exact ideleNorm_pos _
    exact ⟨mul_le_mul_of_nonneg_right h.1 ht0.le, mul_le_mul_of_nonneg_right h.2 ht0.le⟩
  have hFD_eq := hz.setLIntegral_eq hc F hF

  have hrestr : ∀ y : AdelicGL2 (𝓞 K) K, ideleNorm K (Matrix.GeneralLinearGroup.det y) = t →
      ∫⁻ x in (fun x => x * y) '' Φ₀, F x ∂((μ K).restrict (slab K (a * t) (b * t))) =
        ∫⁻ x in (fun x => x * y) '' Φ₀, F x ∂(μ K) := by
    intro y hy
    rw [Measure.restrict_restrict' (slab_measurable (a * t) (b * t)),
      Set.inter_eq_left.2 (hsub y hy)]
  rw [hrestr z rfl, hrestr c hzc] at hFD_eq

  have hcv : ∀ y : AdelicGL2 (𝓞 K) K, ∫⁻ x in Φ₀, F (x * y) ∂(μ K) = ∫⁻ x in (fun x => x * y) '' Φ₀, F x ∂(μ K) :=
    fun y => (measurePreserving_mul_right (μ K) y).setLIntegral_comp_emb
      (MeasurableEquiv.mulRight y).measurableEmbedding F Φ₀
  rw [hcv z, hcv c, hFD_eq]

theorem setIntegral_comp_mulRight_eq (a b : ℝ) {Φ₀ : Set (AdelicGL2 (𝓞 K) K)} (hΦ₀ : Φ₀ ⊆ slab K a b)
    (hFD : IsFundamentalDomain (Γ K) Φ₀ ((μ K).restrict (slab K a b)))
    (F : AdelicGL2 (𝓞 K) K → ℂ) (hF : ∀ (γ : Γ K) (x : AdelicGL2 (𝓞 K) K), F (γ • x) = F x)
    (z c : AdelicGL2 (𝓞 K) K)
    (hzc : ideleNorm K (Matrix.GeneralLinearGroup.det c) = ideleNorm K (Matrix.GeneralLinearGroup.det z)) :
    ∫ x in Φ₀, F (x * z) ∂(μ K) = ∫ x in Φ₀, F (x * c) ∂(μ K) := by
  haveI := countable_Γ (K := K)
  set t := ideleNorm K (Matrix.GeneralLinearGroup.det z) with ht
  haveI : SMulInvariantMeasure (Γ K) (AdelicGL2 (𝓞 K) K) ((μ K).restrict (slab K (a * t) (b * t))) :=
    smulInvariant_restrict _ (slab_Γ_stable (a * t) (b * t))
  have hz := isFundamentalDomain_image_mulRight a b hFD z
  have hc := isFundamentalDomain_image_mulRight a b hFD c
  rw [hzc] at hc
  have hsub : ∀ y : AdelicGL2 (𝓞 K) K, ideleNorm K (Matrix.GeneralLinearGroup.det y) = t →
      (fun x => x * y) '' Φ₀ ⊆ slab K (a * t) (b * t) := by
    rintro y hy _ ⟨x, hx, rfl⟩
    have h := hΦ₀ hx
    simp only [slab, Set.mem_setOf_eq, Set.mem_Icc, normDet_mul, hy] at h ⊢
    have ht0 : 0 < t := by rw [ht]; exact ideleNorm_pos _
    exact ⟨mul_le_mul_of_nonneg_right h.1 ht0.le, mul_le_mul_of_nonneg_right h.2 ht0.le⟩
  have hFD_eq := hz.setIntegral_eq hc (f := F) hF
  have hrestr : ∀ y : AdelicGL2 (𝓞 K) K, ideleNorm K (Matrix.GeneralLinearGroup.det y) = t →
      ∫ x in (fun x => x * y) '' Φ₀, F x ∂((μ K).restrict (slab K (a * t) (b * t))) =
        ∫ x in (fun x => x * y) '' Φ₀, F x ∂(μ K) := by
    intro y hy
    rw [Measure.restrict_restrict' (slab_measurable (a * t) (b * t)),
      Set.inter_eq_left.2 (hsub y hy)]
  rw [hrestr z rfl, hrestr c hzc] at hFD_eq
  have hcv : ∀ y : AdelicGL2 (𝓞 K) K, ∫ x in (fun x => x * y) '' Φ₀, F x ∂(μ K) = ∫ x in Φ₀, F (x * y) ∂(μ K) :=
    fun y => (measurePreserving_mul_right (μ K) y).setIntegral_image_emb
      (MeasurableEquiv.mulRight y).measurableEmbedding F Φ₀
  rw [← hcv z, ← hcv c, hFD_eq]

end R4UwAdj
p2m_reactivate "P2MW.S_AutomorphicForm_setIntegral_rightConv_mul_conj_eq_setIntegral_mul_conj_rightConv_flat_of_isLsXiFunction_of_isFundamentalDomain_slab.R4UwAdj"

end
p2m_reactivate "P2MW.S_AutomorphicForm_setIntegral_rightConv_mul_conj_eq_setIntegral_mul_conj_rightConv_flat_of_isLsXiFunction_of_isFundamentalDomain_slab.R4UwAdj"

open MeasureTheory NumberField NumberField.AdelicHaar NumberField.TateGlobal
open scoped ComplexConjugate ENNReal
open AutomorphicForm

attribute [local instance] NumberField.AdelicHaar.glBorel

theorem solution
    (K : Type) [Field K] [NumberField K] (α β : ℝ)
    (Φ₀ : Set (AutomorphicForm.AdelicGL2 (𝓞 K) K))
    (hΦ₀ : Φ₀ ⊆ {g | NumberField.TateGlobal.ideleNorm K (Matrix.GeneralLinearGroup.det g) ∈ Set.Icc α β})
    (hFD : IsFundamentalDomain (AutomorphicForm.globalPoints (𝓞 K) K).range Φ₀
      ((adelicGLHaar (Fin 2) (𝓞 K) K).restrict
        {g | NumberField.TateGlobal.ideleNorm K (Matrix.GeneralLinearGroup.det g) ∈ Set.Icc α β}))
    (ξ : (⊤ : Subgroup (AdeleRing (𝓞 K) K)ˣ) →* ℂˣ) (σ : ℝ)
    (hσ : ∀ z : (⊤ : Subgroup (AdeleRing (𝓞 K) K)ˣ),
      ‖((ξ z : ℂˣ) : ℂ)‖ = NumberField.TateGlobal.ideleNorm K (z : (AdeleRing (𝓞 K) K)ˣ) ^ σ)
    (u v : AutomorphicForm.AdelicGL2 (𝓞 K) K → ℂ)
    (hu : AutomorphicForm.IsLsXiFunction (𝓞 K) K ⊤ ξ u) (hv : AutomorphicForm.IsLsXiFunction (𝓞 K) K ⊤ ξ v)
    (huc : Continuous u) (hvc : Continuous v)
    (hu₂ : MemLp u 2 ((adelicGLHaar (Fin 2) (𝓞 K) K).restrict Φ₀))
    (hv₂ : MemLp v 2 ((adelicGLHaar (Fin 2) (𝓞 K) K).restrict Φ₀))
    (g : AutomorphicForm.AdelicGL2 (𝓞 K) K → ℂ) (hg : Continuous g) (hgc : HasCompactSupport g) :
    ∫ x in Φ₀, AutomorphicForm.rightConv K u g x * conj (v x) ∂(adelicGLHaar (Fin 2) (𝓞 K) K) =
      ∫ x in Φ₀, u x * conj (AutomorphicForm.rightConv K v (fun y => conj (g y⁻¹) *
          ((NumberField.TateGlobal.ideleNorm K (Matrix.GeneralLinearGroup.det y) ^ (-σ) : ℝ) : ℂ)) x)
        ∂(adelicGLHaar (Fin 2) (𝓞 K) K) := by

  set μ : Measure (AdelicGL2 (𝓞 K) K) := adelicGLHaar (Fin 2) (𝓞 K) K with hμ
  have hΦ₀' : Φ₀ ⊆ R4UwAdj.slab K α β := hΦ₀
  have hFD' : IsFundamentalDomain (R4UwAdj.Γ K) Φ₀ ((R4UwAdj.μ K).restrict (R4UwAdj.slab K α β)) := hFD
  let nd : AdelicGL2 (𝓞 K) K → ℝ := fun z => ideleNorm K (Matrix.GeneralLinearGroup.det z)
  have nd_pos : ∀ z, 0 < nd z := fun z => ideleNorm_pos _
  have nd_cont : Continuous nd := continuous_ideleNorm_det K
  let gf : AdelicGL2 (𝓞 K) K → ℂ := fun y => conj (g y⁻¹) * ((nd y ^ (-σ) : ℝ) : ℂ)
  have hgf_c : Continuous gf :=
    (Complex.continuous_conj.comp (hg.comp continuous_inv)).mul
      (Complex.continuous_ofReal.comp (nd_cont.rpow_const fun _ => Or.inl (nd_pos _).ne'))
  have hgf_s : HasCompactSupport gf := by
    have h1 : HasCompactSupport (fun y : AdelicGL2 (𝓞 K) K => g y⁻¹) :=
      hgc.comp_homeomorph (Homeomorph.inv (AdelicGL2 (𝓞 K) K))
    exact (h1.comp_left (map_zero (starRingEnd ℂ))).mul_right

  have lsxi_translate : ∀ {w : AdelicGL2 (𝓞 K) K → ℂ}, IsLsXiFunction (𝓞 K) K ⊤ ξ w →
      ∀ y : AdelicGL2 (𝓞 K) K, IsLsXiFunction (𝓞 K) K ⊤ ξ (fun x => w (x * y)) := fun hw y =>
    { left_invariant := fun γ x => by simp only [mul_assoc, hw.left_invariant]
      central_transform := fun z x => by simp only [mul_assoc, hw.central_transform] }

  have hmod : ∀ a : (AdeleRing (𝓞 K) K)ˣ,
      ‖((ξ ⟨a, Subgroup.mem_top a⟩ : ℂˣ) : ℂ)‖ ^ 2 =
        ideleNorm K (Matrix.GeneralLinearGroup.det (centralScalar (𝓞 K) K a)) ^ σ := by
    intro a
    rw [hσ ⟨a, Subgroup.mem_top a⟩, R4UwAdj.normDet_central]
    show (ideleNorm K a ^ σ) ^ 2 = (ideleNorm K a ^ 2) ^ σ
    rw [← Real.rpow_natCast (ideleNorm K a ^ σ) 2, ← Real.rpow_mul (ideleNorm_pos a).le,
      ← Real.rpow_natCast (ideleNorm K a) 2, ← Real.rpow_mul (ideleNorm_pos a).le, mul_comm]
  have hξsq : ∀ a : (AdeleRing (𝓞 K) K)ˣ,
      ((ξ ⟨a, Subgroup.mem_top a⟩ : ℂˣ) : ℂ) * conj ((ξ ⟨a, Subgroup.mem_top a⟩ : ℂˣ) : ℂ) =
        ((ideleNorm K (Matrix.GeneralLinearGroup.det (centralScalar (𝓞 K) K a)) ^ σ : ℝ) : ℂ) := by
    intro a
    rw [Complex.mul_conj, Complex.normSq_eq_norm_sq, hmod a]

  have scaling : ∀ (p q : AdelicGL2 (𝓞 K) K → ℂ), IsLsXiFunction (𝓞 K) K ⊤ ξ p → IsLsXiFunction (𝓞 K) K ⊤ ξ q →
      ∀ z : AdelicGL2 (𝓞 K) K,
        ∫ x in Φ₀, p (x * z) * conj (q (x * z)) ∂μ = ((nd z ^ σ : ℝ) : ℂ) * ∫ x in Φ₀, p x * conj (q x) ∂μ := by
    intro p q hp hq z
    obtain ⟨a, ha⟩ := R4UwAdj.exists_central_normDet_eq (K := K) (nd z) (nd_pos z)
    have hF : ∀ (γ : R4UwAdj.Γ K) (x : AdelicGL2 (𝓞 K) K),
        (fun y => p y * conj (q y)) (γ • x) = (fun y => p y * conj (q y)) x := by
      intro γ x
      obtain ⟨γ₀, hγ₀⟩ := R4UwAdj.Γ_smul_eq γ
      show p (γ • x) * conj (q (γ • x)) = p x * conj (q x)
      rw [R4UwAdj.Γ_smul, hγ₀, hp.left_invariant, hq.left_invariant]
    have h1 := R4UwAdj.setIntegral_comp_mulRight_eq α β hΦ₀' hFD' (fun y => p y * conj (q y)) hF z
      (centralScalar (𝓞 K) K a) ha
    show ∫ x in Φ₀, (fun y => p y * conj (q y)) (x * z) ∂(R4UwAdj.μ K) = _
    rw [h1]
    have h2 : ∀ x, (fun y => p y * conj (q y)) (x * centralScalar (𝓞 K) K a) =
        ((nd z ^ σ : ℝ) : ℂ) * (p x * conj (q x)) := by
      intro x
      show p (x * centralScalar (𝓞 K) K a) * conj (q (x * centralScalar (𝓞 K) K a)) = _
      rw [R4UwAdj.central_comm, hp.central_transform ⟨a, Subgroup.mem_top a⟩ x,
        hq.central_transform ⟨a, Subgroup.mem_top a⟩ x, map_mul]
      rw [show nd z = ideleNorm K (Matrix.GeneralLinearGroup.det (centralScalar (𝓞 K) K a)) from ha.symm,
        ← hξsq a]
      ring
    simp_rw [h2]
    exact integral_const_mul _ _
  have scaling_l : ∀ (p : AdelicGL2 (𝓞 K) K → ℂ), IsLsXiFunction (𝓞 K) K ⊤ ξ p →
      ∀ z : AdelicGL2 (𝓞 K) K,
        ∫⁻ x in Φ₀, (‖p (x * z)‖₊ : ℝ≥0∞) ^ 2 ∂μ = ENNReal.ofReal (nd z ^ σ) * ∫⁻ x in Φ₀, (‖p x‖₊ : ℝ≥0∞) ^ 2 ∂μ := by
    intro p hp z
    obtain ⟨a, ha⟩ := R4UwAdj.exists_central_normDet_eq (K := K) (nd z) (nd_pos z)
    have hF : ∀ (γ : R4UwAdj.Γ K) (x : AdelicGL2 (𝓞 K) K),
        (fun y => (‖p y‖₊ : ℝ≥0∞) ^ 2) (γ • x) = (fun y => (‖p y‖₊ : ℝ≥0∞) ^ 2) x := by
      intro γ x
      obtain ⟨γ₀, hγ₀⟩ := R4UwAdj.Γ_smul_eq γ
      show (‖p (γ • x)‖₊ : ℝ≥0∞) ^ 2 = (‖p x‖₊ : ℝ≥0∞) ^ 2
      rw [R4UwAdj.Γ_smul, hγ₀, hp.left_invariant]
    have h1 := R4UwAdj.setLIntegral_comp_mulRight_eq α β hΦ₀' hFD' (fun y => (‖p y‖₊ : ℝ≥0∞) ^ 2) hF z
      (centralScalar (𝓞 K) K a) ha
    show ∫⁻ x in Φ₀, (fun y => (‖p y‖₊ : ℝ≥0∞) ^ 2) (x * z) ∂(R4UwAdj.μ K) = _
    rw [h1]
    have hnorm : ‖((ξ ⟨a, Subgroup.mem_top a⟩ : ℂˣ) : ℂ)‖ ^ 2 = nd z ^ σ := by
      rw [hmod a]
      exact congrArg (fun r : ℝ => r ^ σ) ha
    have h2 : ∀ x, (fun y => (‖p y‖₊ : ℝ≥0∞) ^ 2) (x * centralScalar (𝓞 K) K a) =
        ENNReal.ofReal (nd z ^ σ) * (‖p x‖₊ : ℝ≥0∞) ^ 2 := by
      intro x
      show (‖p (x * centralScalar (𝓞 K) K a)‖₊ : ℝ≥0∞) ^ 2 = _
      rw [R4UwAdj.central_comm, hp.central_transform ⟨a, Subgroup.mem_top a⟩ x, nnnorm_mul,
        ENNReal.coe_mul, mul_pow, ← hnorm, ENNReal.ofReal_pow (norm_nonneg _), ofReal_norm]
      rfl
    simp_rw [h2]
    exact lintegral_const_mul' _ _ ENNReal.ofReal_ne_top

  have memLp_translate : ∀ {w : AdelicGL2 (𝓞 K) K → ℂ}, IsLsXiFunction (𝓞 K) K ⊤ ξ w → Continuous w →
      MemLp w 2 (μ.restrict Φ₀) → ∀ y : AdelicGL2 (𝓞 K) K, MemLp (fun x => w (x * y)) 2 (μ.restrict Φ₀) := by
    intro w hw hwc hw2 y
    have hmeas : AEStronglyMeasurable (fun x => w (x * y)) (μ.restrict Φ₀) :=
      (hwc.comp (continuous_id.mul continuous_const)).aestronglyMeasurable
    refine (memLp_two_iff_integrable_sq_norm hmeas).2 ?_
    refine ⟨(hmeas.norm.pow 2), ?_⟩
    have hfin : ∫⁻ x, ‖‖w x‖ ^ 2‖ₑ ∂(μ.restrict Φ₀) < ⊤ := ((memLp_two_iff_integrable_sq_norm hw2.1).1 hw2).2
    have hconv : ∀ (F : AdelicGL2 (𝓞 K) K → ℂ) (x : AdelicGL2 (𝓞 K) K),
        ‖‖F x‖ ^ 2‖ₑ = (‖F x‖₊ : ℝ≥0∞) ^ 2 := by
      intro F x
      rw [Real.enorm_eq_ofReal (sq_nonneg _), ENNReal.ofReal_pow (norm_nonneg _), ofReal_norm]
      rfl
    simp_rw [hconv] at hfin
    show ∫⁻ x, ‖‖w (x * y)‖ ^ 2‖ₑ ∂(μ.restrict Φ₀) < ⊤
    simp_rw [hconv]
    show ∫⁻ x in Φ₀, (‖w (x * y)‖₊ : ℝ≥0∞) ^ 2 ∂μ < ⊤
    rw [scaling_l w hw y]
    exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top hfin

  have int_mul_conj : ∀ (p q : AdelicGL2 (𝓞 K) K → ℂ), MemLp p 2 (μ.restrict Φ₀) → MemLp q 2 (μ.restrict Φ₀) →
      Integrable (fun x => p x * conj (q x)) (μ.restrict Φ₀) := by
    intro p q hp hq
    have hp' := (memLp_two_iff_integrable_sq_norm hp.1).1 hp
    have hq' := (memLp_two_iff_integrable_sq_norm hq.1).1 hq
    have hpt : ∀ x, ‖p x * conj (q x)‖ ≤ (‖p x‖ ^ 2 + ‖q x‖ ^ 2) / 2 := fun x => by
      rw [norm_mul, RCLike.norm_conj]
      nlinarith [sq_nonneg (‖p x‖ - ‖q x‖)]
    exact Integrable.mono' ((hp'.add hq').div_const 2)
      (hp.1.mul (Complex.continuous_conj.comp_aestronglyMeasurable hq.1)) (Filter.Eventually.of_forall hpt)

  have norm_int_le : ∀ (p q : AdelicGL2 (𝓞 K) K → ℂ), MemLp p 2 (μ.restrict Φ₀) → MemLp q 2 (μ.restrict Φ₀) →
      ∫ x in Φ₀, ‖p x * conj (q x)‖ ∂μ ≤
        ((∫ x in Φ₀, ‖p x‖ ^ 2 ∂μ) + ∫ x in Φ₀, ‖q x‖ ^ 2 ∂μ) / 2 := by
    intro p q hp hq
    have hp' := (memLp_two_iff_integrable_sq_norm hp.1).1 hp
    have hq' := (memLp_two_iff_integrable_sq_norm hq.1).1 hq
    have hpt : ∀ x, ‖p x * conj (q x)‖ ≤ (‖p x‖ ^ 2 + ‖q x‖ ^ 2) / 2 := fun x => by
      rw [norm_mul, RCLike.norm_conj]
      nlinarith [sq_nonneg (‖p x‖ - ‖q x‖)]
    calc ∫ x in Φ₀, ‖p x * conj (q x)‖ ∂μ ≤ ∫ x in Φ₀, (‖p x‖ ^ 2 + ‖q x‖ ^ 2) / 2 ∂μ :=
          integral_mono_of_nonneg (Filter.Eventually.of_forall fun x => norm_nonneg _)
            ((hp'.add hq').div_const 2) (Filter.Eventually.of_forall hpt)
      _ = ((∫ x in Φ₀, ‖p x‖ ^ 2 ∂μ) + ∫ x in Φ₀, ‖q x‖ ^ 2 ∂μ) / 2 := by
          rw [integral_div, integral_add hp' hq']

  have swap : ∀ (k : AdelicGL2 (𝓞 K) K → ℂ), Continuous k → HasCompactSupport k →
      ∀ (p q : AdelicGL2 (𝓞 K) K → ℂ), IsLsXiFunction (𝓞 K) K ⊤ ξ p → Continuous p → MemLp p 2 (μ.restrict Φ₀) →
        Continuous q → MemLp q 2 (μ.restrict Φ₀) →
        Integrable (fun w : AdelicGL2 (𝓞 K) K × AdelicGL2 (𝓞 K) K => k w.2 * (p (w.1 * w.2) * conj (q w.1)))
          ((μ.restrict Φ₀).prod μ) := by
    intro k hk hkc p q hp hpc hp2 hqc hq2
    have hFc : Continuous (fun w : AdelicGL2 (𝓞 K) K × AdelicGL2 (𝓞 K) K =>
        k w.2 * (p (w.1 * w.2) * conj (q w.1))) :=
      (hk.comp continuous_snd).mul ((hpc.comp (continuous_fst.mul continuous_snd)).mul
        (Complex.continuous_conj.comp (hqc.comp continuous_fst)))
    have hFm : AEStronglyMeasurable (fun w : AdelicGL2 (𝓞 K) K × AdelicGL2 (𝓞 K) K =>
        k w.2 * (p (w.1 * w.2) * conj (q w.1))) ((μ.restrict Φ₀).prod μ) := hFc.aestronglyMeasurable
    refine (integrable_prod_iff' hFm).2 ⟨Filter.Eventually.of_forall fun z => ?_, ?_⟩
    · exact (int_mul_conj _ _ (memLp_translate hp hpc hp2 z) hq2).const_mul (k z)

    · obtain ⟨T, hT⟩ := (hkc : IsCompact (tsupport k)).exists_bound_of_continuousOn
        ((nd_cont.rpow_const fun _ => Or.inl (nd_pos _).ne').continuousOn (s := tsupport k))
      set Ip : ℝ := ∫ x in Φ₀, ‖p x‖ ^ 2 ∂μ with hIp
      set Iq : ℝ := ∫ x in Φ₀, ‖q x‖ ^ 2 ∂μ with hIq
      have hIp0 : 0 ≤ Ip := integral_nonneg fun x => by positivity
      have hIq0 : 0 ≤ Iq := integral_nonneg fun x => by positivity
      set Cst : ℝ := (max T 0 * Ip + Iq) / 2 with hCst
      have hmeas : AEStronglyMeasurable
          (fun z => ∫ x, ‖k z * (p (x * z) * conj (q x))‖ ∂(μ.restrict Φ₀)) μ :=
        (hFc.norm.stronglyMeasurable.integral_prod_left' (μ := μ.restrict Φ₀)).aestronglyMeasurable
      refine Integrable.mono' ((hk.norm.integrable_of_hasCompactSupport hkc.norm).const_mul Cst) hmeas
        (Filter.Eventually.of_forall fun z => ?_)
      rw [Real.norm_of_nonneg (integral_nonneg fun x => norm_nonneg _)]
      by_cases hz : z ∈ tsupport k
      · have hsq : ∫ x in Φ₀, ‖p (x * z)‖ ^ 2 ∂μ = nd z ^ σ * Ip := by
          have h := scaling p p hp hp z
          have hre := congrArg Complex.re h
          rw [show (∫ x in Φ₀, p (x * z) * conj (p (x * z)) ∂μ) =
              ((∫ x in Φ₀, ‖p (x * z)‖ ^ 2 ∂μ : ℝ) : ℂ) from ?_,
            show (∫ x in Φ₀, p x * conj (p x) ∂μ) = ((∫ x in Φ₀, ‖p x‖ ^ 2 ∂μ : ℝ) : ℂ) from ?_] at hre
          · simpa using hre
          · have h2 : (fun x => p x * conj (p x)) = fun x => ((‖p x‖ ^ 2 : ℝ) : ℂ) := by
              funext x; rw [Complex.mul_conj, Complex.normSq_eq_norm_sq, Complex.ofReal_pow]
            rw [h2, integral_complex_ofReal]
          · have h2 : (fun x => p (x * z) * conj (p (x * z))) = fun x => ((‖p (x * z)‖ ^ 2 : ℝ) : ℂ) := by
              funext x; rw [Complex.mul_conj, Complex.normSq_eq_norm_sq, Complex.ofReal_pow]
            rw [h2, integral_complex_ofReal]
        have hTz : nd z ^ σ ≤ max T 0 :=
          ((le_abs_self _).trans ((Real.norm_eq_abs _).symm.le.trans (hT z hz))).trans (le_max_left _ _)
        calc ∫ x, ‖k z * (p (x * z) * conj (q x))‖ ∂(μ.restrict Φ₀)
            = ‖k z‖ * ∫ x in Φ₀, ‖p (x * z) * conj (q x)‖ ∂μ := by
              simp_rw [norm_mul (k z)]
              exact integral_const_mul _ _
          _ ≤ ‖k z‖ * (((∫ x in Φ₀, ‖p (x * z)‖ ^ 2 ∂μ) + ∫ x in Φ₀, ‖q x‖ ^ 2 ∂μ) / 2) :=
              mul_le_mul_of_nonneg_left (norm_int_le _ _ (memLp_translate hp hpc hp2 z) hq2) (norm_nonneg _)
          _ ≤ ‖k z‖ * Cst := by
              refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
              rw [hsq, hCst]
              refine div_le_div_of_nonneg_right (add_le_add ?_ le_rfl) (by norm_num)
              exact mul_le_mul_of_nonneg_right hTz hIp0
          _ = Cst * ‖k z‖ := mul_comm _ _
      · have hk0 : k z = 0 := image_eq_zero_of_notMem_tsupport hz
        simp only [hk0, zero_mul, norm_zero, integral_zero, mul_zero, le_refl]

  have hL : ∫ x in Φ₀, rightConv K u g x * conj (v x) ∂μ =
      ∫ z, g z * ∫ x in Φ₀, u (x * z) * conj (v x) ∂μ ∂μ := by
    have hint := swap g hg hgc u v hu huc hu₂ hvc hv₂
    calc ∫ x in Φ₀, rightConv K u g x * conj (v x) ∂μ
        = ∫ x in Φ₀, ∫ z, g z * (u (x * z) * conj (v x)) ∂μ ∂μ := by
          refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
          show rightConv K u g x * conj (v x) = _
          rw [rightConv_apply, ← integral_mul_const]
          exact integral_congr_ae (Filter.Eventually.of_forall fun z => by ring)
      _ = ∫ z, ∫ x in Φ₀, g z * (u (x * z) * conj (v x)) ∂μ ∂μ :=
          integral_integral_swap (by first | simpa [Function.uncurry] using hint | (simp only [Function.uncurry_def]; exact hint) | exact hint)
      _ = ∫ z, g z * ∫ x in Φ₀, u (x * z) * conj (v x) ∂μ ∂μ := by
          refine integral_congr_ae (Filter.Eventually.of_forall fun z => ?_)
          exact integral_const_mul _ _

  have hR : ∫ x in Φ₀, u x * conj (rightConv K v gf x) ∂μ =
      ∫ z, conj (gf z) * ∫ x in Φ₀, u x * conj (v (x * z)) ∂μ ∂μ := by

    have hint := swap gf hgf_c hgf_s v u hv hvc hv₂ huc hu₂
    have hint' : Integrable (fun w : AdelicGL2 (𝓞 K) K × AdelicGL2 (𝓞 K) K =>
        conj (gf w.2) * (u w.1 * conj (v (w.1 * w.2)))) ((μ.restrict Φ₀).prod μ) := by
      have h := (Complex.conjCLE.toContinuousLinearMap.integrable_comp hint :)
      refine h.congr (Filter.Eventually.of_forall fun w => ?_)
      show Complex.conjCLE (gf w.2 * (v (w.1 * w.2) * conj (u w.1))) = _
      rw [Complex.conjCLE_apply]
      simp only [map_mul, Complex.conj_conj]
      ring
    calc ∫ x in Φ₀, u x * conj (rightConv K v gf x) ∂μ
        = ∫ x in Φ₀, ∫ z, conj (gf z) * (u x * conj (v (x * z))) ∂μ ∂μ := by
          refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
          show u x * conj (rightConv K v gf x) = _
          rw [rightConv_apply, ← integral_conj, ← integral_const_mul]
          exact integral_congr_ae (Filter.Eventually.of_forall fun z => by
            simp only [map_mul]; ring)
      _ = ∫ z, ∫ x in Φ₀, conj (gf z) * (u x * conj (v (x * z))) ∂μ ∂μ :=
          integral_integral_swap (by first | simpa [Function.uncurry] using hint' | (simp only [Function.uncurry_def]; exact hint') | exact hint')
      _ = ∫ z, conj (gf z) * ∫ x in Φ₀, u x * conj (v (x * z)) ∂μ ∂μ := by
          refine integral_congr_ae (Filter.Eventually.of_forall fun z => ?_)
          exact integral_const_mul _ _

  let J : AdelicGL2 (𝓞 K) K → ℂ := fun z => ∫ x in Φ₀, u x * conj (v (x * z)) ∂μ
  have hI : ∀ z, ∫ x in Φ₀, u (x * z) * conj (v x) ∂μ = ((nd z ^ σ : ℝ) : ℂ) * J z⁻¹ := by
    intro z
    have h := scaling u (fun x => v (x * z⁻¹)) hu (lsxi_translate hv z⁻¹) z
    simp only [mul_assoc, mul_inv_cancel, mul_one] at h
    exact h
  have hflat : ∀ z, conj (gf z⁻¹) = g z * ((nd z ^ σ : ℝ) : ℂ) := by
    intro z
    show conj (conj (g z⁻¹⁻¹) * ((nd z⁻¹ ^ (-σ) : ℝ) : ℂ)) = _
    rw [inv_inv, map_mul, Complex.conj_conj, Complex.conj_ofReal]
    congr 2
    show ideleNorm K (Matrix.GeneralLinearGroup.det z⁻¹) ^ (-σ) = nd z ^ σ
    rw [R4UwAdj.normDet_inv, Real.inv_rpow (nd_pos z).le, Real.rpow_neg (nd_pos z).le, inv_inv]
  show ∫ x in Φ₀, rightConv K u g x * conj (v x) ∂μ = ∫ x in Φ₀, u x * conj (rightConv K v gf x) ∂μ
  rw [hL, hR, ← integral_inv_eq_self (fun z => conj (gf z) * ∫ x in Φ₀, u x * conj (v (x * z)) ∂μ) μ]
  refine integral_congr_ae (Filter.Eventually.of_forall fun z => ?_)
  show g z * ∫ x in Φ₀, u (x * z) * conj (v x) ∂μ = conj (gf z⁻¹) * J z⁻¹
  rw [hI z, hflat z, mul_assoc]

end S_AutomorphicForm_setIntegral_rightConv_mul_conj_eq_setIntegral_mul_conj_rightConv_flat_of_isLsXiFunction_of_isFundamentalDomain_slab
end P2MW
export P2MW.S_AutomorphicForm_setIntegral_rightConv_mul_conj_eq_setIntegral_mul_conj_rightConv_flat_of_isLsXiFunction_of_isFundamentalDomain_slab (solution)
