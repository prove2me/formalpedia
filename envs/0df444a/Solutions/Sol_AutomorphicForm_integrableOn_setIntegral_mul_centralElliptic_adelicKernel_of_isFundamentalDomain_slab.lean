-- Prove2me | solution 1 for AutomorphicForm.integrableOn_setIntegral_mul_centralElliptic_adelicKernel_of_isFundamentalDomain_slab
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:05.340288+00:00
-- url     : https://prove2.me/submissions/99023c97-ff49-5cfc-9a9b-877c906116b6

import Theorems.Thm_AutomorphicForm_integrableOn_adelicKernelEllipticPart_diag_of_isFundamentalDomain_slab
import Theorems.Thm_AutomorphicForm_adelicGLHaar_inter_setOf_ideleNorm_det_mem_Icc_lt_top_of_isFundamentalDomain
import Theorems.Thm_AutomorphicForm_adelicKernelLocalFiniteness
import Theorems.Thm_NumberField_TateGlobal_compactSpace_normOneIdeleClass
import Theorems.Thm_NumberField_AdeleRing_secondCountableTopology
import Theorems.Thm_NumberField_TateGlobal_continuous_ideleNorm
import Theorems.Thm_NumberField_TateGlobal_continuous_ideleNorm_det
import Theorems.Thm_NumberField_AdeleRing_distribHaarChar_algebraMap
import Theorems.Thm_NumberField_AdeleRing_distribHaarChar_eq_prod_norm_pow_mult_of_snd_eq_one
import Definitions.Def_AutomorphicForm_AdelicKernel
import Definitions.Def_NumberField_AdelicHaar
import Definitions.Def_NumberField_TateGlobalZeta
import Definitions.Def_NumberField_AdelicVolume
import Definitions.Def_M4aHerbrand_IdeleClassVocab
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AutomorphicForm_integrableOn_setIntegral_mul_centralElliptic_adelicKernel_of_isFundamentalDomain_slab
p2m_attr_erase "instance" "FLT.SmoothVectors.RightTranslationFn.instAddCommMonoid FLT.SmoothVectors.RightTranslationFn.instMulAction FLT.SmoothVectors.RightTranslationFn.instDistribMulAction instContinuousSMulOfDiscreteTopologyOfContinuousSMulDiscrete HeckePair.instSMulCommClassSubtypeForallMemSubmoduleHeckeAlgebra HeckePair.instAlgebraSubtypeForallMemSubmoduleHeckeAlgebra HeckePair.instOneSubtypeForallMemSubmoduleHeckeAlgebra HeckePair.instIsScalarTowerSubtypeForallMemSubmoduleHeckeAlgebra HeckePair.instRingSubtypeForallMemSubmoduleHeckeAlgebra HeckePair.instMulSubtypeForallMemSubmoduleHeckeAlgebra FixedPoints.instMulActionElemFixedPointsOfSMulCommClass_definitions FixedPoints.module FixedPoints.instSMulElemFixedPointsOfSMulCommClass_definitions FixedPoints.instAddCommMonoidElemFixedPoints_definitions instFiniteResidueFieldAdicCompletionRingOfIntegersWithZeroMultiplicativeInt_definitions NumberField.instCompactSpaceAdicCompletionIntegers Rat.adicCompletion.locallyCompactSpace NumberField.instFiniteResidueFieldAdicCompletionIntegers instWeaklyLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions instCountableOfNumberField_definitions RestrictedProduct.SecondCountableTopology_of_principal instCountableElemSetSetsCofinite_definitions"
p2m_attr_erase "simp" "AutomorphicForm.classSq_apply AutomorphicForm.classRepEmbedding_one AutomorphicForm.finIdeleExponentAt_one AutomorphicForm.classRepFinIdele_one AutomorphicForm.productionPinsGeneralOf_D AutomorphicForm.productionPinsGeneral_D AutomorphicForm.productionPinsGeneralOf_μ AutomorphicForm.productionPinsGeneralOf_U AutomorphicForm.productionPinsCompact_ν AutomorphicForm.productionPinsCompact_U AutomorphicForm.productionPinsCompact_D AutomorphicForm.productionPinsCompact_nS AutomorphicForm.productionPinsCompact_gen AutomorphicForm.productionPinsCompact_Z AutomorphicForm.productionPinsCompact_mS AutomorphicForm.productionPinsCompact_μ AutomorphicForm.productionPins_nS AutomorphicForm.productionPins_mS AutomorphicForm.productionPins_ν AutomorphicForm.productionPins_Z AutomorphicForm.productionPins_U AutomorphicForm.productionPins_μ AutomorphicForm.productionPins_gen AutomorphicForm.productionPins_D AutomorphicForm.unipotentGL2_zero AutomorphicForm.constantTerm_const AutomorphicForm.constantTerm_zero AutomorphicForm.unipotentGL2_coe FLT.SmoothVectors.RightTranslationFn.toFun_smul FLT.SmoothVectors.RightTranslationFn.mk_toFun FLT.SmoothVectors.RightTranslationFn.toFun_mk FLT.SmoothVectors.mem_smoothVectors_iff AutomorphicForm.HeckeEigensystem.ofRawCentral_toRawCentral AutomorphicForm.HeckeEigensystem.toRawCentral_ofRawCentral AutomorphicForm.HeckeEigensystem.ofRawCentral_a AutomorphicForm.HeckeEigensystem.ofRawCentral_b AutomorphicForm.HeckeEigensystem.toRawCentral_level AutomorphicForm.HeckeEigensystem.toRawCentral_a AutomorphicForm.HeckeEigensystem.ofRawCentral_level AutomorphicForm.HeckeEigensystem.toRawCentral_b"
p2m_attr_erase "simp" "AutomorphicForm.SmoothCuspRealizationAt.mk.injEq AutomorphicForm.degenerateEigensystem_a AutomorphicForm.SmoothCuspRealizationAt.mk.sizeOf_spec AutomorphicForm.degenerateEigensystem_b AutomorphicForm.HeckeEigensystem.map_b AutomorphicForm.HeckeEigensystem.map_a AutomorphicForm.HeckeEigensystem.map_level AutomorphicForm.CuspidalityNotion.mk.injEq AutomorphicForm.HeckeEigensystem.twist_b AutomorphicForm.satakePow_zero AutomorphicForm.HeckeEigensystem.twist_a AutomorphicForm.HeckeEigensystem.mk.injEq AutomorphicForm.HeckeEigensystem.mk.sizeOf_spec AutomorphicForm.DescentPackage.mk.injEq AutomorphicForm.DescentPackage.mk.sizeOf_spec AutomorphicForm.CuspidalityNotion.mk.sizeOf_spec AutomorphicForm.satakePow_one HeckePair.convTerm_mk HeckePair.coe_apply_add HeckePair.coe_apply_smul FixedPoints.coe_zero FixedPoints.coe_smul FixedPoints.coe_add ContinuousAddEquiv.restrictedProductPi_apply RestrictedProduct.flatten_homeomorph_apply RestrictedProduct.flatten_homeomorph'_symm_apply ContinuousMulEquiv.restrictedProductPi_symm_apply RestrictedProduct.flatten_homeomorph'_apply RestrictedProduct.flatten_homeomorph_symm_apply ContinuousMulEquiv.restrictedProductPi_apply ContinuousAddEquiv.restrictedProductPi_symm_apply RingEquiv.restrictedProductCongr_symm_apply RingEquiv.restrictedProductCongrRight_apply MulEquiv.restrictedProductCongrRight_apply Equiv.restrictedProductProd_symm_apply_coe Equiv.restrictedProductCongrRight_apply AddEquiv.restrictedProductCongr_apply Equiv.restrictedProductCongrLeft'_symm_apply_apply Equiv.restrictedProductCongr_apply_apply Equiv.restrictedProductCongrLeft_apply_apply"
p2m_attr_erase "simp" "RestrictedProduct.flatten_equiv'_apply AddEquiv.restrictedProductCongrRight_apply Equiv.restrictedProductCongr_symm_apply Equiv.restrictedProductCongrRight_symm_apply RestrictedProduct.flatten_equiv'_symm_apply AddEquiv.restrictedProductCongrLeft'_apply Equiv.restrictedProductCongrLeft'_apply RestrictedProduct.flatten_apply RingEquiv.restrictedProductCongr_apply_apply RingEquiv.restrictedProductCongrLeft'_apply Equiv.restrictedProductProd_apply RestrictedProduct.flatten_equiv_apply RestrictedProduct.flatten_equiv_symm_apply LinearEquiv.restrictedProductCongrLeft'_apply RestrictedProduct.not_mem_support RestrictedProduct.mem_structureSubring_iff RestrictedProduct.not_mem_mulSupport RestrictedProduct.support_neg RestrictedProduct.mem_indexSupport_iff RestrictedProduct.mulSupport_inv RestrictedProduct.mapAlongLinearMap_apply"

set_option autoImplicit false
set_option linter.unusedSectionVars false

p2m_open "MeasureTheory NumberField NumberField.AdelicHaar NumberField.TateGlobal AutomorphicForm~ideleNorm_det_globalPoints"
open scoped ENNReal Pointwise Topology

noncomputable section

namespace R1CentEllFold

variable {K : Type} [Field K] [NumberField K]

attribute [local instance] NumberField.AdelicHaar.glBorel NumberField.AdelicHaar.borelSpace_glBorel

theorem secondCountable_adele : SecondCountableTopology (AdeleRing (𝓞 K) K) :=
  NumberField.AdeleRing.secondCountableTopology K

scoped instance secondCountable_idele : SecondCountableTopology (AdeleRing (𝓞 K) K)ˣ := by
  haveI := secondCountable_adele (K := K)
  haveI : SecondCountableTopology (AdeleRing (𝓞 K) K)ᵐᵒᵖ :=
    MulOpposite.opHomeomorph.symm.secondCountableTopology
  exact Units.isEmbedding_embedProduct.secondCountableTopology

scoped instance secondCountable_gl : SecondCountableTopology (AdelicGL2 (𝓞 K) K) := by
  haveI := secondCountable_adele (K := K)
  haveI : SecondCountableTopology (Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 K) K)) :=
    inferInstanceAs (SecondCountableTopology (Fin 2 → Fin 2 → AdeleRing (𝓞 K) K))
  haveI : SecondCountableTopology (Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 K) K))ᵐᵒᵖ :=
    MulOpposite.opHomeomorph.symm.secondCountableTopology
  exact Units.isEmbedding_embedProduct.secondCountableTopology

scoped instance locallyCompact_idele : LocallyCompactSpace (AdeleRing (𝓞 K) K)ˣ := inferInstance

scoped instance sigmaCompact_idele : SigmaCompactSpace (AdeleRing (𝓞 K) K)ˣ := by
  haveI := secondCountable_adele (K := K)
  haveI : SigmaCompactSpace (AdeleRing (𝓞 K) K)ᵐᵒᵖ :=
    MulOpposite.opHomeomorph.symm.isClosedEmbedding.sigmaCompactSpace
  exact Units.isClosedEmbedding_embedProduct.sigmaCompactSpace

theorem isHaar : (adelicGLHaar (Fin 2) (𝓞 K) K).IsHaarMeasure :=
  isHaarMeasure_adelicGLHaar (Fin 2) (𝓞 K) K

attribute [local instance] isHaar

theorem coe_centralScalar (z : (AdeleRing (𝓞 K) K)ˣ) :
    ((centralScalar (𝓞 K) K z : AdelicGL2 (𝓞 K) K) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 K) K)) =
      Matrix.scalar (Fin 2) (z : AdeleRing (𝓞 K) K) := rfl

theorem continuous_centralScalar : Continuous (centralScalar (𝓞 K) K) := by
  have h : Continuous ((Matrix.scalar (Fin 2)).toMonoidHom :
      AdeleRing (𝓞 K) K → Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 K) K)) := by
    show Continuous fun a : AdeleRing (𝓞 K) K => Matrix.scalar (Fin 2) a
    simp_rw [Matrix.scalar_apply]
    exact (continuous_pi fun _ => continuous_id).matrix_diagonal
  exact h.units_map

theorem centralScalar_comm (z : (AdeleRing (𝓞 K) K)ˣ) (g : AdelicGL2 (𝓞 K) K) :
    centralScalar (𝓞 K) K z * g = g * centralScalar (𝓞 K) K z := by
  refine Units.ext ?_
  rw [Units.val_mul, Units.val_mul, coe_centralScalar]
  exact (Matrix.scalar_commute (n := Fin 2) (z : AdeleRing (𝓞 K) K) (fun r' => Commute.all _ r') _).eq

theorem conj_centralScalar_mul (x g : AdelicGL2 (𝓞 K) K) (z : (AdeleRing (𝓞 K) K)ˣ) :
    x⁻¹ * g * (centralScalar (𝓞 K) K z * x) = centralScalar (𝓞 K) K z * (x⁻¹ * g * x) := by
  rw [centralScalar_comm z (x⁻¹ * g * x), mul_assoc (x⁻¹ * g) x, ← centralScalar_comm z x,
    ← mul_assoc]

theorem det_centralScalar (z : (AdeleRing (𝓞 K) K)ˣ) :
    Matrix.GeneralLinearGroup.det (centralScalar (𝓞 K) K z) = z ^ 2 := by
  show Matrix.GeneralLinearGroup.det (Matrix.GeneralLinearGroup.scalar (Fin 2) z) = z ^ 2
  rw [Matrix.GeneralLinearGroup.det_scalar, Fintype.card_fin]

theorem det_globalPoints (γ : GL (Fin 2) K) :
    Matrix.GeneralLinearGroup.det (globalPoints (𝓞 K) K γ) =
      Units.map (algebraMap K (AdeleRing (𝓞 K) K)).toMonoidHom (Matrix.GeneralLinearGroup.det γ) := by
  unfold globalPoints
  rw [Matrix.GeneralLinearGroup.map_det]
  rfl

theorem ideleNorm_principal (a : Kˣ) :
    ideleNorm K (Units.map (algebraMap K (AdeleRing (𝓞 K) K)).toMonoidHom a) = 1 := by
  unfold ideleNorm
  rw [@NumberField.AdeleRing.distribHaarChar_algebraMap K _ _ (adeleBorel (𝓞 K) K)
    (borelSpace_adeleBorel (𝓞 K) K) a]
  simp

theorem ideleNorm_of_mem_range {p : (AdeleRing (𝓞 K) K)ˣ}
    (hp : p ∈ (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K)).range) :
    ideleNorm K p = 1 := by
  obtain ⟨a, rfl⟩ := hp
  exact ideleNorm_principal a

theorem ideleNorm_det_globalPoints (γ : GL (Fin 2) K) :
    ideleNorm K (Matrix.GeneralLinearGroup.det (globalPoints (𝓞 K) K γ)) = 1 := by
  rw [det_globalPoints, ideleNorm_principal]

theorem ideleNorm_det_conj (x : AdelicGL2 (𝓞 K) K) (γ : GL (Fin 2) K) (z : (AdeleRing (𝓞 K) K)ˣ) :
    ideleNorm K (Matrix.GeneralLinearGroup.det
      (x⁻¹ * globalPoints (𝓞 K) K γ * (centralScalar (𝓞 K) K z * x))) = ideleNorm K z ^ 2 := by
  simp only [map_mul, map_inv, det_centralScalar, ideleNorm_mul]
  rw [ideleNorm_det_globalPoints]
  have hx : ideleNorm K (Matrix.GeneralLinearGroup.det x)⁻¹ * ideleNorm K (Matrix.GeneralLinearGroup.det x)
      = 1 := by rw [← ideleNorm_mul, inv_mul_cancel]; unfold ideleNorm; simp
  calc ideleNorm K (Matrix.GeneralLinearGroup.det x)⁻¹ * 1 *
        (ideleNorm K (z ^ 2) * ideleNorm K (Matrix.GeneralLinearGroup.det x))
        = (ideleNorm K (Matrix.GeneralLinearGroup.det x)⁻¹ *
            ideleNorm K (Matrix.GeneralLinearGroup.det x)) * ideleNorm K (z ^ 2) := by ring
    _ = ideleNorm K z ^ 2 := by rw [hx, one_mul, sq, sq, ideleNorm_mul]

private theorem _root_.R1CentEllFold.continuous_ideleNorm_det :
    Continuous fun g : AdelicGL2 (𝓞 K) K => ideleNorm K (Matrix.GeneralLinearGroup.det g) :=
  NumberField.TateGlobal.continuous_ideleNorm_det K

p2m_export "R1CentEllFold" "continuous_ideleNorm_det"

def ratScalar (a : Kˣ) : GL (Fin 2) K := Matrix.GeneralLinearGroup.scalar (Fin 2) a

theorem coe_ratScalar (a : Kˣ) :
    ((ratScalar a : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) = (a : K) • (1 : Matrix (Fin 2) (Fin 2) K) := by
  show Matrix.scalar (Fin 2) (a : K) = _
  ext i j
  simp [Matrix.scalar_apply, Matrix.diagonal_apply, Matrix.one_apply]

theorem ratScalar_mul (a b : Kˣ) : ratScalar (a * b) = ratScalar a * ratScalar b := map_mul _ a b

theorem ratScalar_inv (a : Kˣ) : ratScalar a⁻¹ = (ratScalar a)⁻¹ := map_inv _ a

theorem globalPoints_ratScalar (a : Kˣ) :
    globalPoints (𝓞 K) K (ratScalar a) =
      centralScalar (𝓞 K) K (Units.map (algebraMap K (AdeleRing (𝓞 K) K)).toMonoidHom a) := by
  refine Units.ext ?_
  rw [coe_centralScalar]
  show (algebraMap K (AdeleRing (𝓞 K) K)).mapMatrix ((ratScalar a : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K)
    = Matrix.scalar (Fin 2) (algebraMap K (AdeleRing (𝓞 K) K) (a : K))
  rw [coe_ratScalar]
  ext i j
  simp only [RingHom.mapMatrix_apply, Matrix.map_apply, Matrix.smul_apply, Matrix.scalar_apply,
    Matrix.diagonal_apply, Matrix.one_apply, smul_eq_mul, mul_ite, mul_one, mul_zero]
  split_ifs <;> simp

theorem isCentralType_smul_iff {a : K} (ha : a ≠ 0) (M : Matrix (Fin 2) (Fin 2) K) :
    IsCentralType (a • M) ↔ IsCentralType M := by
  constructor
  · rintro ⟨c, hc⟩
    refine ⟨a⁻¹ * c, ?_⟩
    have : M = a⁻¹ • (a • M) := by rw [smul_smul, inv_mul_cancel₀ ha, one_smul]
    rw [this, hc, smul_smul]
  · rintro ⟨c, hc⟩
    exact ⟨a * c, by rw [hc, smul_smul]⟩

theorem eval_charpoly_fin_two (M : Matrix (Fin 2) (Fin 2) K) (t : K) :
    (M.charpoly).eval t = t ^ 2 - M.trace * t + M.det := by
  rw [Matrix.charpoly_fin_two]
  simp

theorem isEllipticType_smul_iff {a : K} (ha : a ≠ 0) (M : Matrix (Fin 2) (Fin 2) K) :
    IsEllipticType (a • M) ↔ IsEllipticType M := by
  have key : ∀ t : K, (a • M).charpoly.IsRoot t ↔ M.charpoly.IsRoot (a⁻¹ * t) := by
    intro t
    rw [Polynomial.IsRoot, Polynomial.IsRoot, eval_charpoly_fin_two, eval_charpoly_fin_two,
      Matrix.trace_smul, Matrix.det_smul, Fintype.card_fin, smul_eq_mul]
    have h2 : (a⁻¹ * t) ^ 2 - M.trace * (a⁻¹ * t) + M.det
        = a⁻¹ ^ 2 * (t ^ 2 - a * M.trace * t + a ^ 2 * M.det) := by
      field_simp
    rw [h2, mul_eq_zero, or_iff_right (pow_ne_zero 2 (inv_ne_zero ha))]
  constructor
  · intro h t ht
    refine h (a * t) ?_
    rw [key, inv_mul_cancel_left₀ ha]
    exact ht
  · intro h t ht
    exact h _ ((key t).mp ht)

theorem coe_mul_ratScalar (γ : GL (Fin 2) K) (a : Kˣ) :
    ((γ * ratScalar a : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) =
      (a : K) • ((γ : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) := by
  rw [Units.val_mul, coe_ratScalar, Matrix.mul_smul, Matrix.mul_one]

theorem mul_ratScalar_mem_centralCell_iff (γ : GL (Fin 2) K) (a : Kˣ) :
    γ * ratScalar a ∈ centralCell K ↔ γ ∈ centralCell K := by
  rw [mem_centralCell_iff, mem_centralCell_iff, coe_mul_ratScalar]
  exact isCentralType_smul_iff a.ne_zero _

theorem mul_ratScalar_mem_ellipticCell_iff (γ : GL (Fin 2) K) (a : Kˣ) :
    γ * ratScalar a ∈ ellipticCell K ↔ γ ∈ ellipticCell K := by
  rw [mem_ellipticCell_iff, mem_ellipticCell_iff, coe_mul_ratScalar]
  exact isEllipticType_smul_iff a.ne_zero _

def ScalarStable (𝒞 : Set (GL (Fin 2) K)) : Prop := ∀ (a : Kˣ) (γ : GL (Fin 2) K), γ ∈ 𝒞 → γ * ratScalar a ∈ 𝒞

theorem scalarStable_centralCell : ScalarStable (centralCell K) :=
  fun a γ h => (mul_ratScalar_mem_centralCell_iff γ a).mpr h

theorem scalarStable_ellipticCell : ScalarStable (ellipticCell K) :=
  fun a γ h => (mul_ratScalar_mem_ellipticCell_iff γ a).mpr h

theorem ScalarStable.bijOn {𝒞 : Set (GL (Fin 2) K)} (h𝒞 : ScalarStable 𝒞) (a : Kˣ) :
    Set.BijOn (fun γ => γ * ratScalar a) 𝒞 𝒞 := by
  refine ⟨fun γ hγ => h𝒞 a γ hγ, fun γ _ γ' _ h => mul_right_cancel h, fun γ hγ => ?_⟩
  refine ⟨γ * ratScalar a⁻¹, h𝒞 a⁻¹ γ hγ, ?_⟩
  show γ * ratScalar a⁻¹ * ratScalar a = γ
  rw [mul_assoc, ← ratScalar_mul, inv_mul_cancel, ratScalar, map_one, mul_one]

def cellSum (𝒞 : Set (GL (Fin 2) K)) {E : Type*} [AddCommMonoid E] (h : AdelicGL2 (𝓞 K) K → E)
    (x y : AdelicGL2 (𝓞 K) K) : E :=
  ∑ᶠ γ ∈ 𝒞, h (x⁻¹ * globalPoints (𝓞 K) K γ * y)

theorem adelicKernelCentralPart_eq_cellSum {E : Type*} [AddCommMonoid E] (h : AdelicGL2 (𝓞 K) K → E)
    (x y : AdelicGL2 (𝓞 K) K) : adelicKernelCentralPart K h x y = cellSum (centralCell K) h x y := rfl

theorem adelicKernelEllipticPart_eq_cellSum {E : Type*} [AddCommMonoid E] (h : AdelicGL2 (𝓞 K) K → E)
    (x y : AdelicGL2 (𝓞 K) K) : adelicKernelEllipticPart K h x y = cellSum (ellipticCell K) h x y := rfl

theorem finite_conj_mem {C : Set (AdelicGL2 (𝓞 K) K)} (hC : IsCompact C) (x y : AdelicGL2 (𝓞 K) K) :
    {γ : GL (Fin 2) K | x⁻¹ * globalPoints (𝓞 K) K γ * y ∈ C}.Finite :=
  AutomorphicForm.adelicKernelLocalFiniteness K C hC x y

theorem finite_conj_mem_of_isCompact {N : Set (AdelicGL2 (𝓞 K) K)} {M : Set (AdeleRing (𝓞 K) K)ˣ}
    (hN : IsCompact N) (hM : IsCompact M) {C : Set (AdelicGL2 (𝓞 K) K)} (hC : IsCompact C) :
    {γ : GL (Fin 2) K | ∃ x ∈ N, ∃ z ∈ M,
      x⁻¹ * globalPoints (𝓞 K) K γ * (centralScalar (𝓞 K) K z * x) ∈ C}.Finite := by
  set φ : (AdelicGL2 (𝓞 K) K × AdelicGL2 (𝓞 K) K) × (AdeleRing (𝓞 K) K)ˣ → AdelicGL2 (𝓞 K) K :=
    fun p => p.1.1 * p.1.2 * p.1.1⁻¹ * (centralScalar (𝓞 K) K p.2)⁻¹ with hφ
  have hφc : Continuous φ := by
    refine ((continuous_fst.comp continuous_fst).mul (continuous_snd.comp continuous_fst)).mul
      (continuous_fst.comp continuous_fst).inv |>.mul ?_
    exact (continuous_centralScalar.comp continuous_snd).inv
  have hC' : IsCompact (φ '' ((N ×ˢ C) ×ˢ M)) := ((hN.prod hC).prod hM).image hφc
  refine (finite_conj_mem hC' 1 1).subset ?_
  rintro γ ⟨x, hx, z, hz, hmem⟩
  simp only [Set.mem_setOf_eq, inv_one, one_mul, mul_one]
  refine ⟨((x, x⁻¹ * globalPoints (𝓞 K) K γ * (centralScalar (𝓞 K) K z * x)), z), ⟨⟨hx, hmem⟩, hz⟩, ?_⟩
  simp only [hφ]
  group

theorem cellSum_eq_sum {𝒞 : Set (GL (Fin 2) K)} {E : Type*} [AddCommMonoid E]
    (h : AdelicGL2 (𝓞 K) K → E) (x y : AdelicGL2 (𝓞 K) K) {T : Finset (GL (Fin 2) K)}
    (hT : (T : Set (GL (Fin 2) K)) ⊆ 𝒞)
    (hsupp : ∀ γ ∈ 𝒞, h (x⁻¹ * globalPoints (𝓞 K) K γ * y) ≠ 0 → γ ∈ T) :
    cellSum 𝒞 h x y = ∑ γ ∈ T, h (x⁻¹ * globalPoints (𝓞 K) K γ * y) := by
  unfold cellSum
  refine finsum_mem_eq_sum_of_subset _ ?_ hT
  rintro γ ⟨hγ, hne⟩
  exact hsupp γ hγ hne

theorem continuous_cellSum_fold (𝒞 : Set (GL (Fin 2) K)) {E : Type*} [AddCommMonoid E]
    [TopologicalSpace E] [ContinuousAdd E] (h : AdelicGL2 (𝓞 K) K → E) (hh : Continuous h)
    (hhc : HasCompactSupport h) :
    Continuous fun p : AdelicGL2 (𝓞 K) K × (AdeleRing (𝓞 K) K)ˣ =>
      cellSum 𝒞 h p.1 (centralScalar (𝓞 K) K p.2 * p.1) := by
  classical
  rw [continuous_iff_continuousAt]
  rintro ⟨x₀, z₀⟩
  obtain ⟨N, hN, hNx⟩ := exists_compact_mem_nhds x₀
  obtain ⟨M, hM, hMz⟩ := exists_compact_mem_nhds z₀
  have hfin := finite_conj_mem_of_isCompact hN hM hhc.isCompact
  set T : Finset (GL (Fin 2) K) := hfin.toFinset.filter (· ∈ 𝒞) with hTdef
  have hT : (T : Set (GL (Fin 2) K)) ⊆ 𝒞 := by
    intro γ hγ
    rw [hTdef, Finset.coe_filter] at hγ
    exact hγ.2
  have heq : Set.EqOn
      (fun p : AdelicGL2 (𝓞 K) K × (AdeleRing (𝓞 K) K)ˣ =>
        ∑ γ ∈ T, h (p.1⁻¹ * globalPoints (𝓞 K) K γ * (centralScalar (𝓞 K) K p.2 * p.1)))
      (fun p => cellSum 𝒞 h p.1 (centralScalar (𝓞 K) K p.2 * p.1)) (N ×ˢ M) := by
    rintro ⟨x, z⟩ ⟨hx, hz⟩
    refine (cellSum_eq_sum h x _ hT fun γ hγ hne => ?_).symm
    rw [hTdef, Finset.mem_filter, Set.Finite.mem_toFinset]
    exact ⟨⟨x, hx, z, hz, subset_tsupport _ hne⟩, hγ⟩
  have hcont : Continuous fun p : AdelicGL2 (𝓞 K) K × (AdeleRing (𝓞 K) K)ˣ =>
      ∑ γ ∈ T, h (p.1⁻¹ * globalPoints (𝓞 K) K γ * (centralScalar (𝓞 K) K p.2 * p.1)) := by
    refine continuous_finsetSum _ fun γ _ => hh.comp ?_
    exact (continuous_fst.inv.mul continuous_const).mul
      ((continuous_centralScalar.comp continuous_snd).mul continuous_fst)
  exact hcont.continuousAt.congr_of_eventuallyEq
    ((Filter.eventuallyEq_of_mem (prod_mem_nhds hNx hMz) heq).symm)

theorem continuous_cellSum_diag (𝒞 : Set (GL (Fin 2) K)) {E : Type*} [AddCommMonoid E]
    [TopologicalSpace E] [ContinuousAdd E] (h : AdelicGL2 (𝓞 K) K → E) (hh : Continuous h)
    (hhc : HasCompactSupport h) :
    Continuous fun x : AdelicGL2 (𝓞 K) K => cellSum 𝒞 h x x := by
  have := (continuous_cellSum_fold 𝒞 h hh hhc).comp
    (continuous_id.prodMk (continuous_const (y := (1 : (AdeleRing (𝓞 K) K)ˣ))))
  simpa [Function.comp_def, map_one, one_mul] using this

def realEmb (w : InfinitePlace K) : ℝ →+* w.Completion := by
  classical
  exact if hw : w.IsReal then (InfinitePlace.Completion.ringEquivRealOfIsReal hw).symm.toRingHom
  else ((InfinitePlace.Completion.ringEquivComplexOfIsComplex
    (InfinitePlace.not_isReal_iff_isComplex.mp hw)).symm.toRingHom).comp Complex.ofRealHom

theorem extensionEmbedding_realEmb (w : InfinitePlace K) (r : ℝ) :
    InfinitePlace.Completion.extensionEmbedding w (realEmb w r) = (r : ℂ) := by
  unfold realEmb
  split_ifs with hw
  · rw [RingEquiv.toRingHom_eq_coe, RingHom.coe_coe,
      ← InfinitePlace.Completion.extensionEmbeddingOfIsReal_apply hw,
      ← InfinitePlace.Completion.ringEquivRealOfIsReal_apply hw, RingEquiv.apply_symm_apply]
  · rw [RingHom.comp_apply, RingEquiv.toRingHom_eq_coe, RingHom.coe_coe,
      ← InfinitePlace.Completion.ringEquivComplexOfIsComplex_apply
        (InfinitePlace.not_isReal_iff_isComplex.mp hw), RingEquiv.apply_symm_apply]
    rfl

theorem norm_realEmb (w : InfinitePlace K) (r : ℝ) : ‖realEmb w r‖ = |r| := by
  rw [← (InfinitePlace.Completion.isometry_extensionEmbedding w).norm_map_of_map_zero (map_zero _),
    extensionEmbedding_realEmb, Complex.norm_real, Real.norm_eq_abs]

theorem realEmb_ne_zero (w : InfinitePlace K) {r : ℝ} (hr : r ≠ 0) : realEmb w r ≠ 0 := by
  intro h
  have := norm_realEmb w r
  rw [h, norm_zero] at this
  exact hr (abs_eq_zero.mp this.symm)

theorem continuous_realEmb (w : InfinitePlace K) : Continuous (realEmb w) :=
  (AddMonoidHomClass.isometry_of_norm (realEmb w) fun r => by
    rw [norm_realEmb, Real.norm_eq_abs]).continuous

theorem ideleNorm_archCentralUnit (w₀ : InfinitePlace K) (a : (w₀.Completion)ˣ) :
    ideleNorm K (NumberField.AdelicVolume.archCentralUnit K w₀ a) =
      ‖(a : w₀.Completion)‖ ^ w₀.mult := by
  classical
  unfold ideleNorm
  have h := NumberField.AdeleRing.distribHaarChar_eq_prod_norm_pow_mult_of_snd_eq_one K
    (NumberField.AdelicVolume.archCentralUnit K w₀ a) rfl
  rw [show ((distribHaarChar (AdeleRing (𝓞 K) K)) (NumberField.AdelicVolume.archCentralUnit K w₀ a) : ℝ)
      = ((MeasureTheory.distribHaarChar (AdeleRing (RingOfIntegers K) K)
          (NumberField.AdelicVolume.archCentralUnit K w₀ a) : NNReal) : ℝ) from rfl, h]
  rw [Finset.prod_eq_single w₀]
  · congr 1
    show ‖Function.update (1 : InfiniteAdeleRing K) w₀ (a : w₀.Completion) w₀‖ = _
    rw [Function.update_self]
  · intro w _ hw
    show ‖Function.update (1 : InfiniteAdeleRing K) w₀ (a : w₀.Completion) w‖ ^ w.mult = 1
    rw [Function.update_of_ne hw, show (1 : InfiniteAdeleRing K) w = 1 from rfl, norm_one, one_pow]
  · intro h; exact absurd (Finset.mem_univ w₀) h

def rayUnit (w : InfinitePlace K) (t : ℝ) : (w.Completion)ˣ :=
  Units.mk0 (realEmb w (Real.exp t)) (realEmb_ne_zero w (Real.exp_pos t).ne')

def ray (w : InfinitePlace K) (t : ℝ) : (AdeleRing (𝓞 K) K)ˣ :=
  NumberField.AdelicVolume.archCentralUnit K w (rayUnit w t)

theorem ideleNorm_ray (w : InfinitePlace K) (t : ℝ) : ideleNorm K (ray w t) = Real.exp t ^ w.mult := by
  rw [ray, ideleNorm_archCentralUnit, rayUnit, Units.val_mk0, norm_realEmb, abs_of_pos (Real.exp_pos t)]

open scoped Classical in
theorem continuous_ray (w : InfinitePlace K) : Continuous (ray (K := K) w) := by
  have h1 : Continuous fun t : ℝ => ((rayUnit w t : (w.Completion)ˣ) : w.Completion) :=
    (continuous_realEmb w).comp Real.continuous_exp
  have h2 : Continuous fun t : ℝ => (((rayUnit w t)⁻¹ : (w.Completion)ˣ) : w.Completion) := by
    have : (fun t : ℝ => (((rayUnit w t)⁻¹ : (w.Completion)ˣ) : w.Completion)) =
        fun t => realEmb w (Real.exp (-t)) := by
      funext t
      rw [Units.val_inv_eq_inv_val, rayUnit, Units.val_mk0, Real.exp_neg, map_inv₀]
    rw [this]
    exact (continuous_realEmb w).comp (Real.continuous_exp.comp continuous_neg)
  refine Units.continuous_iff.mpr ⟨?_, ?_⟩
  · show Continuous fun t => ((Function.update (1 : InfiniteAdeleRing K) w
      ((rayUnit w t : (w.Completion)ˣ) : w.Completion), (1 : IsDedekindDomain.FiniteAdeleRing (𝓞 K) K)) : AdeleRing (𝓞 K) K)
    exact (continuous_const.update w h1).prodMk continuous_const
  · show Continuous fun t => ((Function.update (1 : InfiniteAdeleRing K) w
      (((rayUnit w t)⁻¹ : (w.Completion)ˣ) : w.Completion), (1 : IsDedekindDomain.FiniteAdeleRing (𝓞 K) K)) : AdeleRing (𝓞 K) K)
    exact (continuous_const.update w h2).prodMk continuous_const

theorem ideleNorm_inv (z : (AdeleRing (𝓞 K) K)ˣ) : ideleNorm K z⁻¹ = (ideleNorm K z)⁻¹ := by
  unfold ideleNorm; rw [map_inv, NNReal.coe_inv]

theorem principalIdeles_eq :
    M4aHerbrand.principalIdeles (𝓞 K) K =
      (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K)).range := rfl

theorem exists_isCompact_band_repr {a b : ℝ} (ha : 0 < a) :
    ∃ Z₀ : Set (AdeleRing (𝓞 K) K)ˣ, IsCompact Z₀ ∧ ∀ z : (AdeleRing (𝓞 K) K)ˣ,
      ideleNorm K z ∈ Set.Icc a b →
        ∃ l ∈ M4aHerbrand.principalIdeles (𝓞 K) K, ∃ z₀ ∈ Z₀, z = l * z₀ := by
  classical
  obtain ⟨V, hVc, hV1⟩ := exists_compact_mem_nhds (1 : (AdeleRing (𝓞 K) K)ˣ)
  haveI := NumberField.TateGlobal.compactSpace_normOneIdeleClass K
  set H := normOneIdeles K with hH
  set P := (M4aHerbrand.principalIdeles (𝓞 K) K).subgroupOf H with hP
  set W : Set H := Subtype.val ⁻¹' interior V with hW
  have hWopen : IsOpen W := isOpen_interior.preimage continuous_subtype_val
  let U : H → Set (H ⧸ P) := fun t => QuotientGroup.mk '' ((fun v : H => t * v) '' W)
  have hUopen : ∀ t, IsOpen (U t) := fun t =>
    QuotientGroup.isOpenMap_coe _ (isOpenMap_mul_left t _ hWopen)
  have hUcov : (Set.univ : Set (H ⧸ P)) ⊆ ⋃ t, U t := by
    intro q _
    obtain ⟨t, rfl⟩ := QuotientGroup.mk_surjective q
    refine Set.mem_iUnion.mpr ⟨t, ⟨t * 1, ⟨1, ?_, rfl⟩, by rw [mul_one]⟩⟩
    show ((1 : H) : (AdeleRing (𝓞 K) K)ˣ) ∈ interior V
    exact mem_interior_iff_mem_nhds.mpr hV1
  obtain ⟨ι, hι⟩ := isCompact_univ.elim_finite_subcover U hUopen hUcov
  obtain ⟨w₀⟩ : Nonempty (InfinitePlace K) := inferInstance
  have hm : (0 : ℝ) < w₀.mult := by
    have := InfinitePlace.mult_pos (w := w₀); exact_mod_cast this
  set I : Set ℝ := Set.Icc (Real.log a / w₀.mult) (Real.log b / w₀.mult) with hI
  set Φ₀ : ((AdeleRing (𝓞 K) K)ˣ × (AdeleRing (𝓞 K) K)ˣ) × ℝ → (AdeleRing (𝓞 K) K)ˣ :=
    fun p => p.1.1 * p.1.2 * ray w₀ p.2 with hΦ₀
  have hΦ₀c : Continuous Φ₀ :=
    ((continuous_fst.comp continuous_fst).mul (continuous_snd.comp continuous_fst)).mul
      ((continuous_ray w₀).comp continuous_snd)
  refine ⟨Φ₀ '' (((((↑) : H → (AdeleRing (𝓞 K) K)ˣ) '' (ι : Set H)) ×ˢ V) ×ˢ I), ?_, ?_⟩
  · exact ((((ι.finite_toSet.image _).isCompact).prod hVc).prod isCompact_Icc).image hΦ₀c
  · intro z hz
    have hr : 0 < ideleNorm K z := ideleNorm_pos z
    set t₀ : ℝ := Real.log (ideleNorm K z) / w₀.mult with ht₀
    have hray : ideleNorm K (ray w₀ t₀) = ideleNorm K z := by
      rw [ideleNorm_ray, ← Real.exp_nat_mul, ht₀, mul_div_cancel₀ _ hm.ne', Real.exp_log hr]
    have ht₀I : t₀ ∈ I := by
      refine ⟨div_le_div_of_nonneg_right (Real.log_le_log ha hz.1) hm.le,
        div_le_div_of_nonneg_right (Real.log_le_log hr hz.2) hm.le⟩
    set u : (AdeleRing (𝓞 K) K)ˣ := z * (ray w₀ t₀)⁻¹ with hu
    have huH : u ∈ H := by
      rw [hH, mem_normOneIdeles_iff, hu, ideleNorm_mul, ideleNorm_inv, hray, mul_inv_cancel₀ hr.ne']
    have hq := hι (Set.mem_univ (QuotientGroup.mk (⟨u, huH⟩ : H) : H ⧸ P))
    simp only [Set.mem_iUnion] at hq
    obtain ⟨t, ht, hmem⟩ := hq
    obtain ⟨y, ⟨v, hv, rfl⟩, hyt⟩ := hmem
    have hrel : (t * v)⁻¹ * (⟨u, huH⟩ : H) ∈ P := QuotientGroup.eq.mp hyt
    rw [hP, Subgroup.mem_subgroupOf] at hrel
    refine ⟨(((t * v)⁻¹ * (⟨u, huH⟩ : H) : H) : (AdeleRing (𝓞 K) K)ˣ), hrel,
      (t : (AdeleRing (𝓞 K) K)ˣ) * (v : (AdeleRing (𝓞 K) K)ˣ) * ray w₀ t₀,
      ⟨(((t : (AdeleRing (𝓞 K) K)ˣ), (v : (AdeleRing (𝓞 K) K)ˣ)), t₀),
        ⟨⟨⟨t, ht, rfl⟩, interior_subset hv⟩, ht₀I⟩, rfl⟩, ?_⟩
    show z = ((t : (AdeleRing (𝓞 K) K)ˣ) * (v : (AdeleRing (𝓞 K) K)ˣ))⁻¹ * (z * (ray w₀ t₀)⁻¹) *
      ((t : (AdeleRing (𝓞 K) K)ˣ) * (v : (AdeleRing (𝓞 K) K)ˣ) * ray w₀ t₀)
    set X : (AdeleRing (𝓞 K) K)ˣ := (t : (AdeleRing (𝓞 K) K)ˣ) * (v : (AdeleRing (𝓞 K) K)ˣ)
    rw [mul_assoc, mul_assoc, mul_comm X (ray w₀ t₀), inv_mul_cancel_left, mul_comm z X,
      inv_mul_cancel_left]

theorem countable_numberField : Countable K :=
  (Module.Free.chooseBasis ℚ K).equivFun.toEquiv.countable_iff.2 inferInstance

scoped instance countable_principalIdeles : Countable (M4aHerbrand.principalIdeles (𝓞 K) K) := by
  haveI := countable_numberField (K := K)
  haveI : Countable Kˣ :=
    Function.Injective.countable (f := (Units.val : Kˣ → K)) Units.val_injective
  exact Function.Surjective.countable (MonoidHom.rangeRestrict_surjective _)

theorem measure_inter_lt_top_of_repr [MeasurableSpace (AdeleRing (𝓞 K) K)ˣ] [BorelSpace (AdeleRing (𝓞 K) K)ˣ]
    (ν : Measure (AdeleRing (𝓞 K) K)ˣ) [ν.IsHaarMeasure] {Ω : Set (AdeleRing (𝓞 K) K)ˣ}
    (hΩ : IsFundamentalDomain (M4aHerbrand.principalIdeles (𝓞 K) K) Ω ν)
    {B Z₀ : Set (AdeleRing (𝓞 K) K)ˣ} (hZ₀ : IsCompact Z₀)
    (hB : ∀ z ∈ B, ∃ l ∈ M4aHerbrand.principalIdeles (𝓞 K) K, ∃ z₀ ∈ Z₀, z = l * z₀) :
    ν (Ω ∩ B) < ∞ := by
  calc ν (Ω ∩ B) ≤ ν (⋃ l : M4aHerbrand.principalIdeles (𝓞 K) K, (l • Z₀ ∩ Ω)) := by
        refine measure_mono fun z hz => ?_
        obtain ⟨l, hl, z₀, hz₀, rfl⟩ := hB z hz.2
        exact Set.mem_iUnion.mpr ⟨⟨l, hl⟩, Set.smul_mem_smul_set hz₀, hz.1⟩
    _ ≤ ∑' l : M4aHerbrand.principalIdeles (𝓞 K) K, ν (l • Z₀ ∩ Ω) := measure_iUnion_le _
    _ = ν Z₀ := (hΩ.measure_eq_tsum Z₀).symm
    _ < ∞ := hZ₀.measure_lt_top

theorem cellSum_fold_principal_mul {𝒞 : Set (GL (Fin 2) K)} (h𝒞 : ScalarStable 𝒞) {E : Type*}
    [AddCommMonoid E] (h : AdelicGL2 (𝓞 K) K → E) (x : AdelicGL2 (𝓞 K) K) {l : (AdeleRing (𝓞 K) K)ˣ}
    (hl : l ∈ M4aHerbrand.principalIdeles (𝓞 K) K) (z : (AdeleRing (𝓞 K) K)ˣ) :
    cellSum 𝒞 h x (centralScalar (𝓞 K) K (l * z) * x) = cellSum 𝒞 h x (centralScalar (𝓞 K) K z * x) := by
  obtain ⟨a, rfl⟩ := hl
  unfold cellSum
  refine finsum_mem_eq_of_bijOn (fun γ => γ * ratScalar a) (h𝒞.bijOn a) fun γ _ => ?_
  simp only [map_mul, globalPoints_ratScalar]
  congr 1
  simp only [mul_assoc]
  rfl

theorem xi_principal_mul (ξ : (⊤ : Subgroup (AdeleRing (𝓞 K) K)ˣ) →* ℂˣ)
    (hξt : ∀ z : (AdeleRing (𝓞 K) K)ˣ, z ∈ M4aHerbrand.principalIdeles (𝓞 K) K →
      ξ ⟨z, Subgroup.mem_top z⟩ = 1)
    {l : (AdeleRing (𝓞 K) K)ˣ} (hl : l ∈ M4aHerbrand.principalIdeles (𝓞 K) K) (z : (AdeleRing (𝓞 K) K)ˣ) :
    ξ ⟨l * z, Subgroup.mem_top (l * z)⟩ = ξ ⟨z, Subgroup.mem_top z⟩ := by
  have : (⟨l * z, Subgroup.mem_top (l * z)⟩ : (⊤ : Subgroup (AdeleRing (𝓞 K) K)ˣ)) =
      ⟨l, Subgroup.mem_top l⟩ * ⟨z, Subgroup.mem_top z⟩ := rfl
  rw [this, map_mul, hξt l hl, one_mul]

def supTest (f : AdelicGL2 (𝓞 K) K → ℂ) (Z₀ : Set (AdeleRing (𝓞 K) K)ˣ) (g : AdelicGL2 (𝓞 K) K) : ℝ :=
  sSup ((fun z₀ : (AdeleRing (𝓞 K) K)ˣ => ‖f (centralScalar (𝓞 K) K z₀ * g)‖) '' Z₀)

theorem continuous_uncurry_norm {f : AdelicGL2 (𝓞 K) K → ℂ} (hf : Continuous f) :
    Continuous (Function.HasUncurry.uncurry fun (g : AdelicGL2 (𝓞 K) K) (z₀ : (AdeleRing (𝓞 K) K)ˣ) =>
      ‖f (centralScalar (𝓞 K) K z₀ * g)‖) := by
  show Continuous fun p : AdelicGL2 (𝓞 K) K × (AdeleRing (𝓞 K) K)ˣ => ‖f (centralScalar (𝓞 K) K p.2 * p.1)‖
  exact (hf.comp ((continuous_centralScalar.comp continuous_snd).mul continuous_fst)).norm

theorem continuous_supTest {f : AdelicGL2 (𝓞 K) K → ℂ} (hf : Continuous f) {Z₀ : Set (AdeleRing (𝓞 K) K)ˣ}
    (hZ₀ : IsCompact Z₀) : Continuous (supTest f Z₀) :=
  hZ₀.continuous_sSup (continuous_uncurry_norm hf)

theorem norm_le_supTest {f : AdelicGL2 (𝓞 K) K → ℂ} (hf : Continuous f) {Z₀ : Set (AdeleRing (𝓞 K) K)ˣ}
    (hZ₀ : IsCompact Z₀) {z₀ : (AdeleRing (𝓞 K) K)ˣ} (hz₀ : z₀ ∈ Z₀) (g : AdelicGL2 (𝓞 K) K) :
    ‖f (centralScalar (𝓞 K) K z₀ * g)‖ ≤ supTest f Z₀ g := by
  refine le_csSup (hZ₀.bddAbove_image ?_) (Set.mem_image_of_mem _ hz₀)
  exact ((hf.comp ((continuous_centralScalar).mul continuous_const)).norm).continuousOn

theorem supTest_nonneg (f : AdelicGL2 (𝓞 K) K → ℂ) (Z₀ : Set (AdeleRing (𝓞 K) K)ˣ) (g : AdelicGL2 (𝓞 K) K) :
    0 ≤ supTest f Z₀ g :=
  Real.sSup_nonneg (by rintro _ ⟨z₀, _, rfl⟩; exact norm_nonneg _)

theorem hasCompactSupport_supTest {f : AdelicGL2 (𝓞 K) K → ℂ} (hfc : HasCompactSupport f)
    {Z₀ : Set (AdeleRing (𝓞 K) K)ˣ} (hZ₀ : IsCompact Z₀) : HasCompactSupport (supTest f Z₀) := by
  set S : Set (AdelicGL2 (𝓞 K) K) :=
    (fun p : (AdeleRing (𝓞 K) K)ˣ × AdelicGL2 (𝓞 K) K => (centralScalar (𝓞 K) K p.1)⁻¹ * p.2) ''
      (Z₀ ×ˢ tsupport f) with hS
  have hSc : IsCompact S :=
    (hZ₀.prod hfc.isCompact).image ((continuous_centralScalar.comp continuous_fst).inv.mul continuous_snd)
  refine HasCompactSupport.intro hSc fun g hg => ?_
  have himg : (fun z₀ : (AdeleRing (𝓞 K) K)ˣ => ‖f (centralScalar (𝓞 K) K z₀ * g)‖) '' Z₀ ⊆ {0} := by
    rintro _ ⟨z₀, hz₀, rfl⟩
    rw [Set.mem_singleton_iff, norm_eq_zero]
    by_contra hne
    refine hg ⟨(z₀, centralScalar (𝓞 K) K z₀ * g), ⟨hz₀, subset_tsupport _ hne⟩, ?_⟩
    show (centralScalar (𝓞 K) K z₀)⁻¹ * (centralScalar (𝓞 K) K z₀ * g) = g
    rw [inv_mul_cancel_left]
  unfold supTest
  rcases (Set.subset_singleton_iff_eq.mp himg) with h | h
  · rw [h, Real.sSup_empty]
  · rw [h, csSup_singleton]

theorem cellSum_supTest_nonneg (𝒞 : Set (GL (Fin 2) K)) (f : AdelicGL2 (𝓞 K) K → ℂ)
    (Z₀ : Set (AdeleRing (𝓞 K) K)ˣ) (x : AdelicGL2 (𝓞 K) K) : 0 ≤ cellSum 𝒞 (supTest f Z₀) x x :=
  finsum_nonneg fun _ => finsum_nonneg fun _ => supTest_nonneg _ _ _

theorem cellSum_ofReal (𝒞 : Set (GL (Fin 2) K)) {H : AdelicGL2 (𝓞 K) K → ℝ} (hHc : HasCompactSupport H)
    (x : AdelicGL2 (𝓞 K) K) :
    cellSum 𝒞 (fun g => (H g : ℂ)) x x = ((cellSum 𝒞 H x x : ℝ) : ℂ) := by
  unfold cellSum
  have hfin : (𝒞 ∩ Function.support fun γ : GL (Fin 2) K => H (x⁻¹ * globalPoints (𝓞 K) K γ * x)).Finite := by
    refine (finite_conj_mem hHc.isCompact x x).subset ?_
    rintro γ ⟨_, hγ⟩
    exact subset_tsupport _ hγ
  exact (AddMonoidHom.map_finsum_mem' (Complex.ofRealHom : ℝ →+* ℂ).toAddMonoidHom hfin).symm

theorem norm_cellSum_fold_le (𝒞 : Set (GL (Fin 2) K)) {f : AdelicGL2 (𝓞 K) K → ℂ} (hf : Continuous f)
    (hfc : HasCompactSupport f) {Z₀ : Set (AdeleRing (𝓞 K) K)ˣ} (hZ₀ : IsCompact Z₀)
    {z₀ : (AdeleRing (𝓞 K) K)ˣ} (hz₀ : z₀ ∈ Z₀) (x : AdelicGL2 (𝓞 K) K) :
    ‖cellSum 𝒞 f x (centralScalar (𝓞 K) K z₀ * x)‖ ≤ cellSum 𝒞 (supTest f Z₀) x x := by
  classical
  have hT₁ := finite_conj_mem hfc.isCompact x (centralScalar (𝓞 K) K z₀ * x)
  have hT₂ := finite_conj_mem (hasCompactSupport_supTest hfc hZ₀).isCompact x x
  set T : Finset (GL (Fin 2) K) := (hT₁.union hT₂).toFinset.filter (· ∈ 𝒞) with hTdef
  have hT : (T : Set (GL (Fin 2) K)) ⊆ 𝒞 := by
    intro γ hγ; rw [hTdef, Finset.coe_filter] at hγ; exact hγ.2
  rw [cellSum_eq_sum f x _ hT, cellSum_eq_sum (supTest f Z₀) x x hT]
  · refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun γ _ => ?_)
    rw [conj_centralScalar_mul]
    exact norm_le_supTest hf hZ₀ hz₀ _
  · intro γ hγ hne
    rw [hTdef, Finset.mem_filter, Set.Finite.mem_toFinset]
    exact ⟨Or.inr (subset_tsupport _ hne), hγ⟩
  · intro γ hγ hne
    rw [hTdef, Finset.mem_filter, Set.Finite.mem_toFinset]
    exact ⟨Or.inl (subset_tsupport _ hne), hγ⟩

theorem exists_band_of_isCompact {D : Set ℝ} (hD : IsCompact D) (hpos : ∀ d ∈ D, 0 < d) :
    ∃ a b : ℝ, 0 < a ∧ ∀ d ∈ D, ∀ r : ℝ, 0 ≤ r → r ^ 2 = d → r ∈ Set.Icc a b := by
  rcases D.eq_empty_or_nonempty with rfl | hne
  · exact ⟨1, 1, one_pos, fun d hd => absurd hd (Set.notMem_empty d)⟩
  refine ⟨Real.sqrt (sInf D), Real.sqrt (sSup D), Real.sqrt_pos.mpr (hpos _ (hD.sInf_mem hne)), ?_⟩
  intro d hd r hr hrd
  have hr' : r = Real.sqrt d := by rw [← hrd, Real.sqrt_sq hr]
  rw [hr']
  exact ⟨Real.sqrt_le_sqrt (csInf_le hD.bddBelow hd), Real.sqrt_le_sqrt (le_csSup hD.bddAbove hd)⟩

theorem cell_main (𝒞 : Set (GL (Fin 2) K)) (h𝒞 : ScalarStable 𝒞) (Φ : Set (AdelicGL2 (𝓞 K) K))
    [MeasurableSpace (AdeleRing (𝓞 K) K)ˣ] [BorelSpace (AdeleRing (𝓞 K) K)ˣ]
    (ν : Measure (AdeleRing (𝓞 K) K)ˣ) [ν.IsHaarMeasure] (Ω : Set (AdeleRing (𝓞 K) K)ˣ)
    (hΩ : IsFundamentalDomain (M4aHerbrand.principalIdeles (𝓞 K) K) Ω ν)
    (ξ : (⊤ : Subgroup (AdeleRing (𝓞 K) K)ˣ) →* ℂˣ)
    (hξc : Continuous fun z : (AdeleRing (𝓞 K) K)ˣ => ((ξ ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ))
    (hξt : ∀ z : (AdeleRing (𝓞 K) K)ˣ, z ∈ M4aHerbrand.principalIdeles (𝓞 K) K →
      ξ ⟨z, Subgroup.mem_top z⟩ = 1)
    (f : AdelicGL2 (𝓞 K) K → ℂ) (hf : Continuous f) (hfc : HasCompactSupport f)
    (hint : ∀ H : AdelicGL2 (𝓞 K) K → ℂ, Continuous H → HasCompactSupport H →
      IntegrableOn (fun x => cellSum 𝒞 H x x) Φ (adelicGLHaar (Fin 2) (𝓞 K) K)) :
    (∀ x : AdelicGL2 (𝓞 K) K, IntegrableOn (fun z : (AdeleRing (𝓞 K) K)ˣ =>
        ((ξ ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ) * cellSum 𝒞 f x (centralScalar (𝓞 K) K z * x)) Ω ν) ∧
    IntegrableOn (fun x : AdelicGL2 (𝓞 K) K => ∫ z in Ω,
        ((ξ ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ) * cellSum 𝒞 f x (centralScalar (𝓞 K) K z * x) ∂ν)
      Φ (adelicGLHaar (Fin 2) (𝓞 K) K) := by
  set μ := adelicGLHaar (Fin 2) (𝓞 K) K with hμ
  set ξ' : (AdeleRing (𝓞 K) K)ˣ → ℂ := fun z => ((ξ ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ) with hξ'

  set D : Set ℝ := (fun g : AdelicGL2 (𝓞 K) K => ideleNorm K (Matrix.GeneralLinearGroup.det g)) '' tsupport f
  have hD : IsCompact D := hfc.isCompact.image continuous_ideleNorm_det
  obtain ⟨a, b, ha, hab⟩ := exists_band_of_isCompact hD (by
    rintro _ ⟨g, _, rfl⟩; exact ideleNorm_pos _)
  set B : Set (AdeleRing (𝓞 K) K)ˣ := {z | ideleNorm K z ∈ Set.Icc a b} with hB
  have hBm : MeasurableSet B :=
    measurableSet_preimage (NumberField.TateGlobal.continuous_ideleNorm K).measurable measurableSet_Icc
  have hsuppB : ∀ (x : AdelicGL2 (𝓞 K) K) (γ : GL (Fin 2) K) (z : (AdeleRing (𝓞 K) K)ˣ),
      f (x⁻¹ * globalPoints (𝓞 K) K γ * (centralScalar (𝓞 K) K z * x)) ≠ 0 → z ∈ B := by
    intro x γ z hne
    refine hab _ ⟨_, subset_tsupport _ hne, rfl⟩ (ideleNorm K z) (ideleNorm_pos z).le ?_
    exact (ideleNorm_det_conj x γ z).symm

  obtain ⟨Z₀, hZ₀, hrepr⟩ := exists_isCompact_band_repr (K := K) (b := b) ha
  have hνB : ν (Ω ∩ B) < ∞ := measure_inter_lt_top_of_repr ν hΩ hZ₀ fun z hz => hrepr z hz

  set Mξ : ℝ := sSup ((fun z => ‖ξ' z‖) '' Z₀) with hMξ
  have hξle : ∀ z₀ ∈ Z₀, ‖ξ' z₀‖ ≤ Mξ := fun z₀ hz₀ =>
    le_csSup (hZ₀.bddAbove_image hξc.norm.continuousOn) (Set.mem_image_of_mem _ hz₀)

  set H : AdelicGL2 (𝓞 K) K → ℝ := supTest f Z₀ with hHdef
  have hHc : Continuous H := continuous_supTest hf hZ₀
  have hHs : HasCompactSupport H := hasCompactSupport_supTest hfc hZ₀
  set E : AdelicGL2 (𝓞 K) K → ℝ := fun x => cellSum 𝒞 H x x with hEdef
  have hEc : Continuous E := continuous_cellSum_diag 𝒞 H hHc hHs
  have hE0 : ∀ x, 0 ≤ E x := fun x => cellSum_supTest_nonneg 𝒞 f Z₀ x
  have hEint : ∫⁻ x in Φ, ENNReal.ofReal (E x) ∂μ < ∞ := by
    have hi := hint (fun g => (H g : ℂ)) (Complex.continuous_ofReal.comp hHc)
      (hHs.comp_left Complex.ofReal_zero)
    have hfi := hi.hasFiniteIntegral
    rw [hasFiniteIntegral_iff_enorm] at hfi
    refine lt_of_le_of_lt (lintegral_mono fun x => ?_) hfi
    show ENNReal.ofReal (E x) ≤ ‖cellSum 𝒞 (fun g => (H g : ℂ)) x x‖ₑ
    rw [cellSum_ofReal 𝒞 hHs, ← ofReal_norm, Complex.norm_real, Real.norm_of_nonneg (hE0 x)]

  set I : AdelicGL2 (𝓞 K) K × (AdeleRing (𝓞 K) K)ˣ → ℂ :=
    fun p => ξ' p.2 * cellSum 𝒞 f p.1 (centralScalar (𝓞 K) K p.2 * p.1) with hIdef
  have hIc : Continuous I :=
    (hξc.comp continuous_snd).mul (continuous_cellSum_fold 𝒞 f hf hfc)
  have hbound : ∀ (x : AdelicGL2 (𝓞 K) K) (z : (AdeleRing (𝓞 K) K)ˣ),
      ‖I (x, z)‖ₑ ≤ ENNReal.ofReal Mξ * (ENNReal.ofReal (E x) * B.indicator 1 z) := by
    intro x z
    by_cases hz : z ∈ B
    · obtain ⟨l, hl, z₀, hz₀, rfl⟩ := hrepr z hz
      rw [Set.indicator_of_mem hz, Pi.one_apply, mul_one]
      show ‖ξ' (l * z₀) * cellSum 𝒞 f x (centralScalar (𝓞 K) K (l * z₀) * x)‖ₑ ≤ _
      rw [cellSum_fold_principal_mul h𝒞 f x hl z₀, hξ']
      dsimp only
      rw [xi_principal_mul ξ hξt hl z₀, enorm_mul, ← ofReal_norm, ← ofReal_norm]
      exact mul_le_mul' (ENNReal.ofReal_le_ofReal (hξle z₀ hz₀))
        (ENNReal.ofReal_le_ofReal (norm_cellSum_fold_le 𝒞 hf hfc hZ₀ hz₀ x))
    · have h0 : cellSum 𝒞 f x (centralScalar (𝓞 K) K z * x) = 0 := by
        unfold cellSum
        refine finsum_mem_eq_zero_of_forall_eq_zero fun γ _ => ?_
        by_contra hne
        exact hz (hsuppB x γ z hne)
      show ‖ξ' z * cellSum 𝒞 f x (centralScalar (𝓞 K) K z * x)‖ₑ ≤ _
      rw [h0, mul_zero, enorm_zero]
      exact zero_le

  have h1 : ∀ x : AdelicGL2 (𝓞 K) K, IntegrableOn (fun z => I (x, z)) Ω ν := by
    intro x
    refine ⟨(hIc.comp (Continuous.prodMk_right x)).aestronglyMeasurable, ?_⟩
    rw [hasFiniteIntegral_iff_enorm]
    calc ∫⁻ z in Ω, ‖I (x, z)‖ₑ ∂ν
        ≤ ∫⁻ z in Ω, ENNReal.ofReal Mξ * (ENNReal.ofReal (E x) * B.indicator 1 z) ∂ν :=
          lintegral_mono fun z => hbound x z
      _ = ENNReal.ofReal Mξ * (ENNReal.ofReal (E x) * ν (B ∩ Ω)) := by
          rw [lintegral_const_mul _ ((measurable_one.indicator hBm).const_mul _),
            lintegral_const_mul _ (measurable_one.indicator hBm), lintegral_indicator_one hBm,
            Measure.restrict_apply hBm]
      _ < ∞ := by
          rw [Set.inter_comm] at hνB
          exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top (ENNReal.mul_lt_top ENNReal.ofReal_lt_top hνB)

  have h2 : Integrable I ((μ.restrict Φ).prod (ν.restrict Ω)) := by
    refine ⟨hIc.aestronglyMeasurable, ?_⟩
    rw [hasFiniteIntegral_iff_enorm]
    calc ∫⁻ p, ‖I p‖ₑ ∂(μ.restrict Φ).prod (ν.restrict Ω)
        ≤ ∫⁻ p, ENNReal.ofReal Mξ * (ENNReal.ofReal (E p.1) * B.indicator 1 p.2)
            ∂(μ.restrict Φ).prod (ν.restrict Ω) := lintegral_mono fun p => hbound p.1 p.2
      _ = ENNReal.ofReal Mξ * ∫⁻ p, ENNReal.ofReal (E p.1) * B.indicator 1 p.2
            ∂(μ.restrict Φ).prod (ν.restrict Ω) := lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
      _ = ENNReal.ofReal Mξ * ((∫⁻ x in Φ, ENNReal.ofReal (E x) ∂μ) * ∫⁻ z in Ω, B.indicator 1 z ∂ν) := by
          congr 1
          exact lintegral_prod_mul (f := fun x => ENNReal.ofReal (E x)) (g := B.indicator 1)
            (hEc.measurable.ennreal_ofReal).aemeasurable (measurable_one.indicator hBm).aemeasurable
      _ = ENNReal.ofReal Mξ * ((∫⁻ x in Φ, ENNReal.ofReal (E x) ∂μ) * ν (B ∩ Ω)) := by
          rw [lintegral_indicator_one hBm, Measure.restrict_apply hBm]
      _ < ∞ := by
          rw [Set.inter_comm] at hνB
          exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top (ENNReal.mul_lt_top hEint hνB)
  exact ⟨h1, h2.integral_prod_left⟩

def slab (K : Type) [Field K] [NumberField K] (α β : ℝ) : Set (AdelicGL2 (𝓞 K) K) :=
  {g | ideleNorm K (Matrix.GeneralLinearGroup.det g) ∈ Set.Icc α β}

theorem measurableSet_slab (α β : ℝ) : MeasurableSet (slab K α β) :=
  measurableSet_preimage continuous_ideleNorm_det.measurable measurableSet_Icc

theorem globalPoints_comm_of_mem_centralCell {γ : GL (Fin 2) K} (hγ : γ ∈ centralCell K)
    (g : AdelicGL2 (𝓞 K) K) : globalPoints (𝓞 K) K γ * g = g * globalPoints (𝓞 K) K γ := by
  obtain ⟨c, hc⟩ := (mem_centralCell_iff.mp hγ)
  refine Units.ext ?_
  have hval : ((globalPoints (𝓞 K) K γ : AdelicGL2 (𝓞 K) K) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 K) K)) =
      Matrix.scalar (Fin 2) (algebraMap K (AdeleRing (𝓞 K) K) c) := by
    show (algebraMap K (AdeleRing (𝓞 K) K)).mapMatrix ((γ : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) = _
    rw [hc]
    ext i j
    simp only [RingHom.mapMatrix_apply, Matrix.map_apply, Matrix.smul_apply, Matrix.scalar_apply,
      Matrix.diagonal_apply, Matrix.one_apply, smul_eq_mul, mul_ite, mul_one, mul_zero]
    split_ifs <;> simp
  rw [Units.val_mul, Units.val_mul, hval]
  exact (Matrix.scalar_commute (n := Fin 2) _ (fun r' => Commute.all _ r') _).eq

theorem conj_globalPoints_of_mem_centralCell {γ : GL (Fin 2) K} (hγ : γ ∈ centralCell K)
    (x : AdelicGL2 (𝓞 K) K) : x⁻¹ * globalPoints (𝓞 K) K γ * x = globalPoints (𝓞 K) K γ := by
  rw [mul_assoc, (globalPoints_comm_of_mem_centralCell hγ x), inv_mul_cancel_left]

theorem integrableOn_cellSum_centralCell {α β : ℝ} (hα : 0 < α) (hαβ : α < β)
    (Φ : Set (AdelicGL2 (𝓞 K) K)) (hΦs : Φ ⊆ slab K α β)
    (hΦ : IsFundamentalDomain (globalPoints (𝓞 K) K).range Φ
      ((adelicGLHaar (Fin 2) (𝓞 K) K).restrict (slab K α β)))
    (H : AdelicGL2 (𝓞 K) K → ℂ) :
    IntegrableOn (fun x => cellSum (centralCell K) H x x) Φ (adelicGLHaar (Fin 2) (𝓞 K) K) := by
  have hconst : (fun x => cellSum (centralCell K) H x x) = fun _ => cellSum (centralCell K) H 1 1 := by
    funext x
    unfold cellSum
    refine finsum_mem_congr rfl fun γ hγ => ?_
    rw [conj_globalPoints_of_mem_centralCell hγ, conj_globalPoints_of_mem_centralCell hγ]
  rw [hconst]
  have hvol := AutomorphicForm.adelicGLHaar_inter_setOf_ideleNorm_det_mem_Icc_lt_top_of_isFundamentalDomain
    K α β hα hαβ Φ hΦ
  change adelicGLHaar (Fin 2) (𝓞 K) K (Φ ∩ slab K α β) < ⊤ at hvol
  rw [Set.inter_eq_left.mpr hΦs] at hvol
  exact integrableOn_const hvol.ne

theorem integrableOn_cellSum_ellipticCell {α β : ℝ} (hα : 0 < α) (hαβ : α < β)
    (Φ : Set (AdelicGL2 (𝓞 K) K)) (hΦs : Φ ⊆ slab K α β)
    (hΦ : IsFundamentalDomain (globalPoints (𝓞 K) K).range Φ
      ((adelicGLHaar (Fin 2) (𝓞 K) K).restrict (slab K α β)))
    (H : AdelicGL2 (𝓞 K) K → ℂ) (hH : Continuous H) (hHc : HasCompactSupport H) :
    IntegrableOn (fun x => cellSum (ellipticCell K) H x x) Φ (adelicGLHaar (Fin 2) (𝓞 K) K) := by
  have h := AutomorphicForm.integrableOn_adelicKernelEllipticPart_diag_of_isFundamentalDomain_slab
    K α β hα hαβ Φ hΦ H hH hHc
  change IntegrableOn (fun x => cellSum (ellipticCell K) H x x) Φ
    ((adelicGLHaar (Fin 2) (𝓞 K) K).restrict (slab K α β)) at h
  rw [IntegrableOn, Measure.restrict_restrict' (measurableSet_slab α β), Set.inter_eq_left.mpr hΦs] at h
  exact h

theorem main (α β : ℝ) (hα : 0 < α) (hαβ : α < β)
    (ΦK : Set (AdelicGL2 (𝓞 K) K))
    (hΦKs : ΦK ⊆
      {g | NumberField.TateGlobal.ideleNorm K (Matrix.GeneralLinearGroup.det g) ∈ Set.Icc α β})
    (hΦK : IsFundamentalDomain (AutomorphicForm.globalPoints (𝓞 K) K).range ΦK
      ((adelicGLHaar (Fin 2) (𝓞 K) K).restrict
        {g | NumberField.TateGlobal.ideleNorm K (Matrix.GeneralLinearGroup.det g) ∈ Set.Icc α β}))
    [MeasurableSpace (AdeleRing (𝓞 K) K)ˣ] [BorelSpace (AdeleRing (𝓞 K) K)ˣ]
    (νZK : Measure (AdeleRing (𝓞 K) K)ˣ) [νZK.IsHaarMeasure] (ΩK : Set (AdeleRing (𝓞 K) K)ˣ)
    (hΩK : IsFundamentalDomain
      (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K)).range ΩK νZK)
    (ξK : (⊤ : Subgroup (AdeleRing (𝓞 K) K)ˣ) →* ℂˣ)
    (hξc : Continuous fun z : (AdeleRing (𝓞 K) K)ˣ => ((ξK ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ))
    (hξt : ∀ z : (AdeleRing (𝓞 K) K)ˣ,
      z ∈ (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K)).range →
        ξK ⟨z, Subgroup.mem_top z⟩ = 1)
    (f : AdelicGL2 (𝓞 K) K → ℂ) (hf : Continuous f) (hfc : HasCompactSupport f) :
    (∀ x : AdelicGL2 (𝓞 K) K, IntegrableOn (fun z : (AdeleRing (𝓞 K) K)ˣ =>
        ((ξK ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ) *
          (AutomorphicForm.adelicKernelCentralPart K f x (AutomorphicForm.centralScalar (𝓞 K) K z * x) +
            AutomorphicForm.adelicKernelEllipticPart K f x (AutomorphicForm.centralScalar (𝓞 K) K z * x)))
      ΩK νZK) ∧
    IntegrableOn (fun x : AdelicGL2 (𝓞 K) K => ∫ z in ΩK,
        ((ξK ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ) *
          (AutomorphicForm.adelicKernelCentralPart K f x (AutomorphicForm.centralScalar (𝓞 K) K z * x) +
            AutomorphicForm.adelicKernelEllipticPart K f x (AutomorphicForm.centralScalar (𝓞 K) K z * x))
      ∂νZK) ΦK (adelicGLHaar (Fin 2) (𝓞 K) K) := by
  have hc := cell_main (centralCell K) scalarStable_centralCell ΦK νZK ΩK hΩK ξK hξc hξt f hf hfc
    (fun H _ _ => integrableOn_cellSum_centralCell hα hαβ ΦK hΦKs hΦK H)
  have he := cell_main (ellipticCell K) scalarStable_ellipticCell ΦK νZK ΩK hΩK ξK hξc hξt f hf hfc
    (fun H hH hHc => integrableOn_cellSum_ellipticCell hα hαβ ΦK hΦKs hΦK H hH hHc)
  refine ⟨fun x => ?_, ?_⟩
  · have heq : (fun z : (AdeleRing (𝓞 K) K)ˣ => ((ξK ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ) *
          (adelicKernelCentralPart K f x (centralScalar (𝓞 K) K z * x) +
            adelicKernelEllipticPart K f x (centralScalar (𝓞 K) K z * x))) =
        (fun z => ((ξK ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ) *
            cellSum (centralCell K) f x (centralScalar (𝓞 K) K z * x)) +
          fun z => ((ξK ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ) *
            cellSum (ellipticCell K) f x (centralScalar (𝓞 K) K z * x) := by
      funext z
      rw [Pi.add_apply, mul_add]
      rfl
    rw [heq]
    exact (hc.1 x).add (he.1 x)
  · have heq : (fun x : AdelicGL2 (𝓞 K) K => ∫ z in ΩK, ((ξK ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ) *
          (adelicKernelCentralPart K f x (centralScalar (𝓞 K) K z * x) +
            adelicKernelEllipticPart K f x (centralScalar (𝓞 K) K z * x)) ∂νZK) =
        (fun x => ∫ z in ΩK, ((ξK ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ) *
            cellSum (centralCell K) f x (centralScalar (𝓞 K) K z * x) ∂νZK) +
          fun x => ∫ z in ΩK, ((ξK ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ) *
            cellSum (ellipticCell K) f x (centralScalar (𝓞 K) K z * x) ∂νZK := by
      funext x
      rw [Pi.add_apply, ← integral_add (hc.1 x) (he.1 x)]
      congr 1
      funext z
      rw [mul_add]
      rfl
    rw [heq]
    exact hc.2.add he.2

end R1CentEllFold
p2m_reactivate "P2MW.S_AutomorphicForm_integrableOn_setIntegral_mul_centralElliptic_adelicKernel_of_isFundamentalDomain_slab.R1CentEllFold"

attribute [local instance] NumberField.AdelicHaar.glBorel

theorem solution
    (K : Type) [Field K] [NumberField K]
    (α β : ℝ) (hα : 0 < α) (hαβ : α < β)
    (ΦK : Set (AdelicGL2 (𝓞 K) K))
    (hΦKs : ΦK ⊆
      {g | NumberField.TateGlobal.ideleNorm K (Matrix.GeneralLinearGroup.det g) ∈ Set.Icc α β})
    (hΦK : IsFundamentalDomain (AutomorphicForm.globalPoints (𝓞 K) K).range ΦK
      ((adelicGLHaar (Fin 2) (𝓞 K) K).restrict
        {g | NumberField.TateGlobal.ideleNorm K (Matrix.GeneralLinearGroup.det g) ∈ Set.Icc α β}))
    [MeasurableSpace (AdeleRing (𝓞 K) K)ˣ] [BorelSpace (AdeleRing (𝓞 K) K)ˣ]
    (νZK : Measure (AdeleRing (𝓞 K) K)ˣ) [νZK.IsHaarMeasure] (ΩK : Set (AdeleRing (𝓞 K) K)ˣ)
    (hΩK : IsFundamentalDomain
      (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K)).range ΩK νZK)
    (ξK : (⊤ : Subgroup (AdeleRing (𝓞 K) K)ˣ) →* ℂˣ)
    (hξc : Continuous fun z : (AdeleRing (𝓞 K) K)ˣ => ((ξK ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ))
    (hξt : ∀ z : (AdeleRing (𝓞 K) K)ˣ,
      z ∈ (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K)).range →
        ξK ⟨z, Subgroup.mem_top z⟩ = 1)
    (f : AdelicGL2 (𝓞 K) K → ℂ) (hf : Continuous f) (hfc : HasCompactSupport f) :
    (∀ x : AdelicGL2 (𝓞 K) K, IntegrableOn (fun z : (AdeleRing (𝓞 K) K)ˣ =>
        ((ξK ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ) *
          (AutomorphicForm.adelicKernelCentralPart K f x (AutomorphicForm.centralScalar (𝓞 K) K z * x) +
            AutomorphicForm.adelicKernelEllipticPart K f x (AutomorphicForm.centralScalar (𝓞 K) K z * x)))
      ΩK νZK) ∧
    IntegrableOn (fun x : AdelicGL2 (𝓞 K) K => ∫ z in ΩK,
        ((ξK ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ) *
          (AutomorphicForm.adelicKernelCentralPart K f x (AutomorphicForm.centralScalar (𝓞 K) K z * x) +
            AutomorphicForm.adelicKernelEllipticPart K f x (AutomorphicForm.centralScalar (𝓞 K) K z * x))
      ∂νZK) ΦK (adelicGLHaar (Fin 2) (𝓞 K) K) :=
  R1CentEllFold.main α β hα hαβ ΦK hΦKs hΦK νZK ΩK hΩK ξK hξc hξt f hf hfc

end
end S_AutomorphicForm_integrableOn_setIntegral_mul_centralElliptic_adelicKernel_of_isFundamentalDomain_slab
end P2MW
export P2MW.S_AutomorphicForm_integrableOn_setIntegral_mul_centralElliptic_adelicKernel_of_isFundamentalDomain_slab (solution)
