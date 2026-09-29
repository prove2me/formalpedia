-- Prove2me | solution 1 for AlgebraicCurve.exists_isUnit_det_evalAt_differentialCoeff
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:02.4153+00:00
-- url     : https://prove2.me/submissions/23dbbdb4-964c-5e84-ada5-e2c9a98c58ea

import Mathlib
import Definitions.Def_AlgebraicCurve_DivisorClassGroup
import Definitions.Def_AlgebraicCurve_IsCurveOver
import Definitions.Def_AlgebraicCurve_CanonicalDivisor
import Definitions.Def_AlgebraicCurve_PlaceEvaluation
import Definitions.Def_AlgebraicCurve_PlaceEvaluationAlgebra
import Definitions.Def_AlgebraicCurve_RegularDifferentials
import Definitions.Def_AlgebraicCurve_AdelicIndex
import Definitions.Def_AlgebraicCurve_RiemannRochRows
import Theorems.Thm_AlgebraicCurve_dCoordGenerates_of_isCurveOver
import Theorems.Thm_AlgebraicCurve_essFiniteType_of_transcendental_of_finiteDimensional
import Theorems.Thm_AlgebraicCurve_finite_and_finrank_regularDifferentials_eq_genus
import Theorems.Thm_AlgebraicCurve_functionFieldRiemannRoch_of_isAlgClosed_of_transcendental
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicCurve_exists_isUnit_det_evalAt_differentialCoeff
p2m_attr_erase "instance" "AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.instHasLocalResidue_of_hasCanonicalLocalResidueK AlgebraicCurve.instHasCanonicalLocalResidueK_of_hasCanonicalLocalResidueKStar AlgebraicCurve.instFundamentalIdentityOfSumRamificationInertia AlgebraicCurve.Place.instIsScalarTowerResidueFieldRestrictPushforward AlgebraicCurve.Place.instAlgebraResidueFieldRestrictPushforward AlgebraicCurve.Place.instIsLocalHomRestrictInclusion AlgebraicCurve.Place.kw_ffgc_finiteDimensional_adicCompletion instAlgebraSubtypeMemValuationSubring_definitions AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersIntegersCompletion ModularCurve.KwF4gRRTate.instAlgebraKAdicCompletionIntegers AlgebraicCurve.Place.kw_ffgc_continuousSMul_adicCompletionComap AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersCompletionCompletion IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions AlgebraicCurve.instHasCanonicalLocalResidueK AlgebraicCurve.Place.instAlgebra_restrictResidueField AlgebraicCurve.Place.instIsScalarTower_restrictResidueField AlgebraicCurve.instHasLocalResidue AlgebraicCurve.HasSeparableResidue.of_perfectField_of_isCurveOver AlgebraicCurve.HasSeparableResidue.of_perfectField AlgebraicCurve.Place.instIsLocalHom_restrictSubringHom AlgebraicCurve.instHasCanonicalLocalResidueKStar ModularCurve.KwNo6Pin.isLocalRing_completion AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.SemilinearAut.instDistribMulActionSubtypeProdRingAutMemSubgroupPic0 AlgebraicCurve.SemilinearAut.instDistribMulActionSubtypeProdRingAutMemSubgroupDivisor AlgebraicCurve.Pic0.instModuleZModTorsion AlgebraicCurve.SemilinearAut.instSMulSubtypeProdRingAutMemSubgroupPlace AlgebraicCurve.SemilinearAut.instDistribMulActionTorsion"
p2m_attr_erase "instance" "AlgebraicCurve.SemilinearAut.instSMulSubtypeProdRingAutMemSubgroupPic0 AlgebraicCurve.SemilinearAut.instSMulTorsion AlgebraicCurve.SemilinearAut.instMulActionSubtypeProdRingAutMemSubgroupPlace AlgebraicCurve.SemilinearAut.instSMulCommClassZModTorsion AlgebraicCurve.SemilinearAut.instMulSemiringActionSubtypeProdRingAutMemSubgroup instDecEqAlgebraicClosureRat WeierstrassCurve.Affine.Point.instDistribMulActionAlgEquiv WeierstrassCurve.Affine.Point.instModuleZModTorsionBy WeierstrassCurve.Affine.Point.instSMulTorsionBy WeierstrassCurve.Affine.Point.instDistribMulActionTorsionBy WeierstrassCurve.Affine.Point.instSMulAlgEquiv WeierstrassCurve.Affine.Point.instSMulCommClassAlgEquivZModTorsionBy"
p2m_attr_erase "simp" "AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none AlgebraicCurve.Place.congrEquiv_symm_apply AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply AlgebraicCurve.RationalFunctionField.deg_placeOfPoint AlgebraicCurve.RationalFunctionField.placeInfty_toValuationSubring AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.sizeOf_spec AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.injEq AlgebraicCurve.adeleSingle_coe AlgebraicCurve.kaehlerResidueTermKFam_apply AlgebraicCurve.Place.LocalResidueData.mk.injEq AlgebraicCurve.Place.LocalResidueData.mk.sizeOf_spec AlgebraicCurve.Divisor.mapRestrict_single AlgebraicCurve.Divisor.pushforward_single AlgebraicCurve.Place.coe_restrictInclusion AlgebraicCurve.Place.mem_fiber AlgebraicCurve.Place.restrict_toValuationSubring AlgebraicCurve.Divisor.degree_pushforward AlgebraicCurve.Place.restrictResidueMap_residue AlgebraicCurve.Pic0.coe_pushforwardDegZeroHom AlgebraicCurve.Pic0.coe_pullbackDegZeroHom AlgebraicCurve.Place.kw_ffgc_adicCompletionComapIntegers_coe AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.sizeOf_spec AlgebraicCurve.Place.mem_simplePoleSubmodule AlgebraicCurve.Place.coe_uniformizerSubring ModularCurve.Lg37.Lg37CompletionSection.mk.injEq AlgebraicCurve.Place.CoefficientFieldSection.mk.injEq AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.injEq ModularCurve.Lg37.Lg37CompletionSection.mk.sizeOf_spec AlgebraicCurve.Place.CoefficientFieldSection.mk.sizeOf_spec AlgebraicCurve.Place.poleSubmodule_one AlgebraicCurve.Place.mem_poleSubmodule AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply"
p2m_attr_erase "simp" "AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal AlgebraicCurve.IsFrobeniusEndo.frobNormRingHom_apply ModularCurve.frobeniusPushforwardGeomLevelPic0_mk ModularCurve.coe_frobeniusGeomLevelEquiv_apply ModularCurve.coe_frobeniusPushforwardGeomLevelDegZero ModularCurve.heckeFibreGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusGeomLevel_apply_coe ModularCurve.frobeniusPullbackGeomLevelPic0OfIsCurveOver_mk ModularCurve.coe_heckeFibreGeomLevelDegZero ModularCurve.coe_frobeniusPullbackGeomLevelDegZero ModularCurve.frobeniusPullbackGeomLevelPic0_mk ModularCurve.frobeniusPullbackGeomLevel_single ModularCurve.heckeFibreGeomLevelPic0_mk ModularCurve.frobeniusPushforwardGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusPushforwardGeomLevel_single ModularCurve.qExpandAlgC_apply AlgebraicCurve.Divisor.degree_pushforwardAlong AlgebraicCurve.Pic0.coe_degZeroCorrespondence AlgebraicCurve.Place.mem_fiberAlong AlgebraicCurve.SemilinearAut.toRingAut_inv AlgebraicCurve.SemilinearAut.smul_def AlgebraicCurve.SemilinearAut.smul_single AlgebraicCurve.SemilinearAut.smul_toValuationSubring AlgebraicCurve.SemilinearAut.baseAut_inv AlgebraicCurve.SemilinearAut.baseAut_ofAlgAut AlgebraicCurve.SemilinearAut.toRingAut_ofAlgAut AlgebraicCurve.SemilinearAut.torsionRep_apply AlgebraicCurve.SemilinearAut.toRingAut_one AlgebraicCurve.SemilinearAut.deg_smul AlgebraicCurve.SemilinearAut.degree_smul AlgebraicCurve.SemilinearAut.coe_degZeroSMulHom AlgebraicCurve.SemilinearAut.baseAut_mul AlgebraicCurve.SemilinearAut.coe_smulValuationSubringEquiv_apply AlgebraicCurve.SemilinearAut.baseAut_one AlgebraicCurve.SemilinearAut.ofAlgAut_smul AlgebraicCurve.SemilinearAut.coe_torsion_smul AlgebraicCurve.SemilinearAut.toRingAut_mul AlgebraicCurve.coe_frobeniusPushforwardDegZero AlgebraicCurve.IsFrobeniusEndo.coe_frobeniusPullbackDegZero"
p2m_attr_erase "simp" "ModularCurve.jqNModC_one ModularCurve.qExpand_coeff_mul ModularCurve.qExpandₐ_apply ModularCurve.jqN_one ModularCurve.qExpand_single ModularCurve.dedekindPsi_one ModularCurve.ModularPolynomialData.mk.sizeOf_spec ModularCurve.evalAtJ_X ModularCurve.ModularPolynomialData.mk.injEq ModularCurve.constantCoeff_jNum ModularCurve.constantCoeff_eisenstein4 ModularCurve.qExpand_C ModularCurve.coeff_jq_neg_one ModularCurve.constantCoeff_jNumQ ModularCurve.reduceModBivar_C_X ModularCurve.laurentMap_coeff ModularCurve.reduceModBivar_X ModularCurve.laurentMap_single ModularCurve.evalAtJInt_X ModularCurve.evalAtJMod_X ModularCurve.jqNMod_one ModularCurve.aeval_heckeGen ModularCurve.coe_mTorsionGaloisRep_apply ModularCurve.eisensteinSystem_of_dvd ModularCurve.eisensteinSystem_of_not_dvd FreyPackage.mk.sizeOf_spec FreyPackage.mk.injEq WeierstrassCurve.Affine.Point.galoisRepModuleEnd_apply"

set_option autoImplicit false
set_option linter.unusedSectionVars false

noncomputable section

p2m_open "AlgebraicCurve P2MW.S_AlgebraicCurve_exists_isUnit_det_evalAt_differentialCoeff.AlgebraicCurve Module"

namespace AlgebraicCurve
p2m_export "AlgebraicCurve" "Place Place.FiniteResidue Place.ord_inv Divisor Divisor.degree Divisor.degree_single Place.FiniteResidue.finite IsCurveOver IsCurveOver.finrank_kaehler IsCurveOver.deg_eq_one_of_isAlgClosed HasCanonicalDivisor canonicalDivisorOf canonicalDivisorOf_apply genus Place.ordDifferential regularDifferentials LSpace ell mem_lSpace_iff_ord lSpace_mono one_mem_lSpace_zero FunctionFieldRiemannRoch dCoordGenerates_of_isCurveOver essFiniteType_of_transcendental_of_finiteDimensional finite_and_finrank_regularDifferentials_eq_genus functionFieldRiemannRoch_of_isAlgClosed_of_transcendental"
namespace GeneralPositionProof
p2m_open "AlgebraicCurve"

section Algebra

variable {K F : Type*} [Field K] [Field F] [Algebra K F]

theorem ord_pos_of_not_isUnit (v : Place K F) {a : v.toValuationSubring} (ha : a ≠ 0)
    (hu : ¬IsUnit a) : 0 < v.ord (a : F) := by
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible v.toValuationSubring
  obtain ⟨n, u, rfl⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible ha hπ
  have hn : n ≠ 0 := by
    rintro rfl
    exact hu (by rw [pow_zero, mul_one]; exact u.isUnit)
  have hcoe : (((u : v.toValuationSubring) * π ^ n : v.toValuationSubring) : F) =
      ((u : v.toValuationSubring) : F) * (π : F) ^ (n : ℤ) := by
    rw [zpow_natCast, Subring.coe_mul, SubmonoidClass.coe_pow]
  rw [hcoe, v.ord_unit_smul_zpow u hπ]
  exact_mod_cast Nat.pos_of_ne_zero hn

theorem ord_neg_of_not_mem (v : Place K F) {f : F} (hf : f ∉ v.toValuationSubring) :
    v.ord f < 0 := by
  have hf0 : f ≠ 0 := by
    rintro rfl
    exact hf (zero_mem _)
  have hinv : f⁻¹ ∈ v.toValuationSubring := (v.toValuationSubring.mem_or_inv_mem f).resolve_left hf
  have hu : ¬IsUnit (⟨f⁻¹, hinv⟩ : v.toValuationSubring) := by
    intro h
    obtain ⟨u, hu⟩ := h
    apply hf
    have : ((u⁻¹ : v.toValuationSubringˣ) : v.toValuationSubring).val = f := by
      have h1 : ((u⁻¹ : v.toValuationSubringˣ) : v.toValuationSubring).val * f⁻¹ = 1 := by
        have := congrArg (fun a : v.toValuationSubring => (a : F)) (u.inv_mul)
        simpa [hu] using this
      have := congrArg (· * f) h1
      simpa [inv_mul_cancel_right₀ hf0, mul_assoc, inv_mul_cancel₀ hf0] using this
    rw [← this]
    exact SetLike.coe_mem _
  have ha : (⟨f⁻¹, hinv⟩ : v.toValuationSubring) ≠ 0 := by
    intro h
    exact inv_ne_zero hf0 (by simpa using congrArg Subtype.val h)
  have := ord_pos_of_not_isUnit v ha hu
  rw [show ((⟨f⁻¹, hinv⟩ : v.toValuationSubring) : F) = f⁻¹ from rfl, v.ord_inv] at this
  omega

theorem mem_of_ord_nonneg (v : Place K F) {f : F} (h : 0 ≤ v.ord f) :
    f ∈ v.toValuationSubring := by
  by_contra hf
  exact absurd (ord_neg_of_not_mem v hf) (not_lt.2 h)

theorem ord_nonneg_of_mem (v : Place K F) {f : F} (hf : f ∈ v.toValuationSubring) :
    0 ≤ v.ord f := by
  by_cases hf0 : f = 0
  · simp [hf0]
  by_cases hu : IsUnit (⟨f, hf⟩ : v.toValuationSubring)
  · exact (v.ord_coe_unit hu.unit).symm.le
  · exact (ord_pos_of_not_isUnit v (fun h => hf0 (by simpa using congrArg Subtype.val h)) hu).le

theorem isUnit_algebraMap (v : Place K F) {c : K} (hc : c ≠ 0) :
    IsUnit (⟨algebraMap K F c, v.algebraMap_mem' c⟩ : v.toValuationSubring) := by
  refine ⟨⟨⟨algebraMap K F c, v.algebraMap_mem' c⟩, ⟨algebraMap K F c⁻¹, v.algebraMap_mem' c⁻¹⟩,
    ?_, ?_⟩, rfl⟩
  · ext; simp [hc]
  · ext; simp [hc]

theorem ord_algebraMap (v : Place K F) (c : K) : v.ord (algebraMap K F c) = 0 := by
  rcases eq_or_ne c 0 with rfl | hc
  · simp
  exact v.ord_coe_unit (isUnit_algebraMap v hc).unit

theorem mem_maximalIdeal_of_ord_pos (v : Place K F) {f : F} (hf : f ∈ v.toValuationSubring)
    (h : 0 < v.ord f) :
    (⟨f, hf⟩ : v.toValuationSubring) ∈ IsLocalRing.maximalIdeal v.toValuationSubring := by
  rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
  intro hu
  have := v.ord_coe_unit hu.unit
  rw [IsUnit.unit_spec] at this
  change v.ord f = 0 at this
  omega

theorem isRational_of_isAlgClosed [IsAlgClosed K] (w : Place K F) [w.FiniteResidue] :
    w.IsRational := by
  haveI : Module.Finite K w.ResidueField := Place.FiniteResidue.finite
  haveI : Algebra.IsIntegral K w.ResidueField := Algebra.IsIntegral.of_finite K _
  exact (IsAlgClosed.algebraMap_bijective_of_isIntegral (k := K) (K := w.ResidueField)).2

theorem residue_algebraMap (w : Place K F) (a : K) :
    IsLocalRing.residue w.toValuationSubring
        (⟨algebraMap K F a, w.algebraMap_mem' a⟩ : w.toValuationSubring) =
      algebraMap K w.ResidueField a := by
  have h : (⟨algebraMap K F a, w.algebraMap_mem' a⟩ : w.toValuationSubring) =
      algebraMap K w.toValuationSubring a := Subtype.ext (w.coe_algebraMap a).symm
  rw [h]
  exact (IsScalarTower.algebraMap_apply K w.toValuationSubring w.ResidueField a).symm

theorem evalAt_algebraMap' (w : Place K F) (a : K) : w.evalAt (algebraMap K F a) = a := by
  rw [w.evalAt_of_mem (w.algebraMap_mem' a), residue_algebraMap, w.residueInv_algebraMap]

theorem evalAt_mul (w : Place K F) (hw : w.IsRational) {f g : F}
    (hf : f ∈ w.toValuationSubring) (hg : g ∈ w.toValuationSubring) :
    w.evalAt (f * g) = w.evalAt f * w.evalAt g := by
  apply w.algebraMap_residueField_injective
  rw [w.algebraMap_evalAt hw (mul_mem hf hg), map_mul, w.algebraMap_evalAt hw hf,
    w.algebraMap_evalAt hw hg, ← map_mul]
  rfl

theorem evalAt_add (w : Place K F) (hw : w.IsRational) {f g : F}
    (hf : f ∈ w.toValuationSubring) (hg : g ∈ w.toValuationSubring) :
    w.evalAt (f + g) = w.evalAt f + w.evalAt g := by
  apply w.algebraMap_residueField_injective
  rw [w.algebraMap_evalAt hw (add_mem hf hg), map_add, w.algebraMap_evalAt hw hf,
    w.algebraMap_evalAt hw hg, ← map_add]
  rfl

theorem ord_pos_of_evalAt_eq_zero (w : Place K F) (hw : w.IsRational) {f : F} (hf0 : f ≠ 0)
    (hf : f ∈ w.toValuationSubring) (h : w.evalAt f = 0) : 0 < w.ord f := by
  rcases (ord_nonneg_of_mem w hf).lt_or_eq with hlt | heq
  · exact hlt
  · exact absurd h (w.evalAt_ne_zero_of_ord_eq_zero hw hf0 heq.symm)

theorem evalAt_eq_zero_of_ord_pos (w : Place K F) {f : F} (hf : f ∈ w.toValuationSubring)
    (h : 0 < w.ord f) : w.evalAt f = 0 := by
  have hres : IsLocalRing.residue w.toValuationSubring (⟨f, hf⟩ : w.toValuationSubring) = 0 :=
    (IsLocalRing.residue_eq_zero_iff _).2 (mem_maximalIdeal_of_ord_pos w hf h)
  rw [w.evalAt_of_mem hf, hres, ← map_zero (algebraMap K w.ResidueField), w.residueInv_algebraMap]

theorem differentialCoeff_add (v : Place K F) [v.DCoordGenerates] [Nontrivial (Ω[F⁄K])]
    (θ θ' : Ω[F⁄K]) :
    v.differentialCoeff (θ + θ') = v.differentialCoeff θ + v.differentialCoeff θ' :=
  v.differentialCoeff_unique (by
    rw [add_smul, v.differentialCoeff_smul_dCoord, v.differentialCoeff_smul_dCoord])

theorem differentialCoeff_mem [Nontrivial (Ω[F⁄K])] {η : Ω[F⁄K]}
    (hη : η ∈ regularDifferentials K F) (v : Place K F) [v.DCoordGenerates] :
    v.differentialCoeff η ∈ v.toValuationSubring := by
  obtain ⟨f, hf, hfeq⟩ := hη v
  rw [v.differentialCoeff_unique hfeq]
  exact hf

theorem differentialCoeff_ne_zero (v : Place K F) [v.DCoordGenerates] {ω : Ω[F⁄K]} (hω : ω ≠ 0) :
    v.differentialCoeff ω ≠ 0 := by
  intro h
  apply hω
  rw [← v.differentialCoeff_smul_dCoord ω, h, zero_smul]

theorem mem_regularDifferentials_of_ord_nonneg [Nontrivial (Ω[F⁄K])]
    [∀ v : Place K F, v.DCoordGenerates] {η : Ω[F⁄K]}
    (h : ∀ v : Place K F, 0 ≤ v.ord (v.differentialCoeff η)) : η ∈ regularDifferentials K F :=
  fun v => ⟨v.differentialCoeff η, mem_of_ord_nonneg v (h v), (v.differentialCoeff_smul_dCoord η).symm⟩

end Algebra

section Curve

variable {K F : Type*} [Field K] [IsAlgClosed K] [Field F] [Algebra K F]
variable [IsCurveOver K F] [∀ v : Place K F, v.DCoordGenerates]

theorem isRational (w : Place K F) : w.IsRational := isRational_of_isAlgClosed w

def evalFunctional (v : Place K F) : ↥(regularDifferentials K F) →ₗ[K] K where
  toFun θ := v.evalAt (v.differentialCoeff (θ : Ω[F⁄K]))
  map_add' θ θ' := by
    rw [Submodule.coe_add, differentialCoeff_add, evalAt_add v (isRational v)
      (differentialCoeff_mem θ.2 v) (differentialCoeff_mem θ'.2 v)]
  map_smul' c θ := by
    rw [Submodule.coe_smul, RingHom.id_apply, ← algebraMap_smul (A := F) c (θ : Ω[F⁄K]),
      v.differentialCoeff_smul, evalAt_mul v (isRational v) (v.algebraMap_mem' c)
        (differentialCoeff_mem θ.2 v), evalAt_algebraMap', smul_eq_mul]

theorem evalFunctional_apply (v : Place K F) (θ : ↥(regularDifferentials K F)) :
    evalFunctional v θ = v.evalAt (v.differentialCoeff (θ : Ω[F⁄K])) := rfl

theorem eq_zero_of_forall_evalFunctional_eq_zero [HasCanonicalDivisor (K := K) (F := F)]
    [Infinite (Place K F)] (θ : ↥(regularDifferentials K F))
    (h : ∀ v : Place K F, evalFunctional v θ = 0) : θ = 0 := by
  by_contra hθ
  have hθ' : (θ : Ω[F⁄K]) ≠ 0 := fun h0 => hθ (Subtype.ext h0)

  have hpos : ∀ v : Place K F, 0 < v.ordDifferential (θ : Ω[F⁄K]) := fun v =>
    ord_pos_of_evalAt_eq_zero v (isRational v) (differentialCoeff_ne_zero v hθ')
      (differentialCoeff_mem θ.2 v) (h v)

  have hsub : (Set.univ : Set (Place K F)) ⊆ ↑(canonicalDivisorOf hθ').support := fun v _ => by
    rw [Finset.mem_coe, Finsupp.mem_support_iff, canonicalDivisorOf_apply]
    exact (hpos v).ne'
  exact Set.infinite_univ ((canonicalDivisorOf hθ').support.finite_toSet.subset hsub)

variable [HasCanonicalDivisor (K := K) (F := F)]

theorem smul_mem_of_mem_lSpace {ω : Ω[F⁄K]} (hω : ω ≠ 0) {D : Divisor K F} (hD : ∀ v, 0 ≤ D v)
    {f : F} (hf : f ∈ LSpace (canonicalDivisorOf hω - D)) (hf0 : f ≠ 0) :
    f • ω ∈ regularDifferentials K F ∧
      ∀ v : Place K F, D v ≤ v.ord (v.differentialCoeff (f • ω)) := by
  have hord : ∀ v : Place K F, D v ≤ v.ord (v.differentialCoeff (f • ω)) := by
    intro v
    rcases (mem_lSpace_iff_ord.1 hf) with h | h
    · exact absurd h hf0
    have hv := h v
    rw [Finsupp.sub_apply, canonicalDivisorOf_apply, Place.ordDifferential] at hv
    rw [v.differentialCoeff_smul, v.ord_mul hf0 (differentialCoeff_ne_zero v hω)]
    linarith
  exact ⟨mem_regularDifferentials_of_ord_nonneg fun v => (hD v).trans (hord v), hord⟩

theorem ell_canonicalDivisorOf_eq {ω : Ω[F⁄K]} (hω : ω ≠ 0) :
    ell (canonicalDivisorOf hω) = Module.finrank K ↥(regularDifferentials K F) := by

  have hmem : ∀ f : F, f ∈ LSpace (canonicalDivisorOf hω) → f • ω ∈ regularDifferentials K F := by
    intro f hf
    by_cases hf0 : f = 0
    · rw [hf0, zero_smul]; exact Submodule.zero_mem _
    have hf' : f ∈ LSpace (canonicalDivisorOf hω - 0) := by rwa [sub_zero]
    exact (smul_mem_of_mem_lSpace hω (D := 0) (fun _ => le_rfl) hf' hf0).1
  set T : ↥(LSpace (canonicalDivisorOf hω)) →ₗ[K] ↥(regularDifferentials K F) :=
    { toFun := fun f => ⟨(f : F) • ω, hmem f f.2⟩
      map_add' := fun f g => by ext; simp [add_smul]
      map_smul' := fun c f => by
        ext
        simp only [Submodule.coe_smul, RingHom.id_apply]
        rw [smul_assoc] } with hT
  have hTinj : Function.Injective T := by
    intro f g hfg
    have h := congrArg (fun θ : ↥(regularDifferentials K F) => (θ : Ω[F⁄K])) hfg
    simp only [hT, LinearMap.coe_mk, AddHom.coe_mk] at h
    have h' : ((f : F) - (g : F)) • ω = 0 := by rw [sub_smul, h, sub_self]
    rcases smul_eq_zero.1 h' with h'' | h''
    · exact Subtype.ext (sub_eq_zero.1 h'')
    · exact absurd h'' hω
  have hTsurj : Function.Surjective T := by
    intro η

    have hrank : Module.finrank F (Ω[F⁄K]) = 1 := IsCurveOver.finrank_kaehler
    obtain ⟨f, hf⟩ := (finrank_eq_one_iff_of_nonzero' ω hω).1 hrank (η : Ω[F⁄K])
    have hfL : f ∈ LSpace (canonicalDivisorOf hω) := by
      rw [mem_lSpace_iff_ord]
      by_cases hf0 : f = 0
      · exact Or.inl hf0
      refine Or.inr fun v => ?_
      rw [canonicalDivisorOf_apply, Place.ordDifferential]
      have hreg : 0 ≤ v.ord (v.differentialCoeff (η : Ω[F⁄K])) :=
        ord_nonneg_of_mem v (differentialCoeff_mem η.2 v)
      rw [← hf, v.differentialCoeff_smul, v.ord_mul hf0 (differentialCoeff_ne_zero v hω)] at hreg
      linarith
    exact ⟨⟨f, hfL⟩, Subtype.ext hf⟩
  exact (LinearEquiv.ofBijective T ⟨hTinj, hTsurj⟩).finrank_eq

theorem ell_zero_eq_one [Algebra.EssFiniteType K F] (hRR : FunctionFieldRiemannRoch K F) :
    ell (0 : Divisor K F) = 1 := by
  obtain ⟨ω, hω⟩ := exists_ne (0 : Ω[F⁄K])
  have h := hRR hω 0
  rw [sub_zero, ell_canonicalDivisorOf_eq hω,
    (finite_and_finrank_regularDifferentials_eq_genus (K := K) (F := F)).2, map_zero] at h
  have : (ell (0 : Divisor K F) : ℤ) = 1 := by linarith
  exact_mod_cast this

theorem exists_eq_algebraMap_of_ell_eq_one {D : Divisor K F} (hD : 0 ≤ D) (hell : ell D = 1)
    {f : F} (hf : f ∈ LSpace D) : ∃ c : K, f = algebraMap K F c := by
  have h1 : (1 : F) ∈ LSpace D := lSpace_mono hD one_mem_lSpace_zero
  have hne : (⟨1, h1⟩ : ↥(LSpace D)) ≠ 0 := by
    intro h; exact one_ne_zero (congrArg Subtype.val h)
  obtain ⟨c, hc⟩ := (finrank_eq_one_iff_of_nonzero' _ hne).1 hell ⟨f, hf⟩
  refine ⟨c, ?_⟩
  have := congrArg Subtype.val hc
  simp only [SetLike.mk_smul_mk] at this
  rw [← this, Algebra.smul_def, mul_one]

theorem exists_ord_neg_of_forall_ne (hell : ell (0 : Divisor K F) = 1) {f : F}
    (hf : ∀ c : K, f ≠ algebraMap K F c) : ∃ v : Place K F, v.ord f < 0 := by
  by_contra h
  push Not at h
  have hfL : f ∈ LSpace (0 : Divisor K F) := by
    rw [mem_lSpace_iff_ord]
    exact Or.inr fun v => by simpa using h v
  obtain ⟨c, hc⟩ := exists_eq_algebraMap_of_ell_eq_one le_rfl hell hfL
  exact hf c hc

theorem infinite_place (hell : ell (0 : Divisor K F) = 1) {x : F} (hx : Transcendental K x) :
    Infinite (Place K F) := by

  have hnc : ∀ c d : K, (x - algebraMap K F c)⁻¹ ≠ algebraMap K F d := by
    intro c d h
    apply hx
    have hx' : x = algebraMap K F (d⁻¹ + c) := by
      have h' : x - algebraMap K F c = algebraMap K F d⁻¹ := by
        rw [← inv_inv (x - algebraMap K F c), h, map_inv₀]
      rw [map_add, ← h', sub_add_cancel]
    rw [hx']
    exact isAlgebraic_algebraMap _
  choose w hw using fun c => exists_ord_neg_of_forall_ne hell (hnc c)
  have hpos : ∀ c, 0 < (w c).ord (x - algebraMap K F c) := fun c => by
    have := hw c
    rw [Place.ord_inv] at this
    omega
  refine Infinite.of_injective w fun c d hcd => ?_
  by_contra hne
  have hposd : 0 < (w c).ord (x - algebraMap K F d) := by rw [hcd]; exact hpos d
  have h1 := mem_maximalIdeal_of_ord_pos (w c) (mem_of_ord_nonneg _ (hpos c).le) (hpos c)
  have h2 := mem_maximalIdeal_of_ord_pos (w c) (mem_of_ord_nonneg _ hposd.le) hposd
  have h3 := Ideal.sub_mem _ h2 h1
  have heq : (⟨x - algebraMap K F d, mem_of_ord_nonneg _ hposd.le⟩ : (w c).toValuationSubring) -
      ⟨x - algebraMap K F c, mem_of_ord_nonneg _ (hpos c).le⟩ =
      ⟨algebraMap K F (c - d), (w c).algebraMap_mem' _⟩ := by
    ext
    simp only [AddSubgroupClass.coe_sub, map_sub]
    ring
  rw [heq, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff] at h3
  exact h3 (isUnit_algebraMap (w c) (sub_ne_zero.2 hne))

omit [∀ v : Place K F, v.DCoordGenerates] [HasCanonicalDivisor (K := K) (F := F)] in

theorem degree_sum_single {n : ℕ} (v : Fin n → Place K F) :
    Divisor.degree (∑ j, Finsupp.single (v j) (1 : ℤ) : Divisor K F) = n := by
  simp [map_sum, Divisor.degree_single, IsCurveOver.deg_eq_one_of_isAlgClosed]

theorem exists_isUnit_det [Infinite (Place K F)] {n : ℕ}
    (b : Module.Basis (Fin n) K ↥(regularDifferentials K F)) :
    ∃ v : Fin n → Place K F,
      IsUnit (Matrix.det (Matrix.of fun i j : Fin n => evalFunctional (v j) (b i))) := by
  classical
  set W := ↥(regularDifferentials K F)
  haveI : Module.Finite K W := Module.Finite.of_basis b
  set e : Place K F → Module.Dual K W := evalFunctional with he

  have hspan : Submodule.span K (Set.range e) = ⊤ := by
    by_contra hlt
    obtain ⟨φ, hφ0, hker⟩ :=
      Submodule.exists_le_ker_of_lt_top _ (lt_top_iff_ne_top.2 hlt)
    set θ : W := (Module.evalEquiv K W).symm φ with hθ
    have hθ0 : θ = 0 := by
      refine eq_zero_of_forall_evalFunctional_eq_zero θ fun v => ?_
      have h1 : e v ∈ LinearMap.ker φ := hker (Submodule.subset_span ⟨v, rfl⟩)
      rw [LinearMap.mem_ker] at h1
      rw [hθ, Module.apply_evalEquiv_symm_apply]
      exact h1
    apply hφ0
    have : φ = Module.evalEquiv K W θ := by rw [hθ, LinearEquiv.apply_symm_apply]
    rw [this, hθ0, map_zero]

  obtain ⟨t, ht, htspan, hli⟩ := exists_linearIndependent K (Set.range e)
  rw [hspan] at htspan
  set Bt : Module.Basis t K (Module.Dual K W) :=
    Module.Basis.mk hli (by rw [Subtype.range_coe, htspan]) with hBt
  set σ : t ≃ Fin n := Bt.indexEquiv b.dualBasis with hσ
  set Bt' : Module.Basis (Fin n) K (Module.Dual K W) := Bt.reindex σ with hBt'
  have hBt'mem : ∀ j, Bt' j ∈ Set.range e := fun j => by
    rw [hBt', Module.Basis.reindex_apply, hBt, Module.Basis.mk_apply]
    exact ht (σ.symm j).2
  choose v hv using hBt'mem
  refine ⟨v, ?_⟩

  have hmat : (Matrix.of fun i j : Fin n => evalFunctional (v j) (b i)) = b.dualBasis.toMatrix Bt' := by
    ext i j
    rw [Matrix.of_apply, Module.Basis.toMatrix_apply, Module.Basis.dualBasis_repr, ← hv j]
  rw [hmat, ← Matrix.isUnit_iff_isUnit_det]
  letI := b.dualBasis.invertibleToMatrix Bt'
  exact isUnit_of_invertible _

theorem injective_of_isUnit_det {n : ℕ} (b : Module.Basis (Fin n) K ↥(regularDifferentials K F))
    {v : Fin n → Place K F}
    (h : IsUnit (Matrix.det (Matrix.of fun i j : Fin n => evalFunctional (v j) (b i)))) :
    Function.Injective v := by
  intro j k hjk
  by_contra hne
  apply h.ne_zero
  rw [← Matrix.det_transpose]
  exact Matrix.det_zero_of_row_eq hne (funext fun i => by simp [Matrix.transpose_apply, hjk])

theorem lSpace_eq_bot_of_isUnit_det {n : ℕ} (b : Module.Basis (Fin n) K ↥(regularDifferentials K F))
    {v : Fin n → Place K F}
    (h : IsUnit (Matrix.det (Matrix.of fun i j : Fin n => evalFunctional (v j) (b i))))
    {ω : Ω[F⁄K]} (hω : ω ≠ 0) :
    LSpace (canonicalDivisorOf hω - ∑ j, Finsupp.single (v j) (1 : ℤ)) = ⊥ := by
  classical
  rw [Submodule.eq_bot_iff]
  intro f hf
  by_contra hf0
  set D : Divisor K F := ∑ j, Finsupp.single (v j) (1 : ℤ) with hD
  have hDnn : ∀ w, 0 ≤ D w := fun w => by
    rw [hD, Finsupp.finsetSum_apply]
    exact Finset.sum_nonneg fun k _ => by rw [Finsupp.single_apply]; split_ifs <;> norm_num
  obtain ⟨hreg, hord⟩ := smul_mem_of_mem_lSpace hω hDnn hf hf0
  set η : ↥(regularDifferentials K F) := ⟨f • ω, hreg⟩ with hη

  have hkill : ∀ j, evalFunctional (v j) η = 0 := fun j => by
    rw [evalFunctional_apply]
    refine evalAt_eq_zero_of_ord_pos (v j) (differentialCoeff_mem hreg (v j)) ?_
    refine lt_of_lt_of_le ?_ (hord (v j))
    have h1 : (1 : ℤ) ≤ D (v j) := by
      rw [hD, Finsupp.finsetSum_apply]
      calc (1 : ℤ) = Finsupp.single (v j) (1 : ℤ) (v j) := Finsupp.single_eq_same.symm
        _ ≤ ∑ k, Finsupp.single (v k) (1 : ℤ) (v j) :=
          Finset.single_le_sum (f := fun k => Finsupp.single (v k) (1 : ℤ) (v j))
            (fun k _ => by simp only [Finsupp.single_apply]; split_ifs <;> norm_num)
            (Finset.mem_univ j)
    exact Int.lt_of_lt_of_le zero_lt_one h1

  set a : Fin n → K := fun i => b.repr η i with ha
  have hvec : Matrix.vecMul a (Matrix.of fun i j : Fin n => evalFunctional (v j) (b i)) = 0 := by
    funext j
    have hsum : η = ∑ i, a i • b i := (b.sum_repr η).symm
    have := hkill j
    rw [hsum, map_sum] at this
    simp only [map_smul, smul_eq_mul] at this
    rw [Matrix.vecMul, dotProduct]
    simpa [Matrix.of_apply] using this
  have ha0 : a = 0 := by
    have hinv := h
    rw [← Matrix.isUnit_iff_isUnit_det] at hinv
    obtain ⟨u, hu⟩ := hinv
    have : Matrix.vecMul (Matrix.vecMul a (u : Matrix (Fin n) (Fin n) K))
        ((u⁻¹ : (Matrix (Fin n) (Fin n) K)ˣ) : Matrix (Fin n) (Fin n) K) = 0 := by
      rw [hu, hvec, Matrix.zero_vecMul]
    rwa [Matrix.vecMul_vecMul, Units.mul_inv, Matrix.vecMul_one] at this
  have hη0 : η = 0 := by
    rw [← b.linearCombination_repr η]
    have : b.repr η = 0 := by
      ext i; exact congrFun ha0 i
    rw [this, map_zero]
  have : f • ω = 0 := congrArg Subtype.val hη0
  rcases smul_eq_zero.1 this with h0 | h0
  · exact hf0 h0
  · exact hω h0

end Curve

end AlgebraicCurve.GeneralPositionProof

open AlgebraicCurve.GeneralPositionProof in
theorem solution
    {K F : Type*} [Field K] [IsAlgClosed K] [Field F] [Algebra K F]
    (hfg : ∃ x : F, Transcendental K x ∧
      FiniteDimensional (IntermediateField.adjoin K ({x} : Set F)) F)
    [IsCurveOver K F] [HasCanonicalDivisor (K := K) (F := F)]
    {n : ℕ} (b : Module.Basis (Fin n) K ↥(regularDifferentials K F)) :
    ∃ v : Fin n → Place K F, Function.Injective v ∧
      IsUnit (Matrix.det (Matrix.of fun i j : Fin n =>
        (v j).evalAt ((v j).differentialCoeff (b i : Ω[F⁄K])))) ∧
      ∀ f : F,
        (∀ w : Place K F, -((∑ j, Finsupp.single (v j) (1 : ℤ) : Divisor K F) w) ≤ w.ord f) →
          ∃ c : K, f = algebraMap K F c := by
  classical
  obtain ⟨x, hx, hxfd⟩ := hfg
  haveI : Algebra.EssFiniteType K F := essFiniteType_of_transcendental_of_finiteDimensional hx hxfd
  haveI : ∀ v : Place K F, v.DCoordGenerates := dCoordGenerates_of_isCurveOver
  have hRR : FunctionFieldRiemannRoch K F :=
    functionFieldRiemannRoch_of_isAlgClosed_of_transcendental hx hxfd
  have hell0 : ell (0 : Divisor K F) = 1 := ell_zero_eq_one hRR
  haveI : Infinite (Place K F) := infinite_place hell0 hx
  obtain ⟨v, hv⟩ := exists_isUnit_det b
  have hv' : IsUnit (Matrix.det (Matrix.of fun i j : Fin n =>
      (v j).evalAt ((v j).differentialCoeff (b i : Ω[F⁄K])))) := hv
  refine ⟨v, injective_of_isUnit_det b hv, hv', ?_⟩

  intro f hf
  obtain ⟨ω, hω⟩ := exists_ne (0 : Ω[F⁄K])
  have hDnn : (0 : Divisor K F) ≤ ∑ j, Finsupp.single (v j) (1 : ℤ) := fun w => by
    rw [Finsupp.finsetSum_apply]
    exact Finset.sum_nonneg fun k _ => by rw [Finsupp.single_apply]; split_ifs <;> norm_num
  have hgenus : (genus K F : ℤ) = n := by
    rw [← (finite_and_finrank_regularDifferentials_eq_genus (K := K) (F := F)).2,
      Module.finrank_eq_card_basis b, Fintype.card_fin]
  have hell' : ell (canonicalDivisorOf hω - ∑ j, Finsupp.single (v j) (1 : ℤ)) = 0 := by
    show Module.finrank K ↥(LSpace (canonicalDivisorOf hω - ∑ j, Finsupp.single (v j) (1 : ℤ))) = 0
    rw [lSpace_eq_bot_of_isUnit_det b hv hω, finrank_bot]
  have hRRD := hRR hω (∑ j, Finsupp.single (v j) (1 : ℤ))
  rw [hell', hgenus, degree_sum_single] at hRRD
  have hell : ell (∑ j, Finsupp.single (v j) (1 : ℤ) : Divisor K F) = 1 := by
    have : (ell (∑ j, Finsupp.single (v j) (1 : ℤ) : Divisor K F) : ℤ) = 1 := by
      push_cast at hRRD; linarith
    exact_mod_cast this
  have hfL : f ∈ LSpace (∑ j, Finsupp.single (v j) (1 : ℤ) : Divisor K F) := by
    rw [mem_lSpace_iff_ord]
    by_cases hf0 : f = 0
    · exact Or.inl hf0
    · exact Or.inr hf
  exact exists_eq_algebraMap_of_ell_eq_one hDnn hell hfL

end

end S_AlgebraicCurve_exists_isUnit_det_evalAt_differentialCoeff
end P2MW
export P2MW.S_AlgebraicCurve_exists_isUnit_det_evalAt_differentialCoeff (solution)
