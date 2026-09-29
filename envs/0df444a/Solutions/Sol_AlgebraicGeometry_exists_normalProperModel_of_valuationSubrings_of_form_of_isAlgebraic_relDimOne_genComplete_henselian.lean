-- Prove2me | solution 1 for AlgebraicGeometry.exists_normalProperModel_of_valuationSubrings_of_form_of_isAlgebraic_relDimOne_genComplete_henselian
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.122355+00:00
-- url     : https://prove2.me/submissions/bd4f8b35-1650-5ce3-a885-d05613c000a7

import Definitions.Def_AlgebraicCurve_SemistableModel
import Definitions.Def_AlgebraicCurve_IsCurveOver
import Definitions.Def_AlgebraicCurve_TwoChartIntegralModel
import Theorems.Thm_IntermediateField_finiteDimensional_adjoin_and_isSeparable_of_form_of_isAlgebraic_of_isCurveOver
import Theorems.Thm_ValuationSubring_exists_forall_mem_and_forall_isUnit_polynomialEval2_of_finset_of_isDiscreteValuationRing
import Theorems.Thm_ValuationSubring_inv_mem_and_chartAlg_le_and_over_gauss_and_isDiscreteValuationRing_of_forall_isUnit_polynomialEval2
import Theorems.Thm_ValuationSubring_not_mem_and_inv_not_mem_of_dominates_of_residuallyAlgebraic_of_forall_isUnit_polynomialEval2
import Theorems.Thm_AlgebraicCurve_TwoChartIntegralModel_isIntegral
import Theorems.Thm_AlgebraicCurve_TwoChartIntegralModel_isProper_toBase
import Theorems.Thm_AlgebraicCurve_TwoChartIntegralModel_flat_toBase
import Theorems.Thm_AlgebraicCurve_TwoChartIntegralModel_locallyOfFinitePresentation_toBase
import Theorems.Thm_AlgebraicCurve_TwoChartIntegralModel_isIntegrallyClosed_stalk
import Theorems.Thm_AlgebraicCurve_TwoChartIntegralModel_exists_ringEquiv_functionField_apply_eq_algebraMap_germ_iotaFin
import Theorems.Thm_AlgebraicCurve_TwoChartIntegralModel_exists_ringEquiv_functionField_apply_eq_algebraMap_germ
import Theorems.Thm_AlgebraicCurve_TwoChartIntegralModel_exists_stalk_iso_localization_chartAlgInf
import Theorems.Thm_AlgebraicCurve_TwoChartIntegralModel_forall_iff_mem_localRing_and_forall_iff_exists_mem_maximalIdeal
import Theorems.Thm_AlgebraicCurve_TwoChartIntegralModel_exists_stalk_iso_localization_atPrime_of_iotaFin_apply_eq
import Theorems.Thm_AlgebraicCurve_TwoChartIntegralModel_finite_polynomial_chartAlgFin_and_chartAlgInf
import Theorems.Thm_AlgebraicCurve_TwoChartIntegralModel_isFractionRing_chartAlg
import Theorems.Thm_AlgebraicCurve_TwoChartIntegralModel_finiteType_chartAlgFin_and_chartAlgInf
import Theorems.Thm_AlgebraicCurve_TwoChartIntegralModel_exists_valuationSubring_of_mem_minimalPrimes_chartAlgFin
import Theorems.Thm_AlgebraicCurve_TwoChartIntegralModel_exists_valuationSubring_forall_mem_nonunits_mem_asIdeal_of_mem_toBase
import Theorems.Thm_AlgebraicCurve_TwoChartIntegralModel_isNoetherianRing_stalk_and_essFiniteType_and_isDomain_and_injective
import Theorems.Thm_AlgebraicCurve_TwoChartIntegralModel_bijective_algebraMap_globalSections_iff_isIntegrallyClosedIn
import Theorems.Thm_AlgebraicGeometry_exists_localRing_eq_valuationSubring_of_isIntegrallyClosed_of_universallyClosed
import Theorems.Thm_AlgebraicGeometry_mem_smoothLocus_of_forall_mem_localRing_eq_algebraMap_mul_of_perfectField
import Theorems.Thm_AlgebraicCurve_TwoChartIntegralModel_mem_smoothLocus_toBase_of_asIdeal_eq_bot_of_charZero
import Theorems.Thm_AlgebraicCurve_TwoChartIntegralModel_mem_minimalPrimes_or_isMaximal_of_mem_chartAlgFin
import Theorems.Thm_AlgebraicCurve_TwoChartIntegralModel_eq_of_specializes_of_isMaximal_of_mem_chart
import Theorems.Thm_Algebra_IsAlgebraic_adjoin_singleton_of_finiteDimensional_intermediateField_adjoin_of_isFractionRing
import Theorems.Thm_ValuationSubring_exists_transcendental_forall_over_gauss_iff_mem_of_henselianLocalRing
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_exists_normalProperModel_of_valuationSubrings_of_form_of_isAlgebraic_relDimOne_genComplete_henselian
p2m_attr_erase "instance" "AlgebraicCurve.CurveModel.chartRing_finitePresentation AlgebraicCurve.CurveModel.isProper AlgebraicCurve.CurveModel.isIntegral AlgebraicCurve.CurveModel.smooth AlgebraicCurve.CurveModel.algebraAdjoin AlgebraicCurve.CurveModel.isDedekindDomain_chartRing AlgebraicCurve.CurveModel.isIntegralClosure AlgebraicCurve.CurveModel.finite_chartRing AlgebraicCurve.CurveModel.centre_isPrime AlgebraicCurve.CurveModel.isFractionRing_chartRing AlgebraicCurve.CurveModel.finiteType_chartRing AlgebraicCurve.CurveModel.isNoetherianRing_chartRing AlgebraicCurve.CurveModel.isScalarTower_base_adjoin AlgebraicCurve.CurveModel.isScalarTower_adjoin AlgebraicCurve.instFundamentalIdentityOfSumRamificationInertia AlgebraicCurve.Place.instIsScalarTowerResidueFieldRestrictPushforward AlgebraicCurve.Place.instAlgebraResidueFieldRestrictPushforward AlgebraicCurve.Place.instIsLocalHomRestrictInclusion AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.SemilinearAut.instDistribMulActionSubtypeProdRingAutMemSubgroupPic0 AlgebraicCurve.SemilinearAut.instDistribMulActionSubtypeProdRingAutMemSubgroupDivisor AlgebraicCurve.Pic0.instModuleZModTorsion AlgebraicCurve.SemilinearAut.instSMulSubtypeProdRingAutMemSubgroupPlace AlgebraicCurve.SemilinearAut.instDistribMulActionTorsion AlgebraicCurve.SemilinearAut.instSMulSubtypeProdRingAutMemSubgroupPic0 AlgebraicCurve.SemilinearAut.instSMulTorsion AlgebraicCurve.SemilinearAut.instMulActionSubtypeProdRingAutMemSubgroupPlace AlgebraicCurve.SemilinearAut.instSMulCommClassZModTorsion AlgebraicCurve.SemilinearAut.instMulSemiringActionSubtypeProdRingAutMemSubgroup AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions"
p2m_attr_erase "simp" "AlgebraicCurve.CurveModel.mk.injEq AlgebraicCurve.CurveModel.mk.sizeOf_spec AlgebraicCurve.CurveModel.coe_primeEquivChartPlaces AlgebraicCurve.Divisor.mapRestrict_single AlgebraicCurve.Divisor.pushforward_single AlgebraicCurve.Place.coe_restrictInclusion AlgebraicCurve.Place.mem_fiber AlgebraicCurve.Place.restrict_toValuationSubring AlgebraicCurve.Divisor.degree_pushforward AlgebraicCurve.Place.restrictResidueMap_residue AlgebraicCurve.Pic0.coe_pushforwardDegZeroHom AlgebraicCurve.Pic0.coe_pullbackDegZeroHom AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal AlgebraicCurve.IsFrobeniusEndo.frobNormRingHom_apply ModularCurve.frobeniusPushforwardGeomLevelPic0_mk ModularCurve.coe_frobeniusGeomLevelEquiv_apply ModularCurve.coe_frobeniusPushforwardGeomLevelDegZero ModularCurve.heckeFibreGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusGeomLevel_apply_coe ModularCurve.frobeniusPullbackGeomLevelPic0OfIsCurveOver_mk ModularCurve.coe_heckeFibreGeomLevelDegZero ModularCurve.coe_frobeniusPullbackGeomLevelDegZero ModularCurve.frobeniusPullbackGeomLevelPic0_mk ModularCurve.frobeniusPullbackGeomLevel_single ModularCurve.heckeFibreGeomLevelPic0_mk ModularCurve.frobeniusPushforwardGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusPushforwardGeomLevel_single ModularCurve.qExpandAlgC_apply AlgebraicCurve.Place.congrEquiv_symm_apply AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply AlgebraicCurve.RationalFunctionField.deg_placeOfPoint AlgebraicCurve.Divisor.degree_pushforwardAlong AlgebraicCurve.Pic0.coe_degZeroCorrespondence"
p2m_attr_erase "simp" "AlgebraicCurve.Place.mem_fiberAlong AlgebraicCurve.SemilinearAut.toRingAut_inv AlgebraicCurve.SemilinearAut.smul_def AlgebraicCurve.SemilinearAut.smul_single AlgebraicCurve.SemilinearAut.smul_toValuationSubring AlgebraicCurve.SemilinearAut.baseAut_inv AlgebraicCurve.SemilinearAut.baseAut_ofAlgAut AlgebraicCurve.SemilinearAut.toRingAut_ofAlgAut AlgebraicCurve.SemilinearAut.torsionRep_apply AlgebraicCurve.SemilinearAut.toRingAut_one AlgebraicCurve.SemilinearAut.deg_smul AlgebraicCurve.SemilinearAut.degree_smul AlgebraicCurve.SemilinearAut.coe_degZeroSMulHom AlgebraicCurve.SemilinearAut.baseAut_mul AlgebraicCurve.SemilinearAut.coe_smulValuationSubringEquiv_apply AlgebraicCurve.SemilinearAut.baseAut_one AlgebraicCurve.SemilinearAut.ofAlgAut_smul AlgebraicCurve.SemilinearAut.coe_torsion_smul AlgebraicCurve.SemilinearAut.toRingAut_mul AlgebraicCurve.coe_frobeniusPushforwardDegZero AlgebraicCurve.IsFrobeniusEndo.coe_frobeniusPullbackDegZero ModularCurve.jqNModC_one ModularCurve.qExpand_coeff_mul ModularCurve.qExpandₐ_apply ModularCurve.jqN_one ModularCurve.qExpand_single ModularCurve.dedekindPsi_one ModularCurve.ModularPolynomialData.mk.sizeOf_spec ModularCurve.evalAtJ_X ModularCurve.ModularPolynomialData.mk.injEq ModularCurve.constantCoeff_jNum ModularCurve.constantCoeff_eisenstein4 ModularCurve.qExpand_C ModularCurve.coeff_jq_neg_one ModularCurve.constantCoeff_jNumQ ModularCurve.reduceModBivar_C_X ModularCurve.laurentMap_coeff ModularCurve.reduceModBivar_X ModularCurve.laurentMap_single ModularCurve.evalAtJInt_X"
p2m_attr_erase "simp" "ModularCurve.evalAtJMod_X ModularCurve.jqNMod_one ModularCurve.aeval_heckeGen ModularCurve.coe_mTorsionGaloisRep_apply ModularCurve.eisensteinSystem_of_dvd ModularCurve.eisensteinSystem_of_not_dvd AlgebraicCurve.RationalFunctionField.placeInfty_toValuationSubring AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none AlgebraicCurve.mulAdele_apply AlgebraicCurve.residuePairing_apply_coe AlgebraicCurve.mem_adeleBdd AlgebraicCurve.weilSmul_one AlgebraicCurve.diagonalHom_apply AlgebraicCurve.weilSmul_apply AlgebraicCurve.adeleSpaceMul_coe AlgebraicCurve.mulAdele_one AlgebraicCurve.coe_cechH0Equiv_apply AlgebraicCurve.cechH1ToH1_mk AlgebraicCurve.lSpaceOn_univ AlgebraicCurve.lSpaceOn_empty AdicCompletion.evalₐ_mapₐ AdicCompletion.mapAlgEquivOfBijective_apply AdicCompletion.levelMapₐ_mk AdicCompletion.mapₐ_of AdicCompletion.mapAlgEquiv_symm_apply AdicCompletion.mapAlgEquiv_apply AdicCompletion.evalₐ_ofLevelwiseEquiv AdicCompletion.evalₐ_levelwiseHom AdicCompletion.localizationEquiv_of AdicCompletion.evalₐ_ofLevelwiseEquiv_symm Localization.AtPrime.quotientPowEquiv_mk AlgebraicCurve.TranscendenceTower.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.injEq AlgebraicCurve.TranscendenceTower.mk.injEq AlgebraicCurve.PoleDivisorPackage.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.sizeOf_spec AlgebraicCurve.PoleDivisorPackage.mk.injEq"

set_option autoImplicit false

universe u

p2m_open "AlgebraicCurve~baseToFunctionField IsLocalRing CategoryTheory AlgebraicGeometry AlgebraicCurve.TwoChartIntegralModel"

theorem MFVR.localRing_ιFin_iff
    (R : Type u) [CommRing R] (F : Type u) [Field F] [Algebra R F] (j : F) [Fact (j ≠ 0)]
    [IsIntegral (TwoChartIntegralModel R F j)]
    (φ : F ≃+* (TwoChartIntegralModel R F j).functionField)
    (hφFin : ∀ (y : ↥(XFin R F j)) (b : ↥(chartAlgFin R F j)),
        φ (b : F) = algebraMap ((TwoChartIntegralModel R F j).presheaf.stalk ((ιFin R F j).base y))
          (TwoChartIntegralModel R F j).functionField
          (((TwoChartIntegralModel R F j).presheaf.germ ((ιFin R F j) ''ᵁ ⊤) ((ιFin R F j).base y) ⟨y, trivial, rfl⟩).hom
            (((ιFin R F j).appIso ⊤).inv.hom ((Scheme.ΓSpecIso (CommRingCat.of ↥(chartAlgFin R F j))).inv.hom b))))
    (y : ↥(XFin R F j)) (f : F) :
    f ∈ SemistableModel.localRing (TwoChartIntegralModel R F j) φ ((ιFin R F j).base y) ↔
      ∃ b c : ↥(chartAlgFin R F j), c ∉ y.asIdeal ∧ f * (c : F) = (b : F) := by
  classical
  set X := TwoChartIntegralModel R F j with hX
  set x := (ιFin R F j).base y with hx

  let Gh : ↥(chartAlgFin R F j) →+* ↑(X.presheaf.stalk x) :=
    ((X.presheaf.germ ((ιFin R F j) ''ᵁ ⊤) x ⟨y, trivial, rfl⟩).hom.comp
      (((ιFin R F j).appIso ⊤).inv.hom)).comp (Scheme.ΓSpecIso (CommRingCat.of ↥(chartAlgFin R F j))).inv.hom
  have hGh : ∀ b : ↥(chartAlgFin R F j), φ (b : F) = algebraMap _ X.functionField (Gh b) := fun b => hφFin y b
  obtain ⟨e, he₁, he₂⟩ :=
    TwoChartIntegralModel.exists_stalk_iso_localization_atPrime_of_iotaFin_apply_eq R F j x y rfl
  have he₂' : ∀ a : ↥(chartAlgFin R F j), e.hom.hom (Gh a) = algebraMap _ (Localization.AtPrime y.asIdeal) a :=
    fun a => he₂ a
  have hinv : ∀ s, e.inv.hom (e.hom.hom s) = s := fun s => by
    have := congrArg (fun ψ => CommRingCat.Hom.hom ψ s) e.hom_inv_id
    simpa [CommRingCat.hom_comp, CommRingCat.hom_id] using this
  have hinv' : ∀ t, e.hom.hom (e.inv.hom t) = t := fun t => by
    have := congrArg (fun ψ => CommRingCat.Hom.hom ψ t) e.inv_hom_id
    simpa [CommRingCat.hom_comp, CommRingCat.hom_id] using this
  have hinjK : Function.Injective (algebraMap (X.presheaf.stalk x) X.functionField) := by
    first
    | exact IsFractionRing.injective (X.presheaf.stalk x) X.functionField
    | exact NoZeroSMulDivisors.algebraMap_injective _ _
    | exact (algebraMap (X.presheaf.stalk x) X.functionField).injective

  have hunit : ∀ c : ↥(chartAlgFin R F j), c ∉ y.asIdeal → IsUnit (Gh c) := by
    intro c hc
    have hu : IsUnit (algebraMap _ (Localization.AtPrime y.asIdeal) c) :=
      IsLocalization.map_units (M := y.asIdeal.primeCompl) _ ⟨c, hc⟩
    rw [← he₂'] at hu
    have := hu.map e.inv.hom
    simpa [hinv] using this
  constructor
  ·
    rintro ⟨s, rfl⟩
    obtain ⟨⟨b, c⟩, hbc⟩ := IsLocalization.surj y.asIdeal.primeCompl (e.hom.hom s)

    refine ⟨b, c, c.2, ?_⟩
    have hs : s * Gh c = Gh b := by
      have := congrArg e.inv.hom hbc
      simpa [map_mul, hinv, ← he₂'] using this
    have := congrArg (fun t => φ.symm (algebraMap (X.presheaf.stalk x) X.functionField t)) hs
    simp only [map_mul] at this

    have hGh' : ∀ a : ↥(chartAlgFin R F j), φ.symm (algebraMap _ X.functionField (Gh a)) = (a : F) := fun a => by
      rw [← hGh, RingEquiv.symm_apply_apply]
    simpa [hGh'] using this
  ·
    rintro ⟨b, c, hc, hfc⟩
    obtain ⟨u, hu⟩ := hunit c hc
    have hc0 : (c : F) ≠ 0 := by
      intro h0
      apply hc
      have : c = 0 := Subtype.ext h0
      rw [this]; exact Ideal.zero_mem _
    refine ⟨Gh b * ↑u⁻¹, ?_⟩
    show φ.symm (algebraMap _ X.functionField (Gh b * ↑u⁻¹)) = f
    apply φ.injective
    rw [RingEquiv.apply_symm_apply]
    have hφc : φ (c : F) ≠ 0 := fun h => hc0 (by simpa using congrArg φ.symm h)
    apply mul_right_cancel₀ hφc
    rw [← map_mul φ, hfc, hGh b, hGh c, ← map_mul, mul_assoc, ← hu, Units.inv_mul, mul_one]

theorem MFVR.localRing_ιInf_iff
    (R : Type u) [CommRing R] (F : Type u) [Field F] [Algebra R F] (j : F) [Fact (j ≠ 0)]
    [IsIntegral (TwoChartIntegralModel R F j)]
    (φ : F ≃+* (TwoChartIntegralModel R F j).functionField)
    (hφInf : ∀ (y : ↥(XInf R F j)) (b : ↥(chartAlgInf R F j)),
        φ (b : F) = algebraMap ((TwoChartIntegralModel R F j).presheaf.stalk ((ιInf R F j).base y))
          (TwoChartIntegralModel R F j).functionField
          (((TwoChartIntegralModel R F j).presheaf.germ ((ιInf R F j) ''ᵁ ⊤) ((ιInf R F j).base y) ⟨y, trivial, rfl⟩).hom
            (((ιInf R F j).appIso ⊤).inv.hom ((Scheme.ΓSpecIso (CommRingCat.of ↥(chartAlgInf R F j))).inv.hom b))))
    (y : ↥(XInf R F j)) (f : F) :
    f ∈ SemistableModel.localRing (TwoChartIntegralModel R F j) φ ((ιInf R F j).base y) ↔
      ∃ b c : ↥(chartAlgInf R F j), c ∉ y.asIdeal ∧ f * (c : F) = (b : F) := by
  classical
  set X := TwoChartIntegralModel R F j with hX
  set x := (ιInf R F j).base y with hx

  let Gh : ↥(chartAlgInf R F j) →+* ↑(X.presheaf.stalk x) :=
    ((X.presheaf.germ ((ιInf R F j) ''ᵁ ⊤) x ⟨y, trivial, rfl⟩).hom.comp
      (((ιInf R F j).appIso ⊤).inv.hom)).comp (Scheme.ΓSpecIso (CommRingCat.of ↥(chartAlgInf R F j))).inv.hom
  have hGh : ∀ b : ↥(chartAlgInf R F j), φ (b : F) = algebraMap _ X.functionField (Gh b) := fun b => hφInf y b
  obtain ⟨e, he₁, he₂⟩ :=
    TwoChartIntegralModel.exists_stalk_iso_localization_chartAlgInf R F j y ⟨y, trivial, rfl⟩
  have he₂' : ∀ a : ↥(chartAlgInf R F j), e.hom.hom (Gh a) = algebraMap _ (Localization.AtPrime y.asIdeal) a :=
    fun a => he₂ a
  have hinv : ∀ s, e.inv.hom (e.hom.hom s) = s := fun s => by
    have := congrArg (fun ψ => CommRingCat.Hom.hom ψ s) e.hom_inv_id
    simpa [CommRingCat.hom_comp, CommRingCat.hom_id] using this
  have hinv' : ∀ t, e.hom.hom (e.inv.hom t) = t := fun t => by
    have := congrArg (fun ψ => CommRingCat.Hom.hom ψ t) e.inv_hom_id
    simpa [CommRingCat.hom_comp, CommRingCat.hom_id] using this
  have hinjK : Function.Injective (algebraMap (X.presheaf.stalk x) X.functionField) := by
    first
    | exact IsFractionRing.injective (X.presheaf.stalk x) X.functionField
    | exact NoZeroSMulDivisors.algebraMap_injective _ _
    | exact (algebraMap (X.presheaf.stalk x) X.functionField).injective

  have hunit : ∀ c : ↥(chartAlgInf R F j), c ∉ y.asIdeal → IsUnit (Gh c) := by
    intro c hc
    have hu : IsUnit (algebraMap _ (Localization.AtPrime y.asIdeal) c) :=
      IsLocalization.map_units (M := y.asIdeal.primeCompl) _ ⟨c, hc⟩
    rw [← he₂'] at hu
    have := hu.map e.inv.hom
    simpa [hinv] using this
  constructor
  ·
    rintro ⟨s, rfl⟩
    obtain ⟨⟨b, c⟩, hbc⟩ := IsLocalization.surj y.asIdeal.primeCompl (e.hom.hom s)

    refine ⟨b, c, c.2, ?_⟩
    have hs : s * Gh c = Gh b := by
      have := congrArg e.inv.hom hbc
      simpa [map_mul, hinv, ← he₂'] using this
    have := congrArg (fun t => φ.symm (algebraMap (X.presheaf.stalk x) X.functionField t)) hs
    simp only [map_mul] at this

    have hGh' : ∀ a : ↥(chartAlgInf R F j), φ.symm (algebraMap _ X.functionField (Gh a)) = (a : F) := fun a => by
      rw [← hGh, RingEquiv.symm_apply_apply]
    simpa [hGh'] using this
  ·
    rintro ⟨b, c, hc, hfc⟩
    obtain ⟨u, hu⟩ := hunit c hc
    have hc0 : (c : F) ≠ 0 := by
      intro h0
      apply hc
      have : c = 0 := Subtype.ext h0
      rw [this]; exact Ideal.zero_mem _
    refine ⟨Gh b * ↑u⁻¹, ?_⟩
    show φ.symm (algebraMap _ X.functionField (Gh b * ↑u⁻¹)) = f
    apply φ.injective
    rw [RingEquiv.apply_symm_apply]
    have hφc : φ (c : F) ≠ 0 := fun h => hc0 (by simpa using congrArg φ.symm h)
    apply mul_right_cancel₀ hφc
    rw [← map_mul φ, hfc, hGh b, hGh c, ← map_mul, mul_assoc, ← hu, Units.inv_mul, mul_one]

theorem solution
    (A₀ : Type) [CommRing A₀] [IsDomain A₀] [IsDiscreteValuationRing A₀] [HenselianLocalRing A₀]
    (ϖ₀ : A₀) (hϖ₀ : maximalIdeal A₀ = Ideal.span {ϖ₀})
    {L : Type} [Field L] [CharZero L] (ι₀ : A₀ →+* L) (hι₀ : Function.Injective ι₀)
    (K₀ : Subfield L) (hK₀A : ∀ a : A₀, ι₀ a ∈ K₀)
    (hK₀ : ∀ x : L, x ∈ K₀ → ∃ a b : A₀, b ≠ 0 ∧ x * ι₀ b = ι₀ a)

    (hLK₀ : ∀ x : L, IsAlgebraic ↥K₀ x)
    {F : Type} [Field F] [Algebra L F] [IsCurveOver L F] [Algebra.EssFiniteType L F]

    (hLalg : ∀ x : F, IsAlgebraic L x → x ∈ Set.range (algebraMap L F))
    (F₀ : Subfield F)
    (hconst : ∀ c : L, algebraMap L F c ∈ F₀ ↔ c ∈ K₀)
    (hspan : ∀ f : F, ∃ (n : ℕ) (c : Fin n → L) (g : Fin n → ↥F₀) (d : Fin n → L) (g' : Fin n → ↥F₀),
      (∑ i, d i • (g' i : F)) ≠ 0 ∧ f * (∑ i, d i • (g' i : F)) = ∑ i, c i • (g i : F))

    (j₀ : A₀ →+* ↥F₀) (hj₀ : ∀ a : A₀, ((j₀ a : ↥F₀) : F) = algebraMap L F (ι₀ a))
    (V : Finset (ValuationSubring ↥F₀)) (hV : V.Nonempty)
    (hdom : ∀ O ∈ V, (∀ a : A₀, j₀ a ∈ O) ∧ ∃ hO : j₀ ϖ₀ ∈ O, (⟨_, hO⟩ : ↥O) ∈ maximalIdeal ↥O)
    (hgeo : ∀ O ∈ V, ∃ f : ↥F₀, f ∈ O ∧ ∀ p : Polynomial A₀, (∃ i, IsUnit (p.coeff i)) →
      ∃ hO : Polynomial.eval₂ j₀ f p ∈ O, IsUnit (⟨_, hO⟩ : ↥O)) :
    ∃ (X₀ : Scheme.{0}) (toBase₀ : X₀ ⟶ Spec (CommRingCat.of A₀))
      (_ : IsIntegral X₀) (_ : IsProper toBase₀) (_ : Flat toBase₀) (_ : LocallyOfFinitePresentation toBase₀)
      (φ₀ : ↥F₀ ≃+* X₀.functionField),
      (∀ a : A₀, φ₀ (j₀ a) = SemistableModel.baseToFunctionField toBase₀ a) ∧
      (∀ y : X₀, IsIntegrallyClosed (X₀.presheaf.stalk y)) ∧
      Function.Bijective (fun a : A₀ => toBase₀.appTop.hom ((Scheme.ΓSpecIso (CommRingCat.of A₀)).inv.hom a)) ∧
      (∀ y : X₀, (toBase₀.base y).asIdeal = ⊥ → y ∈ toBase₀.smoothLocus) ∧

      (∀ η y : X₀, toBase₀.base η = closedPoint A₀ → (∃ z : X₀, η ⤳ z ∧ z ≠ η) → η ⤳ y → y ≠ η →
        ∀ z : X₀, y ⤳ z → z = y) ∧

      (∀ O' : ValuationSubring ↥F₀, O' ≠ ⊤ → (∀ a : A₀, a ≠ 0 → (j₀ a : ↥F₀)⁻¹ ∈ O') →
        ∃ y : X₀, O'.toSubring = SemistableModel.localRing X₀ φ₀ y) ∧
      (∀ O ∈ V, ∃ η : X₀, toBase₀.base η = closedPoint A₀ ∧ (∃ y : X₀, η ⤳ y ∧ y ≠ η) ∧
        SemistableModel.localRing X₀ φ₀ η = O.toSubring) ∧
      (∀ η : X₀, toBase₀.base η = closedPoint A₀ → (∃ y : X₀, η ⤳ y ∧ y ≠ η) →
        ∃ O ∈ V, SemistableModel.localRing X₀ φ₀ η = O.toSubring) := by
  classical

  letI algF : Algebra A₀ ↥F₀ := j₀.toAlgebra
  letI algK : Algebra A₀ ↥K₀ := (ι₀.codRestrict K₀ hK₀A).toAlgebra
  letI algKF : Algebra ↥K₀ ↥F₀ :=
    (((algebraMap L F).comp K₀.subtype).codRestrict F₀ (fun c => (hconst (c : L)).mpr c.2)).toAlgebra
  have halgF : ∀ a : A₀, algebraMap A₀ ↥F₀ a = j₀ a := fun _ => rfl
  have hϖnu : ¬ IsUnit ϖ₀ := fun hu =>
    (IsLocalRing.mem_maximalIdeal _).mp (by rw [hϖ₀]; exact Ideal.mem_span_singleton_self ϖ₀) hu
  have hndvd0 : ∀ p : Polynomial A₀, (∃ i, IsUnit (p.coeff i)) → ¬ (Polynomial.C ϖ₀ ∣ p) := by
    rintro p ⟨i, hi⟩ hdvd
    rw [Polynomial.C_dvd_iff_dvd_coeff] at hdvd
    exact hϖnu (isUnit_of_dvd_unit (hdvd i) hi)

  obtain ⟨hfrK, hST, ⟨t₀, ht₀⟩, hfin, hIC⟩ :=
    IntermediateField.finiteDimensional_adjoin_and_isSeparable_of_form_of_isAlgebraic_of_isCurveOver
      A₀ ι₀ hι₀ K₀ hK₀A hK₀ hLK₀ hLalg F₀ hconst hspan j₀ hj₀
  haveI := hfrK
  haveI := hST

  have hRO : ∀ O ∈ V, ∀ a : A₀, algebraMap A₀ ↥F₀ a ∈ O := fun O hO a => (hdom O hO).1 a
  have hϖO : ∀ O ∈ V, algebraMap A₀ ↥F₀ ϖ₀ ∈ O.nonunits := fun O hO => by
    obtain ⟨hO, hm⟩ := (hdom O hO).2
    exact ValuationSubring.mem_nonunits_iff_exists_mem_maximalIdeal.mpr ⟨hO, hm⟩

  have hdvr : ∀ O ∈ V, IsDiscreteValuationRing ↥O := by
    intro O hO
    obtain ⟨fO, hfO, hgeoO⟩ := hgeo O hO
    obtain ⟨hf0, -, htf, -, -, -, hrest⟩ :=
      ValuationSubring.inv_mem_and_chartAlg_le_and_over_gauss_and_isDiscreteValuationRing_of_forall_isUnit_polynomialEval2
        A₀ ϖ₀ hϖ₀ ↥K₀ ↥F₀ O (hRO O hO) (hϖO O hO) fO hfO hgeoO
    exact (hrest (hfin fO htf).1 (hfin fO htf).2).1

  obtain ⟨f, hf⟩ :=
    ValuationSubring.exists_forall_mem_and_forall_isUnit_polynomialEval2_of_finset_of_isDiscreteValuationRing j₀ V hdvr hgeo
  obtain ⟨O₁, hO₁⟩ := hV
  obtain ⟨hf0, -, htf, -, -, -, -⟩ :=
    ValuationSubring.inv_mem_and_chartAlg_le_and_over_gauss_and_isDiscreteValuationRing_of_forall_isUnit_polynomialEval2
      A₀ ϖ₀ hϖ₀ ↥K₀ ↥F₀ O₁ (hRO O₁ hO₁) (hϖO O₁ hO₁) f (hf O₁ hO₁).1 (hf O₁ hO₁).2

  have hVf : ∀ O ∈ V, (∀ a : A₀, algebraMap A₀ ↥F₀ a ∈ O) ∧ algebraMap A₀ ↥F₀ ϖ₀ ∈ O.nonunits ∧
      ∀ P : Polynomial A₀, ¬ (Polynomial.C ϖ₀ ∣ P) →
        Polynomial.aeval f P ∈ O ∧ (Polynomial.aeval f P)⁻¹ ∈ O := by
    intro O hO
    obtain ⟨hf0', -, -, -, -, hgauss, -⟩ :=
      ValuationSubring.inv_mem_and_chartAlg_le_and_over_gauss_and_isDiscreteValuationRing_of_forall_isUnit_polynomialEval2
        A₀ ϖ₀ hϖ₀ ↥K₀ ↥F₀ O (hRO O hO) (hϖO O hO) f (hf O hO).1 (hf O hO).2
    exact ⟨hRO O hO, hϖO O hO, hgauss⟩

  haveI : CharZero ↥K₀ := inferInstance
  obtain ⟨g, htg, hFDg, hsepg, hComp⟩ :=
    ValuationSubring.exists_transcendental_forall_over_gauss_iff_mem_of_henselianLocalRing
      A₀ ϖ₀ hϖ₀ ↥K₀ ↥F₀ f htf (hfin f htf).1 (hfin f htf).2 V ⟨O₁, hO₁⟩ hVf

  have hg0 : g ≠ 0 := fun h => htg (h ▸ isAlgebraic_zero)
  haveI : Fact (g ≠ 0) := ⟨hg0⟩

  have hg0' : g⁻¹ ≠ 0 := inv_ne_zero hg0
  haveI : Fact (g⁻¹ ≠ 0) := ⟨hg0'⟩
  have hadj : IntermediateField.adjoin ↥K₀ ({g⁻¹} : Set ↥F₀) = IntermediateField.adjoin ↥K₀ ({g} : Set ↥F₀) := by
    apply le_antisymm
    · exact IntermediateField.adjoin_simple_le_iff.mpr (inv_mem (IntermediateField.mem_adjoin_simple_self _ _))
    · refine IntermediateField.adjoin_simple_le_iff.mpr ?_
      have := inv_mem (IntermediateField.mem_adjoin_simple_self (↥K₀) g⁻¹)
      simpa using this
  have htg' : Transcendental A₀ g⁻¹ := by
    first
    | exact htg.inv
    | exact fun h => htg (by simpa using h.inv)
    | exact fun h => htg (IsAlgebraic.inv_iff.mp h)
  have hFDg' : FiniteDimensional ↥(IntermediateField.adjoin ↥K₀ ({g⁻¹} : Set ↥F₀)) ↥F₀ := by
    rw [hadj]; exact hFDg
  have hsepg' : Algebra.IsSeparable ↥(IntermediateField.adjoin ↥K₀ ({g⁻¹} : Set ↥F₀)) ↥F₀ := by
    rw [hadj]; exact hsepg
  haveI : IsIntegral (TwoChartIntegralModel A₀ ↥F₀ g) := TwoChartIntegralModel.isIntegral A₀ ↥F₀ g
  obtain ⟨hFTfin, hFTinf⟩ := TwoChartIntegralModel.finiteType_chartAlgFin_and_chartAlgInf A₀ ↥K₀ ↥F₀ g htg hFDg hsepg
  haveI := hFTfin
  haveI := hFTinf
  haveI : IsProper (toBase A₀ ↥F₀ g) := TwoChartIntegralModel.isProper_toBase A₀ ↥F₀ g
  have hinj : Function.Injective (algebraMap A₀ ↥F₀) := by
    intro a b hab
    apply hι₀
    apply (algebraMap L F).injective
    rw [← hj₀, ← hj₀, ← halgF, ← halgF, hab]
  haveI : Flat (toBase A₀ ↥F₀ g) := TwoChartIntegralModel.flat_toBase A₀ ↥F₀ g hinj
  haveI : LocallyOfFinitePresentation (toBase A₀ ↥F₀ g) :=
    TwoChartIntegralModel.locallyOfFinitePresentation_toBase A₀ ↥F₀ g
  haveI : Algebra.IsAlgebraic ↥(IntermediateField.adjoin ↥K₀ ({g} : Set ↥F₀)) ↥F₀ := Algebra.IsAlgebraic.of_finite _ _
  have hfrac : IsFractionRing ↥(chartAlgFin A₀ ↥F₀ g) ↥F₀ := TwoChartIntegralModel.isFractionRing_chartAlg A₀ ↥K₀ ↥F₀ {g}
  obtain ⟨φ, hφFin, hφInf, hφbase⟩ :=
    TwoChartIntegralModel.exists_ringEquiv_functionField_apply_eq_algebraMap_germ A₀ ↥F₀ g hfrac
  refine ⟨TwoChartIntegralModel A₀ ↥F₀ g, toBase A₀ ↥F₀ g, inferInstance, inferInstance, inferInstance, inferInstance, φ,
    ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  ·
    intro a
    rw [← halgF]
    exact hφbase a
  ·
    exact fun y => TwoChartIntegralModel.isIntegrallyClosed_stalk A₀ ↥F₀ g y
  ·
    have hSt := (TwoChartIntegralModel.bijective_algebraMap_globalSections_iff_isIntegrallyClosedIn A₀ ↥F₀ g).mpr hIC
    convert hSt using 2
    first
    | (simp [Scheme.TwoAffineOpenCover.algebraOfHom, RingHom.algebraMap_toAlgebra, Scheme.Hom.appLE, Scheme.Hom.appTop]; done)
    | (simp [Scheme.TwoAffineOpenCover.algebraOfHom, RingHom.algebraMap_toAlgebra]; rfl)
  ·
    intro y hy
    exact TwoChartIntegralModel.mem_smoothLocus_toBase_of_asIdeal_eq_bot_of_charZero A₀ ↥K₀ ↥F₀ g htg hFDg hsepg y hy
  ·
    intro η y hηsp hηnc hηy hyne z hyz
    rcases TwoChartIntegralModel.mem_range_ιFin_or_mem_range_ιInf A₀ ↥F₀ g y with ⟨yy, hyy⟩ | ⟨yy, hyy⟩
    ·

      have hopen : IsOpen (Set.range (ιFin A₀ ↥F₀ g).base) := (ιFin A₀ ↥F₀ g).isOpenEmbedding.isOpen_range
      obtain ⟨yη, hyη⟩ := hηy.mem_open hopen ⟨yy, hyy⟩
      have hind : Topology.IsInducing (ιFin A₀ ↥F₀ g).base := by
        first
        | exact (ιFin A₀ ↥F₀ g).isOpenEmbedding.isInducing
        | exact (ιFin A₀ ↥F₀ g).isOpenEmbedding.toIsEmbedding.toIsInducing
        | exact (ιFin A₀ ↥F₀ g).isOpenEmbedding.isEmbedding.isInducing
      have hsp : yη ⤳ yy := hind.specializes_iff.mp (by rw [hyη, hyy]; exact hηy)
      have hle : yη.asIdeal ≤ yy.asIdeal := (PrimeSpectrum.le_iff_specializes yη yy).mpr hsp
      have hne' : yη ≠ yy := fun h => hyne (by rw [← hyy, ← hyη, h])

      have hϖη : algebraMap A₀ ↥(chartAlgFin A₀ ↥F₀ g) ϖ₀ ∈ yη.asIdeal := by
        have hcomp : (toBase A₀ ↥F₀ g).base ((ιFin A₀ ↥F₀ g).base yη) = (ιFin A₀ ↥F₀ g ≫ toBase A₀ ↥F₀ g).base yη := by
          first
          | rfl
          | simp
        have h1 : ((Spec.map (CommRingCat.ofHom (algebraMap A₀ ↥(chartAlgFin A₀ ↥F₀ g)))).base yη).asIdeal =
            Ideal.comap (algebraMap A₀ ↥(chartAlgFin A₀ ↥F₀ g)) yη.asIdeal := by
          first
          | rfl
          | simp
        have h2 : (closedPoint A₀).asIdeal = maximalIdeal A₀ := by
          first
          | rfl
          | simp
        have h3 := congrArg PrimeSpectrum.asIdeal hηsp
        rw [← hyη, hcomp, TwoChartIntegralModel.ιFin_toBase, h1, h2, hϖ₀] at h3
        have : ϖ₀ ∈ Ideal.comap (algebraMap A₀ ↥(chartAlgFin A₀ ↥F₀ g)) yη.asIdeal := by
          rw [h3]; exact Ideal.mem_span_singleton_self ϖ₀
        exact Ideal.mem_comap.mp this
      have hϖyy : algebraMap A₀ ↥(chartAlgFin A₀ ↥F₀ g) ϖ₀ ∈ yy.asIdeal := hle hϖη
      rcases TwoChartIntegralModel.mem_minimalPrimes_or_isMaximal_of_mem_chartAlgFin A₀ ϖ₀ hϖ₀ ↥K₀ ↥F₀ g htg hFDg hsepg
          yη.asIdeal hϖη with hminη | hmaxη
      · rcases TwoChartIntegralModel.mem_minimalPrimes_or_isMaximal_of_mem_chartAlgFin A₀ ϖ₀ hϖ₀ ↥K₀ ↥F₀ g htg hFDg hsepg
            yy.asIdeal hϖyy with hminy | hmaxy
        · exfalso
          have hge : yy.asIdeal ≤ yη.asIdeal := hminy.2 ⟨yη.isPrime, hminη.1.2⟩ hle
          exact hne' (PrimeSpectrum.ext (le_antisymm hle hge))
        · exact TwoChartIntegralModel.eq_of_specializes_of_isMaximal_of_mem_chart A₀ ϖ₀ hϖ₀ ↥K₀ ↥F₀ g htg hFDg hsepg
            y (Or.inl ⟨yy, hyy, hmaxy, hϖyy⟩) z hyz
      · exfalso
        have heq : yη.asIdeal = yy.asIdeal := hmaxη.eq_of_le yy.isPrime.ne_top hle
        exact hne' (PrimeSpectrum.ext heq)
    ·

      have hopen : IsOpen (Set.range (ιInf A₀ ↥F₀ g).base) := (ιInf A₀ ↥F₀ g).isOpenEmbedding.isOpen_range
      obtain ⟨yη, hyη⟩ := hηy.mem_open hopen ⟨yy, hyy⟩
      have hind : Topology.IsInducing (ιInf A₀ ↥F₀ g).base := by
        first
        | exact (ιInf A₀ ↥F₀ g).isOpenEmbedding.isInducing
        | exact (ιInf A₀ ↥F₀ g).isOpenEmbedding.toIsEmbedding.toIsInducing
        | exact (ιInf A₀ ↥F₀ g).isOpenEmbedding.isEmbedding.isInducing
      have hsp : yη ⤳ yy := hind.specializes_iff.mp (by rw [hyη, hyy]; exact hηy)
      have hle : yη.asIdeal ≤ yy.asIdeal := (PrimeSpectrum.le_iff_specializes yη yy).mpr hsp
      have hne' : yη ≠ yy := fun h => hyne (by rw [← hyy, ← hyη, h])

      have hϖη : algebraMap A₀ ↥(chartAlgInf A₀ ↥F₀ g) ϖ₀ ∈ yη.asIdeal := by
        have hcomp : (toBase A₀ ↥F₀ g).base ((ιInf A₀ ↥F₀ g).base yη) = (ιInf A₀ ↥F₀ g ≫ toBase A₀ ↥F₀ g).base yη := by
          first
          | rfl
          | simp
        have h1 : ((Spec.map (CommRingCat.ofHom (algebraMap A₀ ↥(chartAlgInf A₀ ↥F₀ g)))).base yη).asIdeal =
            Ideal.comap (algebraMap A₀ ↥(chartAlgInf A₀ ↥F₀ g)) yη.asIdeal := by
          first
          | rfl
          | simp
        have h2 : (closedPoint A₀).asIdeal = maximalIdeal A₀ := by
          first
          | rfl
          | simp
        have h3 := congrArg PrimeSpectrum.asIdeal hηsp
        rw [← hyη, hcomp, TwoChartIntegralModel.ιInf_toBase, h1, h2, hϖ₀] at h3
        have : ϖ₀ ∈ Ideal.comap (algebraMap A₀ ↥(chartAlgInf A₀ ↥F₀ g)) yη.asIdeal := by
          rw [h3]; exact Ideal.mem_span_singleton_self ϖ₀
        exact Ideal.mem_comap.mp this
      have hϖyy : algebraMap A₀ ↥(chartAlgInf A₀ ↥F₀ g) ϖ₀ ∈ yy.asIdeal := hle hϖη
      rcases TwoChartIntegralModel.mem_minimalPrimes_or_isMaximal_of_mem_chartAlgFin A₀ ϖ₀ hϖ₀ ↥K₀ ↥F₀ g⁻¹ htg' hFDg' hsepg'
          yη.asIdeal hϖη with hminη | hmaxη
      · rcases TwoChartIntegralModel.mem_minimalPrimes_or_isMaximal_of_mem_chartAlgFin A₀ ϖ₀ hϖ₀ ↥K₀ ↥F₀ g⁻¹ htg' hFDg' hsepg'
            yy.asIdeal hϖyy with hminy | hmaxy
        · exfalso
          have hge : yy.asIdeal ≤ yη.asIdeal := hminy.2 ⟨yη.isPrime, hminη.1.2⟩ hle
          exact hne' (PrimeSpectrum.ext (le_antisymm hle hge))
        · exact TwoChartIntegralModel.eq_of_specializes_of_isMaximal_of_mem_chart A₀ ϖ₀ hϖ₀ ↥K₀ ↥F₀ g htg hFDg hsepg
            y (Or.inr ⟨yy, hyy, hmaxy, hϖyy⟩) z hyz
      · exfalso
        have heq : yη.asIdeal = yy.asIdeal := hmaxη.eq_of_le yy.isPrime.ne_top hle
        exact hne' (PrimeSpectrum.ext heq)
  ·
    haveI : IsLocallyNoetherian (TwoChartIntegralModel A₀ ↥F₀ g) := by
      first
      | exact inferInstance
      | exact LocallyOfFiniteType.isLocallyNoetherian (toBase A₀ ↥F₀ g)
    haveI : Algebra.IsAlgebraic ↥(Algebra.adjoin A₀ ({g} : Set ↥F₀)) ↥F₀ :=
      Algebra.IsAlgebraic.adjoin_singleton_of_finiteDimensional_intermediateField_adjoin_of_isFractionRing A₀ ↥K₀ ↥F₀ g hFDg
    intro O' _hO'top hO'inv
    have hunit : ∀ a : A₀, IsUnit a → algebraMap A₀ ↥F₀ a ∈ O' := by
      intro a ha
      obtain ⟨u, rfl⟩ := ha
      have hb : ((u⁻¹ : A₀ˣ) : A₀) ≠ 0 := Units.ne_zero _
      have hinv := hO'inv _ hb
      have hmul : algebraMap A₀ ↥F₀ ((u⁻¹ : A₀ˣ) : A₀) * algebraMap A₀ ↥F₀ (u : A₀) = 1 := by
        rw [← map_mul, Units.inv_mul, map_one]
      have : algebraMap A₀ ↥F₀ (u : A₀) = (algebraMap A₀ ↥F₀ ((u⁻¹ : A₀ˣ) : A₀))⁻¹ :=
        (eq_inv_of_mul_eq_one_right hmul)
      rw [this]
      rw [halgF]
      exact hinv
    have hAO : ∀ a : A₀, algebraMap A₀ ↥F₀ a ∈ O' := by
      intro a
      rcases IsLocalRing.isUnit_or_isUnit_one_sub_self a with ha | ha
      · exact hunit a ha
      · have h1 := hunit _ ha
        have : algebraMap A₀ ↥F₀ a = 1 - algebraMap A₀ ↥F₀ (1 - a) := by
          rw [map_sub, map_one, sub_sub_cancel]
        rw [this]
        exact sub_mem (one_mem _) h1
    have hAO' : ∀ a : A₀, algebraMap A₀ ↥F₀ a ≠ 0 → (algebraMap A₀ ↥F₀ a)⁻¹ ∈ O' := by
      intro a ha
      have ha0 : a ≠ 0 := fun h => ha (by rw [h, map_zero])
      rw [halgF]
      exact hO'inv a ha0
    obtain ⟨x, hx⟩ :=
      AlgebraicGeometry.exists_localRing_eq_valuationSubring_of_isIntegrallyClosed_of_universallyClosed
        (toBase A₀ ↥F₀ g) (fun y => TwoChartIntegralModel.isIntegrallyClosed_stalk A₀ ↥F₀ g y) φ hφbase g O' hAO hAO'
    exact ⟨x, hx.symm⟩
  ·

    intro O hO
    have hgauss := (hComp O (hRO O hO) (hϖO O hO)).mpr hO

    have hndvd : ∀ p : Polynomial A₀, (∃ i, IsUnit (p.coeff i)) → ¬ (Polynomial.C ϖ₀ ∣ p) := by
      rintro p ⟨i, hi⟩ hdvd
      rw [Polynomial.C_dvd_iff_dvd_coeff] at hdvd
      have hϖunit : IsUnit ϖ₀ := isUnit_of_dvd_unit (hdvd i) hi
      have hmem : ϖ₀ ∈ maximalIdeal A₀ := by rw [hϖ₀]; exact Ideal.mem_span_singleton_self ϖ₀
      exact (IsLocalRing.mem_maximalIdeal _).mp hmem hϖunit
    have hgeo_g : g ∈ O ∧ ∀ p : Polynomial A₀, (∃ i, IsUnit (p.coeff i)) →
        ∃ hO' : Polynomial.eval₂ (algebraMap A₀ ↥F₀) g p ∈ O, IsUnit (⟨_, hO'⟩ : ↥O) := by
      refine ⟨?_, ?_⟩
      · have h := (hgauss Polynomial.X (hndvd Polynomial.X ⟨1, by simp⟩)).1
        simpa [Polynomial.aeval_X] using h
      · intro p hp
        obtain ⟨h1, h2⟩ := hgauss p (hndvd p hp)
        have heq : Polynomial.eval₂ (algebraMap A₀ ↥F₀) g p = Polynomial.aeval g p := by
          rw [Polynomial.aeval_def]
        have hne : Polynomial.aeval g p ≠ 0 := by
          intro h0
          obtain ⟨i, hi⟩ := hp
          have hp0 : p ≠ 0 := fun hp0 => by
            rw [hp0, Polynomial.coeff_zero] at hi
            exact not_isUnit_zero hi
          exact htg ⟨p, hp0, by rwa [Polynomial.aeval_def] at h0⟩
        refine ⟨heq ▸ h1, ?_⟩
        refine isUnit_iff_exists_inv.mpr ⟨⟨(Polynomial.aeval g p)⁻¹, h2⟩, ?_⟩
        ext
        simp [heq, mul_inv_cancel₀ hne]
    obtain ⟨_, -, -, -, -, -, hrest⟩ :=
      ValuationSubring.inv_mem_and_chartAlg_le_and_over_gauss_and_isDiscreteValuationRing_of_forall_isUnit_polynomialEval2
        A₀ ϖ₀ hϖ₀ ↥K₀ ↥F₀ O (hRO O hO) (hϖO O hO) g hgeo_g.1 hgeo_g.2
    obtain ⟨-, 𝔭, h𝔭min, h𝔭nmax, h𝔭O, hOloc⟩ := hrest hFDg hsepg
    haveI h𝔭prime : 𝔭.IsPrime := h𝔭min.1.1
    let y : ↥(XFin A₀ ↥F₀ g) := ⟨𝔭, h𝔭prime⟩
    refine ⟨(ιFin A₀ ↥F₀ g).base y, ?_, ?_, ?_⟩
    ·
      have hcomp : (toBase A₀ ↥F₀ g).base ((ιFin A₀ ↥F₀ g).base y) = (ιFin A₀ ↥F₀ g ≫ toBase A₀ ↥F₀ g).base y := by
        first
        | rfl
        | simp
      rw [hcomp, TwoChartIntegralModel.ιFin_toBase]
      apply PrimeSpectrum.ext
      have h1 : ((Spec.map (CommRingCat.ofHom (algebraMap A₀ ↥(chartAlgFin A₀ ↥F₀ g)))).base y).asIdeal =
          Ideal.comap (algebraMap A₀ ↥(chartAlgFin A₀ ↥F₀ g)) y.asIdeal := by
        first
        | rfl
        | simp
      have h2 : (closedPoint A₀).asIdeal = maximalIdeal A₀ := by
        first
        | rfl
        | simp
      rw [h1, h2]
      symm
      refine (IsLocalRing.maximalIdeal.isMaximal A₀).eq_of_le ?_ ?_
      · exact Ideal.IsPrime.ne_top (Ideal.IsPrime.comap _)
      · rw [hϖ₀, Ideal.span_singleton_le_iff_mem, Ideal.mem_comap]
        exact h𝔭min.1.2 (Ideal.mem_span_singleton_self _)
    ·
      obtain ⟨𝔮, h𝔮max, h𝔭𝔮⟩ := Ideal.exists_le_maximal 𝔭 h𝔭prime.ne_top
      have h𝔮ne : 𝔮 ≠ 𝔭 := fun h => h𝔭nmax (h ▸ h𝔮max)
      let y' : ↥(XFin A₀ ↥F₀ g) := ⟨𝔮, h𝔮max.isPrime⟩
      have hyy' : y ⤳ y' := by
        first
        | exact (PrimeSpectrum.le_iff_specializes y y').mp h𝔭𝔮
        | exact PrimeSpectrum.le_iff_specializes.mp h𝔭𝔮
      have hcont : Continuous (ιFin A₀ ↥F₀ g).base := by
        first
        | exact (ιFin A₀ ↥F₀ g).base.hom.continuous
        | exact (ιFin A₀ ↥F₀ g).continuous
        | continuity
      have hinjι : Function.Injective (ιFin A₀ ↥F₀ g).base := by
        first
        | exact (ιFin A₀ ↥F₀ g).isOpenEmbedding.injective
        | exact (ιFin A₀ ↥F₀ g).isOpenEmbedding.inj
      refine ⟨(ιFin A₀ ↥F₀ g).base y', hyy'.map hcont, ?_⟩
      intro h
      have hyeq : y' = y := hinjι h
      exact h𝔮ne (congrArg PrimeSpectrum.asIdeal hyeq)
    ·
      ext f'
      rw [MFVR.localRing_ιFin_iff A₀ ↥F₀ g φ hφFin y f', ValuationSubring.mem_toSubring]
      exact (hOloc f').symm
  ·

    intro η hηsp hηnc
    have hϖη : ϖ₀ ∈ ((toBase A₀ ↥F₀ g).base η).asIdeal := by
      rw [hηsp]
      show ϖ₀ ∈ maximalIdeal A₀
      rw [hϖ₀]; exact Ideal.mem_span_singleton_self ϖ₀
    have hprime : Prime ϖ₀ :=
      ((IsDiscreteValuationRing.irreducible_iff_uniformizer ϖ₀).mpr hϖ₀).prime
    obtain ⟨W, -, hWfin, -, hWϖ, hWgauss, hWcenFin, hWcenInf⟩ :=
      TwoChartIntegralModel.exists_valuationSubring_forall_mem_nonunits_mem_asIdeal_of_mem_toBase
        A₀ ↥K₀ ↥F₀ g htg hFDg hsepg ϖ₀ hprime η hϖη
    have hRW : ∀ a : A₀, algebraMap A₀ ↥F₀ a ∈ W := fun a => by
      have := hWfin (algebraMap A₀ ↥(chartAlgFin A₀ ↥F₀ g) a)
      simpa using this
    have hWV : W ∈ V := (hComp W hRW hWϖ).mp hWgauss
    refine ⟨W, hWV, ?_⟩

    have hgeo_W : g ∈ W ∧ ∀ p : Polynomial A₀, (∃ i, IsUnit (p.coeff i)) →
        ∃ hO' : Polynomial.eval₂ (algebraMap A₀ ↥F₀) g p ∈ W, IsUnit (⟨_, hO'⟩ : ↥W) := by
      have hndvd : ∀ p : Polynomial A₀, (∃ i, IsUnit (p.coeff i)) → ¬ (Polynomial.C ϖ₀ ∣ p) := by
        rintro p ⟨i, hi⟩ hdvd
        rw [Polynomial.C_dvd_iff_dvd_coeff] at hdvd
        have hϖunit : IsUnit ϖ₀ := isUnit_of_dvd_unit (hdvd i) hi
        have hmem : ϖ₀ ∈ maximalIdeal A₀ := by rw [hϖ₀]; exact Ideal.mem_span_singleton_self ϖ₀
        exact (IsLocalRing.mem_maximalIdeal _).mp hmem hϖunit
      refine ⟨?_, ?_⟩
      · have h := (hWgauss Polynomial.X (hndvd Polynomial.X ⟨1, by simp⟩)).1
        simpa [Polynomial.aeval_X] using h
      · intro p hp
        obtain ⟨h1, h2⟩ := hWgauss p (hndvd p hp)
        have heq : Polynomial.eval₂ (algebraMap A₀ ↥F₀) g p = Polynomial.aeval g p := by
          rw [Polynomial.aeval_def]
        have hne : Polynomial.aeval g p ≠ 0 := by
          intro h0
          obtain ⟨i, hi⟩ := hp
          have hp0 : p ≠ 0 := fun hp0 => by
            rw [hp0, Polynomial.coeff_zero] at hi
            exact not_isUnit_zero hi
          exact htg ⟨p, hp0, by rwa [Polynomial.aeval_def] at h0⟩
        refine ⟨heq ▸ h1, ?_⟩
        refine isUnit_iff_exists_inv.mpr ⟨⟨(Polynomial.aeval g p)⁻¹, h2⟩, ?_⟩
        ext
        simp [heq, mul_inv_cancel₀ hne]
    obtain ⟨_, -, -, -, -, -, hrestW⟩ :=
      ValuationSubring.inv_mem_and_chartAlg_le_and_over_gauss_and_isDiscreteValuationRing_of_forall_isUnit_polynomialEval2
        A₀ ϖ₀ hϖ₀ ↥K₀ ↥F₀ W hRW hWϖ g hgeo_W.1 hgeo_W.2
    obtain ⟨-, 𝔭W, h𝔭Wmin, -, h𝔭WW, hWloc⟩ := hrestW hFDg hsepg

    rcases TwoChartIntegralModel.mem_range_ιFin_or_mem_range_ιInf A₀ ↥F₀ g η with ⟨yη, hyη⟩ | ⟨yη', hyη'⟩
    ·
      have hϖyη : algebraMap A₀ ↥(chartAlgFin A₀ ↥F₀ g) ϖ₀ ∈ yη.asIdeal := by
        apply hWcenFin yη hyη
        simpa using hWϖ
      have hcen : 𝔭W ≤ yη.asIdeal := fun b hb => hWcenFin yη hyη b ((h𝔭WW b).mp hb)
      rcases TwoChartIntegralModel.mem_minimalPrimes_or_isMaximal_of_mem_chartAlgFin A₀ ϖ₀ hϖ₀ ↥K₀ ↥F₀ g htg hFDg hsepg
          yη.asIdeal hϖyη with hmin | hmax
      ·
        have heq : 𝔭W = yη.asIdeal :=
          le_antisymm hcen (hmin.2 ⟨h𝔭Wmin.1.1, h𝔭Wmin.1.2⟩ hcen)
        ext f'
        rw [← hyη, MFVR.localRing_ιFin_iff A₀ ↥F₀ g φ hφFin yη f', ValuationSubring.mem_toSubring, hWloc f', heq]
      ·
        exfalso
        obtain ⟨z, hz, hne⟩ := hηnc
        exact hne (TwoChartIntegralModel.eq_of_specializes_of_isMaximal_of_mem_chart A₀ ϖ₀ hϖ₀ ↥K₀ ↥F₀ g htg hFDg hsepg
          η (Or.inl ⟨yη, hyη, hmax, hϖyη⟩) z hz)
    ·

      have hgeo_W' : g⁻¹ ∈ W ∧ ∀ p : Polynomial A₀, (∃ i, IsUnit (p.coeff i)) →
          ∃ hO' : Polynomial.eval₂ (algebraMap A₀ ↥F₀) g⁻¹ p ∈ W, IsUnit (⟨_, hO'⟩ : ↥W) := by
        have hgX := hWgauss Polynomial.X (hndvd0 Polynomial.X ⟨1, by simp⟩)
        have hgW : g ∈ W := by simpa [Polynomial.aeval_X] using hgX.1
        have hginvW : g⁻¹ ∈ W := by simpa [Polynomial.aeval_X] using hgX.2
        refine ⟨hginvW, ?_⟩
        rintro p ⟨i₀, hi₀⟩
        have hp0 : p ≠ 0 := fun hp0 => by
          rw [hp0, Polynomial.coeff_zero] at hi₀
          exact not_isUnit_zero hi₀

        have hrev : ¬ (Polynomial.C ϖ₀ ∣ p.reverse) := by
          intro hdvd
          rw [Polynomial.C_dvd_iff_dvd_coeff] at hdvd
          have hle : i₀ ≤ p.natDegree := Polynomial.le_natDegree_of_ne_zero hi₀.ne_zero
          have := hdvd (Polynomial.revAt p.natDegree i₀)
          rw [Polynomial.coeff_reverse, Polynomial.revAt_invol] at this
          exact hϖnu (isUnit_of_dvd_unit this hi₀)
        obtain ⟨h1, h2⟩ := hWgauss p.reverse hrev
        haveI : Invertible (g⁻¹ : ↥F₀) := invertibleOfNonzero hg0'
        have hid : Polynomial.eval₂ (algebraMap A₀ ↥F₀) g p.reverse * (g⁻¹) ^ p.natDegree =
            Polynomial.eval₂ (algebraMap A₀ ↥F₀) g⁻¹ p := by
          have := Polynomial.eval₂_reverse_mul_pow (algebraMap A₀ ↥F₀) (g⁻¹ : ↥F₀) p
          rwa [invOf_eq_inv, inv_inv] at this
        have heq : Polynomial.eval₂ (algebraMap A₀ ↥F₀) g p.reverse = Polynomial.aeval g p.reverse := by
          rw [Polynomial.aeval_def]
        have h1' : Polynomial.eval₂ (algebraMap A₀ ↥F₀) g p.reverse ∈ W := heq ▸ h1
        have hmem : Polynomial.eval₂ (algebraMap A₀ ↥F₀) g⁻¹ p ∈ W := by
          rw [← hid]; exact mul_mem h1' (pow_mem hginvW _)
        refine ⟨hmem, ?_⟩
        have hne : Polynomial.aeval g p.reverse ≠ 0 := by
          intro h0
          have hr0 : p.reverse ≠ 0 := by
            intro hr; exact hp0 (Polynomial.reverse_eq_zero.mp hr)
          exact htg ⟨p.reverse, hr0, by rwa [Polynomial.aeval_def] at h0⟩
        have hu1 : IsUnit (⟨Polynomial.eval₂ (algebraMap A₀ ↥F₀) g p.reverse, h1'⟩ : ↥W) := by
          refine isUnit_iff_exists_inv.mpr ⟨⟨(Polynomial.aeval g p.reverse)⁻¹, h2⟩, ?_⟩
          ext
          simp [heq, mul_inv_cancel₀ hne]
        have hu2 : IsUnit (⟨g⁻¹, hginvW⟩ : ↥W) := by
          refine isUnit_iff_exists_inv.mpr ⟨⟨g, hgW⟩, ?_⟩
          ext
          simp [inv_mul_cancel₀ hg0]
        have hprod : (⟨Polynomial.eval₂ (algebraMap A₀ ↥F₀) g⁻¹ p, hmem⟩ : ↥W) =
            ⟨Polynomial.eval₂ (algebraMap A₀ ↥F₀) g p.reverse, h1'⟩ * ⟨g⁻¹, hginvW⟩ ^ p.natDegree := by
          apply Subtype.ext
          first
          | (simp only [Subring.coe_mul, SubmonoidClass.coe_pow]; exact hid.symm)
          | (push_cast; exact hid.symm)
          | (simp; exact hid.symm)
          | exact hid.symm
        rw [hprod]
        exact hu1.mul (hu2.pow _)
      obtain ⟨_, -, -, -, -, -, hrestW'⟩ :=
        ValuationSubring.inv_mem_and_chartAlg_le_and_over_gauss_and_isDiscreteValuationRing_of_forall_isUnit_polynomialEval2
          A₀ ϖ₀ hϖ₀ ↥K₀ ↥F₀ W hRW hWϖ g⁻¹ hgeo_W'.1 hgeo_W'.2
      obtain ⟨-, 𝔭W', h𝔭W'min, -, h𝔭W'W, hWloc'⟩ := hrestW' hFDg' hsepg'
      have hϖyη' : algebraMap A₀ ↥(chartAlgInf A₀ ↥F₀ g) ϖ₀ ∈ yη'.asIdeal := by
        apply hWcenInf yη' hyη'
        simpa using hWϖ
      have hcen' : 𝔭W' ≤ yη'.asIdeal := fun b hb => hWcenInf yη' hyη' b ((h𝔭W'W b).mp hb)
      rcases TwoChartIntegralModel.mem_minimalPrimes_or_isMaximal_of_mem_chartAlgFin A₀ ϖ₀ hϖ₀ ↥K₀ ↥F₀ g⁻¹ htg' hFDg' hsepg'
          yη'.asIdeal hϖyη' with hmin' | hmax'
      · have heq' : 𝔭W' = yη'.asIdeal :=
          le_antisymm hcen' (hmin'.2 ⟨h𝔭W'min.1.1, h𝔭W'min.1.2⟩ hcen')
        ext f'
        rw [← hyη', MFVR.localRing_ιInf_iff A₀ ↥F₀ g φ hφInf yη' f', ValuationSubring.mem_toSubring, hWloc' f', heq']
      · exfalso
        obtain ⟨z, hz, hne⟩ := hηnc
        exact hne (TwoChartIntegralModel.eq_of_specializes_of_isMaximal_of_mem_chart A₀ ϖ₀ hϖ₀ ↥K₀ ↥F₀ g htg hFDg hsepg
          η (Or.inr ⟨yη', hyη', hmax', hϖyη'⟩) z hz)

end S_AlgebraicGeometry_exists_normalProperModel_of_valuationSubrings_of_form_of_isAlgebraic_relDimOne_genComplete_henselian
end P2MW
export P2MW.S_AlgebraicGeometry_exists_normalProperModel_of_valuationSubrings_of_form_of_isAlgebraic_relDimOne_genComplete_henselian (solution)
