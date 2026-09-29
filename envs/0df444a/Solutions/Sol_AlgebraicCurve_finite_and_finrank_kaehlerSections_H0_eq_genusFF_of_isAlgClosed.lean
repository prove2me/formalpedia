-- Prove2me | solution 1 for AlgebraicCurve.finite_and_finrank_kaehlerSections_H0_eq_genusFF_of_isAlgClosed
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:02.4153+00:00
-- url     : https://prove2.me/submissions/6048d8e1-facc-5af5-94db-07b8053ad6ba

import Mathlib
import Definitions.Def_AlgebraicCurve_Repartitions
import Definitions.Def_AlgebraicCurve_CurveModel
import Definitions.Def_AlgebraicCurve_IsCurveOver
import Definitions.Def_AlgebraicCurve_CanonicalDivisor
import Definitions.Def_AlgebraicCurve_RegularDifferentials
import Definitions.Def_AlgebraicCurve_KaehlerToFunctionField
import Definitions.Def_AlgebraicCurve_PlacesOf
import Definitions.Def_AlgebraicGeometry_TwoAffineOpenCoverKaehler
import Theorems.Thm_AlgebraicGeometry_Scheme_TwoAffineOpenCover_exists_linearEquiv_kaehlerSectionsH0_regularDifferentials_apply_eq_kaehlerToFunctionField
import Theorems.Thm_AlgebraicCurve_finite_and_finrank_regularDifferentials_eq_genus
import Theorems.Thm_AlgebraicCurve_genus_eq_genusFF
import Theorems.Thm_AlgebraicCurve_hasCanonicalDivisor_of_isCurveOver
import Theorems.Thm_AlgebraicCurve_dCoordGenerates_of_isCurveOver
import Theorems.Thm_AlgebraicCurve_functionFieldRiemannRoch_of_isAlgClosed_of_transcendental
import Theorems.Thm_AlgebraicCurve_weilDualityAdelic_of_functionFieldRiemannRoch_of_stichtenothGenusExists
import Theorems.Thm_AlgebraicCurve_stichtenothGenusExists_of_isCurveOver
import Theorems.Thm_AlgebraicCurve_exists_transcendental_isSeparable_of_finrank_kaehlerDifferential_eq_one
import Theorems.Thm_AlgebraicCurve_isCurveOver_of_isIntegral_of_smoothOfRelativeDimension_one
import Theorems.Thm_AlgebraicCurve_essFiniteType_functionField
import Theorems.Thm_AlgebraicGeometry_not_isAffine_of_isProper_of_smoothOfRelativeDimension_one
import Theorems.Thm_AlgebraicCurve_constantsAreBase_of_deg_eq_one
import Theorems.Thm_AlgebraicCurve_placesOf_union_eq_univ_of_sup_eq_top
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicCurve_finite_and_finrank_kaehlerSections_H0_eq_genusFF_of_isAlgClosed
p2m_attr_erase "instance" "AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions AlgebraicCurve.instHasLocalResidue_of_hasCanonicalLocalResidueK AlgebraicCurve.instHasCanonicalLocalResidueK_of_hasCanonicalLocalResidueKStar AlgebraicCurve.Place.kw_ffgc_finiteDimensional_adicCompletion instAlgebraSubtypeMemValuationSubring_definitions AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersIntegersCompletion ModularCurve.KwF4gRRTate.instAlgebraKAdicCompletionIntegers AlgebraicCurve.Place.kw_ffgc_continuousSMul_adicCompletionComap AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersCompletionCompletion IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions AlgebraicCurve.instHasCanonicalLocalResidueK AlgebraicCurve.Place.instAlgebra_restrictResidueField AlgebraicCurve.Place.instIsScalarTower_restrictResidueField AlgebraicCurve.instHasLocalResidue AlgebraicCurve.HasSeparableResidue.of_perfectField_of_isCurveOver AlgebraicCurve.HasSeparableResidue.of_perfectField AlgebraicCurve.Place.instIsLocalHom_restrictSubringHom AlgebraicCurve.instHasCanonicalLocalResidueKStar ModularCurve.KwNo6Pin.isLocalRing_completion AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.SemilinearAut.instDistribMulActionSubtypeProdRingAutMemSubgroupPic0 AlgebraicCurve.SemilinearAut.instDistribMulActionSubtypeProdRingAutMemSubgroupDivisor AlgebraicCurve.Pic0.instModuleZModTorsion AlgebraicCurve.SemilinearAut.instSMulSubtypeProdRingAutMemSubgroupPlace AlgebraicCurve.SemilinearAut.instDistribMulActionTorsion AlgebraicCurve.SemilinearAut.instSMulSubtypeProdRingAutMemSubgroupPic0 AlgebraicCurve.SemilinearAut.instSMulTorsion AlgebraicCurve.SemilinearAut.instMulActionSubtypeProdRingAutMemSubgroupPlace AlgebraicCurve.SemilinearAut.instSMulCommClassZModTorsion AlgebraicCurve.SemilinearAut.instMulSemiringActionSubtypeProdRingAutMemSubgroup instDecEqAlgebraicClosureRat"
p2m_attr_erase "instance" "WeierstrassCurve.Affine.Point.instDistribMulActionAlgEquiv WeierstrassCurve.Affine.Point.instModuleZModTorsionBy WeierstrassCurve.Affine.Point.instSMulTorsionBy WeierstrassCurve.Affine.Point.instDistribMulActionTorsionBy WeierstrassCurve.Affine.Point.instSMulAlgEquiv WeierstrassCurve.Affine.Point.instSMulCommClassAlgEquivZModTorsionBy"
p2m_attr_erase "simp" "AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.sizeOf_spec AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.injEq AlgebraicCurve.adeleSingle_coe AlgebraicCurve.kaehlerResidueTermKFam_apply AlgebraicCurve.Place.LocalResidueData.mk.injEq AlgebraicCurve.Place.LocalResidueData.mk.sizeOf_spec AlgebraicCurve.Place.kw_ffgc_adicCompletionComapIntegers_coe AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.sizeOf_spec AlgebraicCurve.Place.mem_simplePoleSubmodule AlgebraicCurve.Place.coe_uniformizerSubring ModularCurve.Lg37.Lg37CompletionSection.mk.injEq AlgebraicCurve.Place.CoefficientFieldSection.mk.injEq AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.injEq ModularCurve.Lg37.Lg37CompletionSection.mk.sizeOf_spec AlgebraicCurve.Place.CoefficientFieldSection.mk.sizeOf_spec AlgebraicCurve.Place.poleSubmodule_one AlgebraicCurve.Place.mem_poleSubmodule AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal AlgebraicCurve.IsFrobeniusEndo.frobNormRingHom_apply ModularCurve.frobeniusPushforwardGeomLevelPic0_mk ModularCurve.coe_frobeniusGeomLevelEquiv_apply ModularCurve.coe_frobeniusPushforwardGeomLevelDegZero ModularCurve.heckeFibreGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusGeomLevel_apply_coe ModularCurve.frobeniusPullbackGeomLevelPic0OfIsCurveOver_mk ModularCurve.coe_heckeFibreGeomLevelDegZero ModularCurve.coe_frobeniusPullbackGeomLevelDegZero ModularCurve.frobeniusPullbackGeomLevelPic0_mk ModularCurve.frobeniusPullbackGeomLevel_single ModularCurve.heckeFibreGeomLevelPic0_mk ModularCurve.frobeniusPushforwardGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusPushforwardGeomLevel_single"
p2m_attr_erase "simp" "ModularCurve.qExpandAlgC_apply AlgebraicCurve.Divisor.degree_pushforwardAlong AlgebraicCurve.Pic0.coe_degZeroCorrespondence AlgebraicCurve.Place.mem_fiberAlong AlgebraicCurve.SemilinearAut.toRingAut_inv AlgebraicCurve.SemilinearAut.smul_def AlgebraicCurve.SemilinearAut.smul_single AlgebraicCurve.SemilinearAut.smul_toValuationSubring AlgebraicCurve.SemilinearAut.baseAut_inv AlgebraicCurve.SemilinearAut.baseAut_ofAlgAut AlgebraicCurve.SemilinearAut.toRingAut_ofAlgAut AlgebraicCurve.SemilinearAut.torsionRep_apply AlgebraicCurve.SemilinearAut.toRingAut_one AlgebraicCurve.SemilinearAut.deg_smul AlgebraicCurve.SemilinearAut.degree_smul AlgebraicCurve.SemilinearAut.coe_degZeroSMulHom AlgebraicCurve.SemilinearAut.baseAut_mul AlgebraicCurve.SemilinearAut.coe_smulValuationSubringEquiv_apply AlgebraicCurve.SemilinearAut.baseAut_one AlgebraicCurve.SemilinearAut.ofAlgAut_smul AlgebraicCurve.SemilinearAut.coe_torsion_smul AlgebraicCurve.SemilinearAut.toRingAut_mul AlgebraicCurve.coe_frobeniusPushforwardDegZero AlgebraicCurve.IsFrobeniusEndo.coe_frobeniusPullbackDegZero ModularCurve.jqNModC_one ModularCurve.qExpand_coeff_mul ModularCurve.qExpandₐ_apply ModularCurve.jqN_one ModularCurve.qExpand_single ModularCurve.dedekindPsi_one ModularCurve.ModularPolynomialData.mk.sizeOf_spec ModularCurve.evalAtJ_X ModularCurve.ModularPolynomialData.mk.injEq ModularCurve.constantCoeff_jNum ModularCurve.constantCoeff_eisenstein4 ModularCurve.qExpand_C ModularCurve.coeff_jq_neg_one ModularCurve.constantCoeff_jNumQ ModularCurve.reduceModBivar_C_X ModularCurve.laurentMap_coeff"
p2m_attr_erase "simp" "ModularCurve.reduceModBivar_X ModularCurve.laurentMap_single ModularCurve.evalAtJInt_X ModularCurve.evalAtJMod_X ModularCurve.jqNMod_one ModularCurve.aeval_heckeGen ModularCurve.coe_mTorsionGaloisRep_apply ModularCurve.eisensteinSystem_of_dvd ModularCurve.eisensteinSystem_of_not_dvd FreyPackage.mk.sizeOf_spec FreyPackage.mk.injEq WeierstrassCurve.Affine.Point.galoisRepModuleEnd_apply AlgebraicCurve.TranscendenceTower.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.injEq AlgebraicCurve.TranscendenceTower.mk.injEq AlgebraicCurve.PoleDivisorPackage.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.sizeOf_spec AlgebraicCurve.PoleDivisorPackage.mk.injEq"

set_option autoImplicit false

open CategoryTheory AlgebraicGeometry IntermediateField

universe u

namespace AlgebraicCurve
p2m_export "AlgebraicCurve" "genusFF Place baseToFunctionField IsCurveOver IsCurveOver.finrank_kaehler IsCurveOver.deg_eq_one_of_isAlgClosed HasCanonicalDivisor genus finite_and_finrank_regularDifferentials_eq_genus genus_eq_genusFF WeilDualityAdelic FunctionFieldRiemannRoch ConstantsAreBase hasCanonicalDivisor_of_isCurveOver dCoordGenerates_of_isCurveOver functionFieldRiemannRoch_of_isAlgClosed_of_transcendental weilDualityAdelic_of_functionFieldRiemannRoch_of_stichtenothGenusExists stichtenothGenusExists_of_isCurveOver exists_transcendental_isSeparable_of_finrank_kaehlerDifferential_eq_one isCurveOver_of_isIntegral_of_smoothOfRelativeDimension_one essFiniteType_functionField constantsAreBase_of_deg_eq_one placesOf_union_eq_univ_of_sup_eq_top"
p2m_open "AlgebraicCurve"

theorem ne_top_of_isAffineOpen'' {C : Scheme.{u}} (hC : ¬ IsAffine C) {U : C.Opens}
    (hU : IsAffineOpen U) : U ≠ ⊤ := by
  intro h
  apply hC
  have hT : IsAffineOpen (⊤ : C.Opens) := h ▸ hU
  haveI : IsAffine (⊤ : C.Opens) := hT
  exact IsAffine.of_isIso C.topIso.inv

end AlgebraicCurve

open _root_.AlgebraicCurve _root_.P2MW.S_AlgebraicCurve_finite_and_finrank_kaehlerSections_H0_eq_genusFF_of_isAlgClosed.AlgebraicCurve in
theorem solution {K : Type u} [Field K] [IsAlgClosed K] {C : Scheme.{u}} (𝒱 : C.TwoAffineOpenCover)
    (c : C ⟶ Spec (CommRingCat.of K)) [IsIntegral C] [IsProper c] [SmoothOfRelativeDimension 1 c] :
    letI := (AlgebraicCurve.baseToFunctionField c).toAlgebra
    Module.Finite K (𝒱.kaehlerSections c).H0 ∧
      Module.finrank K (𝒱.kaehlerSections c).H0 = AlgebraicCurve.genusFF K C.functionField := by
  letI := (AlgebraicCurve.baseToFunctionField c).toAlgebra

  haveI hcurve : IsCurveOver K C.functionField :=
    isCurveOver_of_isIntegral_of_smoothOfRelativeDimension_one c (RingEquiv.refl _) (fun _ => rfl)
  haveI : Algebra.EssFiniteType K C.functionField := essFiniteType_functionField c
  haveI : HasCanonicalDivisor (K := K) (F := C.functionField) := hasCanonicalDivisor_of_isCurveOver
  haveI : ∀ v : Place K C.functionField, v.DCoordGenerates := dCoordGenerates_of_isCurveOver

  have hNA := not_isAffine_of_isProper_of_smoothOfRelativeDimension_one c
  have hne0 : 𝒱.U0 ≠ ⊤ := ne_top_of_isAffineOpen'' hNA 𝒱.isAffineOpen_U0
  have hne1 : 𝒱.U1 ≠ ⊤ := ne_top_of_isAffineOpen'' hNA 𝒱.isAffineOpen_U1
  haveI : Nonempty 𝒱.U0 := by
    by_contra h
    apply hne1
    have h0 : 𝒱.U0 = ⊥ := by
      rw [← TopologicalSpace.Opens.coe_eq_empty, ← Set.not_nonempty_iff_eq_empty]
      exact fun ⟨x, hx⟩ => h ⟨⟨x, hx⟩⟩
    have := 𝒱.sup_eq_top
    rwa [h0, bot_sup_eq] at this
  haveI : Nonempty 𝒱.U1 := by
    by_contra h
    apply hne0
    have h1 : 𝒱.U1 = ⊥ := by
      rw [← TopologicalSpace.Opens.coe_eq_empty, ← Set.not_nonempty_iff_eq_empty]
      exact fun ⟨x, hx⟩ => h ⟨⟨x, hx⟩⟩
    have := 𝒱.sup_eq_top
    rwa [h1, sup_bot_eq] at this
  obtain ⟨-, ⟨v₀, -⟩, -⟩ :=
    placesOf_union_eq_univ_of_sup_eq_top c 𝒱.U0 𝒱.U1 𝒱.sup_eq_top hne0 hne1

  have hC : ConstantsAreBase K C.functionField :=
    constantsAreBase_of_deg_eq_one v₀ (IsCurveOver.deg_eq_one_of_isAlgClosed v₀)
  haveI : Algebra.Transcendental K C.functionField := by
    rw [Algebra.transcendental_iff_not_isAlgebraic]
    intro halg
    haveI : Algebra.IsIntegral K C.functionField := Algebra.isAlgebraic_iff_isIntegral.mp halg
    apply v₀.ne_top'
    refine eq_top_iff.2 fun x _ => ?_
    obtain ⟨a, rfl⟩ := (IsAlgClosed.algebraMap_bijective_of_isIntegral (k := K) (K := C.functionField)).2 x
    exact v₀.algebraMap_mem' a

  obtain ⟨t, htr, hfd, -⟩ := exists_transcendental_isSeparable_of_finrank_kaehlerDifferential_eq_one
    (K := K) (F := C.functionField) IsCurveOver.finrank_kaehler
  have hRR : FunctionFieldRiemannRoch K C.functionField :=
    functionFieldRiemannRoch_of_isAlgClosed_of_transcendental htr hfd
  have hWDA : WeilDualityAdelic K C.functionField :=
    weilDualityAdelic_of_functionFieldRiemannRoch_of_stichtenothGenusExists hRR
      (stichtenothGenusExists_of_isCurveOver hC)

  obtain ⟨eΩ, -⟩ :=
    AlgebraicGeometry.Scheme.TwoAffineOpenCover.exists_linearEquiv_kaehlerSectionsH0_regularDifferentials_apply_eq_kaehlerToFunctionField 𝒱 c
  obtain ⟨hfin, hrk⟩ := finite_and_finrank_regularDifferentials_eq_genus (K := K) (F := C.functionField)
  haveI := hfin
  refine ⟨Module.Finite.equiv eΩ.symm, ?_⟩
  rw [eΩ.finrank_eq, hrk]
  exact genus_eq_genusFF hRR hWDA hC

end S_AlgebraicCurve_finite_and_finrank_kaehlerSections_H0_eq_genusFF_of_isAlgClosed
end P2MW
export P2MW.S_AlgebraicCurve_finite_and_finrank_kaehlerSections_H0_eq_genusFF_of_isAlgClosed (solution)
