-- Prove2me | solution 1 for AlgebraicGeometry.RelPicard.isAlgEquivZero_of_finrank_H1_tensorPow_add_two_le_of_twoGluedSmoothCurves
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:03.589526+00:00
-- url     : https://prove2.me/submissions/24a1e6c6-ab08-528f-8e5c-0cef5d8a80c6

import Mathlib
import Definitions.Def_AlgebraicGeometry_NeronModelPropertyBundleCarrier
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import Definitions.Def_AlgebraicGeometry_RelPicardAlgEquivZeroCut
import Definitions.Def_AlgebraicGeometry_TwoAffineOpenCover
import Definitions.Def_AlgebraicGeometry_TwoChartCechSectionsOf
import Definitions.Def_SheafOfModules_Monoidal
import Definitions.Def_AlgebraicGeometry_ModulesTensorPow

import Definitions.Def_AlgebraicGeometry_RelPicardPullback
import Definitions.Def_AlgebraicGeometry_OModulePresheafOfModules
import Definitions.Def_AlgebraicGeometry_ModulesPullbackMonoidal
import Theorems.Thm_AlgebraicGeometry_RelPicard_isAlgEquivZero_of_isAlgEquivZero_pullback_curveChange_of_twoGluedSmoothCurves
import Theorems.Thm_AlgebraicGeometry_RelPicard_isAlgEquivZero_iff_eulerChar_sectionsOf_eq
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_IsInvertible_eulerChar_sectionsOf_tensor_eq_add_sub
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_IsInvertible_eulerChar_sectionsOf_dual_eq
import Theorems.Thm_AlgebraicGeometry_RelPicard_finrank_H0_unit_fibre_eq_one
import Theorems.Thm_AlgebraicGeometry_Scheme_TwoAffineOpenCover_exists_linearEquiv_sectionsOf_of_iso
import Theorems.Thm_AlgebraicGeometry_Scheme_TwoAffineOpenCover_exists_linearEquiv_sectionsOf_H0
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_exists_linearEquiv_sections_pullback_of_isClosedImmersion_of_locallyTrivial
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_nonempty_pullback_tensorPow_iso
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_IsInvertible_tensorPow
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_IsInvertible_tensor
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_IsInvertible_dual
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_IsInvertible_pullback_dual
import Theorems.Thm_AlgebraicGeometry_OModulePresheaf_cechFinite_ofModules_of_locallyTrivial
import Theorems.Thm_AlgebraicGeometry_OModulePresheaf_cechFinite_toOrderedAffineCover_iff
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_RelPicard_isAlgEquivZero_of_finrank_H1_tensorPow_add_two_le_of_twoGluedSmoothCurves
p2m_attr_erase "instance" "AlgebraicGeometry.RelEffCartierDiv.isIso_subschemeIota_snd_of_degree_one AlgebraicGeometry.isIso_ker_graphOver_subschemeIota_snd AlgebraicGeometry.isClosedImmersion_graphOver AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instNeg AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instSMulInt AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instAddCommGroup AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instAdd AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instSub AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instModuleCarrierObjOppositeOpensCarrierCarrierCommRingCatPresheafOpOpensTop AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instSMulCarrierObjOppositeOpensCarrierCarrierCommRingCatPresheafOpOpensTop AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instSMulNat AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instZero AlgebraicGeometry.RelEffCartierDiv.subsingleton_of_degree_zero AlgebraicCurve.Place.instIsScalarTowerSubtypeMemValuationSubringToValuationSubring AlgebraicCurve.Divisor.instDistribMulActionAlgEquiv AlgebraicCurve.Place.instSMulAlgEquiv AlgebraicCurve.Place.instIsPrincipalIdealRingSubtypeMemValuationSubringToValuationSubring AlgebraicCurve.Place.instIsDiscreteValuationRingSubtypeMemValuationSubringToValuationSubring AlgebraicCurve.Pic0.instDistribMulActionAlgEquiv AlgebraicCurve.Place.instAlgebraSubtypeMemValuationSubringToValuationSubring AlgebraicCurve.Place.instMulActionAlgEquiv AlgebraicCurve.Pic0.instSMulAlgEquiv AlgebraicCurve.IsCurveOver.instNontrivialKaehler AlgebraicCurve.IsCurveOver.instFreeKaehler AlgebraicCurve.IsCurveOver.toHasPrincipalDivisors AlgebraicCurve.IsCurveOver.instFiniteResidue AlgebraicCurve.CurveModel.isProper AlgebraicCurve.CurveModel.isIntegral AlgebraicCurve.CurveModel.smooth AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.instFundamentalIdentityOfSumRamificationInertia AlgebraicCurve.Place.instIsScalarTowerResidueFieldRestrictPushforward AlgebraicCurve.Place.instAlgebraResidueFieldRestrictPushforward AlgebraicCurve.Place.instIsLocalHomRestrictInclusion AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt"
p2m_attr_erase "instance" "AlgebraicCurve.SemilinearAut.instDistribMulActionSubtypeProdRingAutMemSubgroupPic0 AlgebraicCurve.SemilinearAut.instDistribMulActionSubtypeProdRingAutMemSubgroupDivisor AlgebraicCurve.Pic0.instModuleZModTorsion AlgebraicCurve.SemilinearAut.instSMulSubtypeProdRingAutMemSubgroupPlace AlgebraicCurve.SemilinearAut.instDistribMulActionTorsion AlgebraicCurve.SemilinearAut.instSMulSubtypeProdRingAutMemSubgroupPic0 AlgebraicCurve.SemilinearAut.instSMulTorsion AlgebraicCurve.SemilinearAut.instMulActionSubtypeProdRingAutMemSubgroupPlace AlgebraicCurve.SemilinearAut.instSMulCommClassZModTorsion AlgebraicCurve.SemilinearAut.instMulSemiringActionSubtypeProdRingAutMemSubgroup instDecEqAlgebraicClosureRat WeierstrassCurve.Affine.Point.instDistribMulActionAlgEquiv WeierstrassCurve.Affine.Point.instModuleZModTorsionBy WeierstrassCurve.Affine.Point.instSMulTorsionBy WeierstrassCurve.Affine.Point.instDistribMulActionTorsionBy WeierstrassCurve.Affine.Point.instSMulAlgEquiv WeierstrassCurve.Affine.Point.instSMulCommClassAlgEquivZModTorsionBy AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions AlgebraicCurve.instHasLocalResidue_of_hasCanonicalLocalResidueK AlgebraicCurve.instHasCanonicalLocalResidueK_of_hasCanonicalLocalResidueKStar AlgebraicCurve.Place.kw_ffgc_finiteDimensional_adicCompletion instAlgebraSubtypeMemValuationSubring_definitions AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersIntegersCompletion ModularCurve.KwF4gRRTate.instAlgebraKAdicCompletionIntegers AlgebraicCurve.Place.kw_ffgc_continuousSMul_adicCompletionComap AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersCompletionCompletion IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions AlgebraicCurve.instHasCanonicalLocalResidueK AlgebraicCurve.Place.instAlgebra_restrictResidueField AlgebraicCurve.Place.instIsScalarTower_restrictResidueField AlgebraicCurve.instHasLocalResidue AlgebraicCurve.HasSeparableResidue.of_perfectField_of_isCurveOver AlgebraicCurve.HasSeparableResidue.of_perfectField AlgebraicCurve.Place.instIsLocalHom_restrictSubringHom AlgebraicCurve.instHasCanonicalLocalResidueKStar"
p2m_attr_erase "instance" "ModularCurve.KwNo6Pin.isLocalRing_completion SheafOfModules.isIso_ihomModelToIhom AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instDecidableEqIdx AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instFintype AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instLinearOrder AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instFintypeIdx AlgebraicGeometry.OModulePresheaf.instSubsingletonObjZero AlgebraicGeometry.OModulePresheaf.Leray.relAltC_scalarTower AlgebraicGeometry.OModulePresheaf.Leray.ker_relAltd_modΓ AlgebraicGeometry.OModulePresheaf.Leray.relAltC_modΓ AlgebraicGeometry.OModulePresheaf.Leray.biC_abGrp AlgebraicGeometry.OModulePresheaf.Leray.relAltH_modΓ AlgebraicGeometry.OModulePresheaf.Leray.ker_relAltd_smul AlgebraicGeometry.OModulePresheaf.Leray.relAltH_scalarTower AlgebraicGeometry.OModulePresheaf.Leray.relAltH_smul AlgebraicGeometry.OModulePresheaf.Leray.biC_module DoubleComplex.instModuleE₂I DoubleComplex.Bounded.modR DoubleComplex.instModuleE₂II DoubleComplex.instAddCommGroupE₂II DoubleComplex.Bounded.abGrp DoubleComplex.instAddCommGroupE₂I AlgebraicGeometry.ChowDatum.hι_closed AlgebraicGeometry.ChowDatumProj.hιN_closed AlgebraicGeometry.ChowDatumProj.hp_proper AlgebraicGeometry.ChowDatum.hp_isoU AlgebraicGeometry.ChowDatum.hp_proper AlgebraicGeometry.ProjSpace.algebraAway AlgebraicGeometry.ProjSpace.instIsProperProdOverπ AlgebraicGeometry.ChowDatumProj.hp_isoU AlgebraicGeometry.ProjSpace.isProper_π AlgebraicGeometry.ProjSpace.finiteType_mvPolynomial ProjSpaceCech.GradedModule.H.module ProjSpaceCech.GradedModule.H.addCommGroup ProjSpaceCech.GradedModule.sec.instAdd ProjSpaceCech.GradedModule.sec.instNeg ProjSpaceCech.GradedModule.acg ProjSpaceCech.GradedModule.Frac.setoid ProjSpaceCech.GradedModule.modR ProjSpaceCech.GradedModule.sec.instModule"
p2m_attr_erase "instance" "ProjSpaceCech.GradedModule.sec.instAddCommGroup ProjSpaceCech.GradedModule.sec.instZero ProjSpaceCech.GradedModule.Presentation.fJ ProjSpaceCech.GradedModule.sec.instSMul ProjSpaceCech.Twist.H.module ProjSpaceCech.Idx.instFintype ProjSpaceCech.Twist.H.addCommGroup ProjSpaceCech.Idx.instDecidableEq ProjSpaceCech.Twist.Mon.instDecidableEq ProjSpaceCech.Twist.cochain.instAddCommGroup ProjSpaceCech.Twist.cochain.instModule AlgebraicGeometry.SmoothOfRelativeDimension.fiberToSpecResidueField AlgebraicGeometry.SmoothOfRelativeDimension.pullback_snd AlgebraicGeometry.SmoothOfRelativeDimension.pullback_fst AlgebraicGeometry.SmoothOfRelativeDimension.smooth_one AlgebraicGeometry.SmoothProperCurve.isIntegral_pullback_Spec_field AlgebraicGeometry.IsProper.fiberToSpecResidueField"
p2m_attr_erase "simp" "AlgebraicGeometry.RelPicard.algEquivZeroGroupCut_toSubPicCondition AlgebraicGeometry.RelPicard.SubPicGroupCondition.mk.injEq AlgebraicGeometry.RelPicard.SubPicGroupCondition.mk.sizeOf_spec AlgebraicGeometry.RelPicard.SubPicCondition.onClasses_mk AlgebraicGeometry.RelPicard.relSubPicPresheaf_map_coe GoodReductionJacobian.relativeGroupLawOfGrpObj_inv GoodReductionJacobian.relativeGroupLawOfGrpObj_mul GoodReductionJacobian.overHomEquivSchemeHomOver_apply_coe GoodReductionJacobian.relativeGroupLawOfGrpObj_one GoodReductionJacobian.overHomEquivSchemeHomOver_symm_apply_left AlgebraicGeometry.Scheme.Modules.tensorSections_zero_right AlgebraicGeometry.Scheme.Modules.map_unitSection AlgebraicGeometry.Scheme.Modules.tensorSectionsBilin_apply AlgebraicGeometry.Scheme.Modules.tensorPowSection_zero AlgebraicGeometry.Scheme.Modules.tensorSections_zero_left AlgebraicGeometry.Scheme.Modules.pullbackLocalSection_neg AlgebraicGeometry.Scheme.Modules.pullbackLocalSection_zero AlgebraicGeometry.Scheme.Modules.pullbackLocalSection_sub AlgebraicGeometry.Scheme.Modules.pullbackLocalSection_add AlgebraicGeometry.RelPicard.fst_toProdSpec AlgebraicGeometry.RelPicard.toProdSpec_fst_assoc AlgebraicGeometry.RelPicard.pointsSubBasepointModule_cons AlgebraicGeometry.RelPicard.pointsSubBasepointModule_nil AlgebraicGeometry.RelPicard.fst_toProdSpec_assoc AlgebraicGeometry.RelPicard.toProdSpec_fst AlgebraicGeometry.RelEffCartierDiv.toRelEffDivisor_ofRelEffDivisor AlgebraicGeometry.RelEffCartierDiv.toRelEffDivisor_I AlgebraicGeometry.mapOnProdOver_fst_assoc AlgebraicGeometry.RelEffCartierDiv.mk.sizeOf_spec AlgebraicGeometry.RelEffCartierDiv.mk.injEq AlgebraicGeometry.mapOnProdOver_snd AlgebraicGeometry.mapOnProdOver_fst AlgebraicGeometry.mapOnProdOver_snd_assoc AlgebraicGeometry.mapOnProdOver_id AlgebraicCurve.RelEffDivisor.mk.sizeOf_spec AlgebraicCurve.mapOnProd_fst AlgebraicCurve.mapOnProd_fst_assoc AlgebraicCurve.mapOnProd_snd AlgebraicCurve.UnivDivisorPack.mk.injEq AlgebraicCurve.RelEffDivisor.mk.injEq"
p2m_attr_erase "simp" "AlgebraicCurve.UnivDivisorPack.mk.sizeOf_spec AlgebraicCurve.mapOnProd_snd_assoc AlgebraicGeometry.graphOver_fst_assoc AlgebraicGeometry.RelEffCartierDiv.toPoint_comp AlgebraicGeometry.RelEffCartierDiv.toPoint_comp_assoc AlgebraicGeometry.graphOver_fst AlgebraicGeometry.RelEffCartierDiv.ofPoint_I AlgebraicGeometry.graphOver_snd AlgebraicGeometry.graphOver_snd_assoc AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.sub_app AlgebraicGeometry.Scheme.IdealSheafData.sres_sresTop AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.add_app AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.mk.sizeOf_spec AlgebraicGeometry.Scheme.IdealSheafData.coe_resLE AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.smul_app AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.coe_ofLE_app AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.ideal_range AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.zero_app AlgebraicGeometry.Scheme.IdealSheafData.sres_sres AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.comp_app AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.neg_app AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.id_app AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.coe_mulRight_app AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.nsmul_app AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.mk.injEq AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.zsmul_app AlgebraicGeometry.prodKerGraph_one AlgebraicGeometry.fibrePowOver.proj_comp AlgebraicGeometry.prodKerGraph_zero AlgebraicGeometry.RelEffCartierDiv.empty_I AlgebraicGeometry.fibrePowOver.proj_comp_assoc AlgebraicCurve.SymmetricPowerPackage.mk.sizeOf_spec AlgebraicCurve.SymmetricPowerPackage.mk.injEq AlgebraicCurve.Place.mk.injEq AlgebraicCurve.Divisor.degree_single AlgebraicCurve.Divisor.smul_single AlgebraicCurve.Place.smul_toValuationSubring AlgebraicCurve.Place.heightOneSpectrum_asIdeal AlgebraicCurve.Place.coe_algebraMap AlgebraicCurve.Place.ord_one"
p2m_attr_erase "simp" "AlgebraicCurve.Place.coe_smulRingEquiv_apply AlgebraicCurve.Pic0.coe_degZeroSMulHom AlgebraicCurve.Place.deg_smul AlgebraicCurve.Pic0.mk_zero AlgebraicCurve.Place.mk.sizeOf_spec AlgebraicCurve.Divisor.degree_smul AlgebraicCurve.Pic0.mk_add AlgebraicCurve.Place.ord_zero AlgebraicCurve.Place.ofHeightOneSpectrum_toValuationSubring AlgebraicCurve.mulAdele_apply AlgebraicCurve.residuePairing_apply_coe AlgebraicCurve.mem_adeleBdd AlgebraicCurve.weilSmul_one AlgebraicCurve.diagonalHom_apply AlgebraicCurve.weilSmul_apply AlgebraicCurve.adeleSpaceMul_coe AlgebraicCurve.mulAdele_one AlgebraicCurve.CurveModel.mk.injEq AlgebraicCurve.CurveModel.mk.sizeOf_spec AlgebraicCurve.coe_cechH0Equiv_apply AlgebraicCurve.cechH1ToH1_mk AlgebraicCurve.lSpaceOn_univ AlgebraicCurve.lSpaceOn_empty AlgebraicCurve.Place.congrEquiv_symm_apply AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply AlgebraicCurve.RationalFunctionField.deg_placeOfPoint AlgebraicCurve.Divisor.mapRestrict_single AlgebraicCurve.Divisor.pushforward_single AlgebraicCurve.Place.coe_restrictInclusion AlgebraicCurve.Place.mem_fiber AlgebraicCurve.Place.restrict_toValuationSubring AlgebraicCurve.Divisor.degree_pushforward AlgebraicCurve.Place.restrictResidueMap_residue AlgebraicCurve.Pic0.coe_pushforwardDegZeroHom AlgebraicCurve.Pic0.coe_pullbackDegZeroHom AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver"
p2m_attr_erase "simp" "AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal AlgebraicCurve.IsFrobeniusEndo.frobNormRingHom_apply ModularCurve.frobeniusPushforwardGeomLevelPic0_mk ModularCurve.coe_frobeniusGeomLevelEquiv_apply ModularCurve.coe_frobeniusPushforwardGeomLevelDegZero ModularCurve.heckeFibreGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusGeomLevel_apply_coe ModularCurve.frobeniusPullbackGeomLevelPic0OfIsCurveOver_mk ModularCurve.coe_heckeFibreGeomLevelDegZero ModularCurve.coe_frobeniusPullbackGeomLevelDegZero ModularCurve.frobeniusPullbackGeomLevelPic0_mk ModularCurve.frobeniusPullbackGeomLevel_single ModularCurve.heckeFibreGeomLevelPic0_mk ModularCurve.frobeniusPushforwardGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusPushforwardGeomLevel_single ModularCurve.qExpandAlgC_apply AlgebraicCurve.Divisor.degree_pushforwardAlong AlgebraicCurve.Pic0.coe_degZeroCorrespondence AlgebraicCurve.Place.mem_fiberAlong AlgebraicCurve.SemilinearAut.toRingAut_inv AlgebraicCurve.SemilinearAut.smul_def AlgebraicCurve.SemilinearAut.smul_single AlgebraicCurve.SemilinearAut.smul_toValuationSubring AlgebraicCurve.SemilinearAut.baseAut_inv AlgebraicCurve.SemilinearAut.baseAut_ofAlgAut AlgebraicCurve.SemilinearAut.toRingAut_ofAlgAut AlgebraicCurve.SemilinearAut.torsionRep_apply AlgebraicCurve.SemilinearAut.toRingAut_one AlgebraicCurve.SemilinearAut.deg_smul AlgebraicCurve.SemilinearAut.degree_smul AlgebraicCurve.SemilinearAut.coe_degZeroSMulHom AlgebraicCurve.SemilinearAut.baseAut_mul AlgebraicCurve.SemilinearAut.coe_smulValuationSubringEquiv_apply AlgebraicCurve.SemilinearAut.baseAut_one AlgebraicCurve.SemilinearAut.ofAlgAut_smul AlgebraicCurve.SemilinearAut.coe_torsion_smul AlgebraicCurve.SemilinearAut.toRingAut_mul AlgebraicCurve.coe_frobeniusPushforwardDegZero"
p2m_attr_erase "simp" "AlgebraicCurve.IsFrobeniusEndo.coe_frobeniusPullbackDegZero ModularCurve.jqNModC_one ModularCurve.qExpand_coeff_mul ModularCurve.qExpandₐ_apply ModularCurve.jqN_one ModularCurve.qExpand_single ModularCurve.dedekindPsi_one ModularCurve.ModularPolynomialData.mk.sizeOf_spec ModularCurve.evalAtJ_X ModularCurve.ModularPolynomialData.mk.injEq ModularCurve.constantCoeff_jNum ModularCurve.constantCoeff_eisenstein4 ModularCurve.qExpand_C ModularCurve.coeff_jq_neg_one ModularCurve.constantCoeff_jNumQ ModularCurve.reduceModBivar_C_X ModularCurve.laurentMap_coeff ModularCurve.reduceModBivar_X ModularCurve.laurentMap_single ModularCurve.evalAtJInt_X ModularCurve.evalAtJMod_X ModularCurve.jqNMod_one ModularCurve.aeval_heckeGen ModularCurve.coe_mTorsionGaloisRep_apply ModularCurve.eisensteinSystem_of_dvd ModularCurve.eisensteinSystem_of_not_dvd FreyPackage.mk.sizeOf_spec FreyPackage.mk.injEq WeierstrassCurve.Affine.Point.galoisRepModuleEnd_apply AlgebraicCurve.RationalFunctionField.placeInfty_toValuationSubring AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none AlgebraicCurve.Divisor.evalFun_zero AlgebraicCurve.Place.evalAt_one AlgebraicCurve.Place.differentialCoeff_zero AlgebraicCurve.Place.differentialCoeff_dCoord AlgebraicCurve.TranscendenceTower.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.injEq"
p2m_attr_erase "simp" "AlgebraicCurve.TranscendenceTower.mk.injEq AlgebraicCurve.PoleDivisorPackage.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.sizeOf_spec AlgebraicCurve.PoleDivisorPackage.mk.injEq AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.sizeOf_spec AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.injEq AlgebraicCurve.adeleSingle_coe AlgebraicCurve.kaehlerResidueTermKFam_apply AlgebraicCurve.Place.LocalResidueData.mk.injEq AlgebraicCurve.Place.LocalResidueData.mk.sizeOf_spec AlgebraicCurve.Place.kw_ffgc_adicCompletionComapIntegers_coe AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.sizeOf_spec AlgebraicCurve.Place.mem_simplePoleSubmodule AlgebraicCurve.Place.coe_uniformizerSubring ModularCurve.Lg37.Lg37CompletionSection.mk.injEq AlgebraicCurve.Place.CoefficientFieldSection.mk.injEq AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.injEq ModularCurve.Lg37.Lg37CompletionSection.mk.sizeOf_spec AlgebraicCurve.Place.CoefficientFieldSection.mk.sizeOf_spec AlgebraicCurve.Place.poleSubmodule_one AlgebraicCurve.Place.mem_poleSubmodule AlgebraicGeometry.Scheme.Modules.toUnitSection_ofUnitSection AlgebraicGeometry.Scheme.Modules.pullbackSection_def AlgebraicGeometry.Scheme.Modules.ofUnitSection_toUnitSection PresheafOfModules.InternalHom.IsSheafAux.appAt_toPresheafHom SheafOfModules.ihomSectionsEquivFamily_unit AlgebraicGeometry.Scheme.Modules.restrictHomEquivFamily_apply SheafOfModules.ihomEval_unit_app AlgebraicGeometry.Scheme.Modules.ihomEval_zero_right AlgebraicGeometry.Scheme.Modules.ihomEval_zero_left AlgebraicGeometry.Scheme.Modules.homOfFamily_app_apply SheafOfModules.unit_ihomSectionsEquivFamily AlgebraicGeometry.Scheme.Modules.familyOfHom_app AlgebraicGeometry.Scheme.Modules.restrictUnitIso_hom_app_apply AlgebraicGeometry.Scheme.Modules.restrictUnitIso_inv_app_apply AlgebraicGeometry.Scheme.Modules.restrictHomOfFamily_app_apply AlgebraicGeometry.Scheme.Modules.restrictHomEquivFamily_symm_apply AlgebraicGeometry.Scheme.OrderedAffineCover.toCoverOf_U AlgebraicGeometry.Scheme.OrderedAffineCoverOf.mk.sizeOf_spec AlgebraicGeometry.Scheme.OrderedAffineCoverOf.mk.injEq"
p2m_attr_erase "simp" "AlgebraicGeometry.Scheme.OrderedAffineCover.restrict_U AlgebraicGeometry.OModulePresheaf.Hom.mk.injEq AlgebraicGeometry.OModulePresheaf.Hom.id_app AlgebraicGeometry.OModulePresheaf.AffHom.appSections_apply AlgebraicGeometry.OModulePresheaf.AffHom.comp_app AlgebraicGeometry.OModulePresheaf.AffSES.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.AffHom.kerMap_coe AlgebraicGeometry.OModulePresheaf.AffHom.id_app AlgebraicGeometry.OModulePresheaf.Hom.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.Hom.toAffHom_app AlgebraicGeometry.OModulePresheaf.SES.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.AffHom.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.Hom.comp_app AlgebraicGeometry.OModulePresheaf.SES.mk.injEq AlgebraicGeometry.OModulePresheaf.AffHom.mk.injEq AlgebraicGeometry.OModulePresheaf.Hom.appSections_apply AlgebraicGeometry.OModulePresheaf.AffSES.mk.injEq AlgebraicGeometry.OModulePresheaf.prod_obj AlgebraicGeometry.OModulePresheaf.restrOpen_obj AlgebraicGeometry.OModulePresheaf.DevissageStep.mk.injEq AlgebraicGeometry.OModulePresheaf.pushforward_obj AlgebraicGeometry.OModulePresheaf.im_obj AlgebraicGeometry.OModulePresheaf.pow_obj AlgebraicGeometry.OModulePresheaf.fstHom_app AlgebraicGeometry.OModulePresheaf.ker_obj AlgebraicGeometry.OModulePresheaf.coker_obj AlgebraicGeometry.OModulePresheaf.DevissageStep.mk.sizeOf_spec AlgebraicGeometry.Scheme.OrderedAffineCover.preimage_U AlgebraicGeometry.OModulePresheaf.sndHom_app AlgebraicGeometry.OModulePresheaf.Leray.restrictToPreimage_U DoubleComplex.Bounded.mk.injEq DoubleComplex.Bounded.mk.sizeOf_spec DoubleComplex.Convergence.mk.injEq DoubleComplex.Convergence.mk.sizeOf_spec DoubleComplex.SubQuot.mk.sizeOf_spec DoubleComplex.SubQuot.mk.injEq AlgebraicGeometry.ChowDatumProj.mk.sizeOf_spec AlgebraicGeometry.ChowDatum.mk.sizeOf_spec AlgebraicGeometry.ChowDatumProj.mk.injEq AlgebraicGeometry.ChowDatum.mk.injEq"
p2m_attr_erase "simp" "ProjSpaceCech.GradedModule.mk.injEq ProjSpaceCech.GradedModule.mk.sizeOf_spec ProjSpaceCech.GradedModule.Frac.mk.sizeOf_spec ProjSpaceCech.GradedModule.Presentation.mk.injEq ProjSpaceCech.GradedModule.Frac.mk.injEq ProjSpaceCech.GradedModule.Presentation.mk.sizeOf_spec ProjSpaceCech.GradedModule.Hom.shift_toLinearMap ProjSpaceCech.GradedModule.Hom.mk.sizeOf_spec ProjSpaceCech.GradedModule.Hom.mk.injEq TwoChartCech.Mumford.dK_apply TwoChartCech.Mumford.ι0_apply TwoChartCech.Mumford.ι1_apply TwoChartCech.KerCoprod.dK_apply TwoChartCech.KerCoprod.ι1_apply TwoChartCech.KerCoprod.ι0_apply AlgebraicGeometry.tilde.functorCompPullbackSpecIso_app AlgebraicGeometry.SmoothProperCurve.sectionBaseChange_coe_snd AlgebraicGeometry.SmoothProperCurve.sectionBaseChange_coe_fst"

set_option autoImplicit false

universe u

p2m_open "CategoryTheory CategoryTheory.Limits Opposite CategoryTheory.MonoidalCategory AlgebraicGeometry P2MW.S_AlgebraicGeometry_RelPicard_isAlgEquivZero_of_finrank_H1_tensorPow_add_two_le_of_twoGluedSmoothCurves.AlgebraicGeometry AlgebraicGeometry.RelPicard NeronModelInfra TensorProduct"

noncomputable section

namespace AlgebraicGeometry
p2m_export "AlgebraicGeometry" "Scheme.Modules.Hom.app_smul Surjective SmoothOfRelativeDimension IsProper Scheme.Modules.pullback Scheme.Hom GeometricallyIntegral Scheme.Hom.appLE_comp_appLE Scheme.Hom.preimage_inf Scheme.Modules.Hom GeometricallyIntegral.isIntegral_of_subsingleton Spec IsIntegral Scheme IsClosedImmersion IsReduced Scheme.Modules.pullbackCongr Scheme.Modules.pullbackPushforwardAdjunction Scheme.Modules.pullbackId IsAffineOpen Scheme.Hom.preimage_sup Scheme.Modules IsAffineHom geometrically Scheme.Modules.pullbackComp Scheme.ΓSpecIso Scheme.Hom.appLE_eq_app Scheme.Modules.IsInvertible Scheme.TwoAffineOpenCover Scheme.TwoAffineOpenCover.algebraOfHom Scheme.TwoAffineOpenCover.moduleSectionsOfHom Scheme.TwoAffineOpenCover.sectionsOf_r0_apply Scheme.TwoAffineOpenCover.sectionsOf_r1_apply Scheme.Modules.dual Scheme.Modules.tensorPow_succ RelPicard.curveChange OModulePresheaf Scheme.Modules.pullbackTensorUnitObjIso RelPicard.isAlgEquivZero_of_isAlgEquivZero_pullback_curveChange_of_twoGluedSmoothCurves RelPicard.isAlgEquivZero_iff_eulerChar_sectionsOf_eq Scheme.Modules.IsInvertible.eulerChar_sectionsOf_tensor_eq_add_sub Scheme.Modules.IsInvertible.eulerChar_sectionsOf_dual_eq RelPicard.finrank_H0_unit_fibre_eq_one Scheme.TwoAffineOpenCover.exists_linearEquiv_sectionsOf_of_iso Scheme.TwoAffineOpenCover.exists_linearEquiv_sectionsOf_H0 Scheme.Modules.exists_linearEquiv_sections_pullback_of_isClosedImmersion_of_locallyTrivial Scheme.Modules.nonempty_pullback_tensorPow_iso OModulePresheaf.cechFinite_ofModules_of_locallyTrivial OModulePresheaf.cechFinite_toOrderedAffineCover_iff Scheme.TwoAffineOpenCover.ext_N2bC3"
namespace H1Dom
p2m_open "AlgebraicGeometry"

variable {k : Type u} [Field k] {X Y : Scheme.{u}} (i : Y ⟶ X) (x : X ⟶ Spec (CommRingCat.of k))

def res (F : X.Modules) (U : X.Opens) : Γ(F, U) →+ Γ((Scheme.Modules.pullback i).obj F, i ⁻¹ᵁ U) :=
  (((Scheme.Modules.pullbackPushforwardAdjunction i).unit.app F).app U).hom

theorem res_smul (F : X.Modules) (U : X.Opens) (b : Γ(X, U)) (m : Γ(F, U)) :
    res i F U (b • m) = (i.app U).hom b • res i F U m :=
  Scheme.Modules.Hom.app_smul _ b m

theorem res_map (F : X.Modules) {U V : X.Opens} (h : V ≤ U) (m : Γ(F, U)) :
    res i F V (F.presheaf.map (homOfLE h).op m) =
      ((Scheme.Modules.pullback i).obj F).presheaf.map (homOfLE (show i ⁻¹ᵁ V ≤ i ⁻¹ᵁ U from fun _ hy => h hy)).op
        (res i F U m) := by
  simp only [res]
  have := (((Scheme.Modules.pullbackPushforwardAdjunction i).unit.app F)).mapPresheaf.naturality (homOfLE h).op
  have h2 := congrArg (fun φ => φ.hom m) this
  simp at h2
  exact h2

theorem algebraMap_comp (U : X.Opens) (r : k) :
    letI := Scheme.TwoAffineOpenCover.algebraOfHom x U
    letI := Scheme.TwoAffineOpenCover.algebraOfHom (i ≫ x) (i ⁻¹ᵁ U)
    algebraMap k Γ(Y, i ⁻¹ᵁ U) r = (i.app U).hom (algebraMap k Γ(X, U) r) := by
  letI := Scheme.TwoAffineOpenCover.algebraOfHom x U
  letI := Scheme.TwoAffineOpenCover.algebraOfHom (i ≫ x) (i ⁻¹ᵁ U)
  change ((Scheme.ΓSpecIso (.of k)).inv ≫ (i ≫ x).appLE ⊤ (i ⁻¹ᵁ U) le_top).hom r =
    (i.app U).hom (((Scheme.ΓSpecIso (.of k)).inv ≫ x.appLE ⊤ U le_top).hom r)
  have hc : x.appLE ⊤ U le_top ≫ i.app U = (i ≫ x).appLE ⊤ (i ⁻¹ᵁ U) le_top := by
    rw [← Scheme.Hom.appLE_eq_app, Scheme.Hom.appLE_comp_appLE]
  rw [← hc]
  rfl

def resₗ (F : X.Modules) (U : X.Opens) :
    letI := Scheme.TwoAffineOpenCover.moduleSectionsOfHom x F U
    letI := Scheme.TwoAffineOpenCover.moduleSectionsOfHom (i ≫ x) ((Scheme.Modules.pullback i).obj F) (i ⁻¹ᵁ U)
    Γ(F, U) →ₗ[k] Γ((Scheme.Modules.pullback i).obj F, i ⁻¹ᵁ U) :=
  letI := Scheme.TwoAffineOpenCover.moduleSectionsOfHom x F U
  letI := Scheme.TwoAffineOpenCover.moduleSectionsOfHom (i ≫ x) ((Scheme.Modules.pullback i).obj F) (i ⁻¹ᵁ U)
  { toFun := res i F U
    map_add' := fun a b => map_add _ a b
    map_smul' := fun r m => by
      letI := Scheme.TwoAffineOpenCover.algebraOfHom x U
      letI := Scheme.TwoAffineOpenCover.algebraOfHom (i ≫ x) (i ⁻¹ᵁ U)
      change res i F U ((algebraMap k Γ(X, U) r) • m) = (algebraMap k Γ(Y, i ⁻¹ᵁ U) r) • res i F U m
      rw [res_smul, algebraMap_comp] }

theorem resₗ_apply (F : X.Modules) (U : X.Opens) (m : Γ(F, U)) :
    resₗ i x F U m = res i F U m := rfl

theorem res_surjective [IsClosedImmersion i] (F : X.Modules) (hF : Scheme.Modules.IsInvertible F)
    (U : X.Opens) (hU : IsAffineOpen U) : Function.Surjective (res i F U) := by
  letI : Algebra Γ(X, U) Γ(Y, i ⁻¹ᵁ U) := (i.app U).hom.toAlgebra
  obtain ⟨e, he⟩ := Scheme.Modules.exists_linearEquiv_sections_pullback_of_isClosedImmersion_of_locallyTrivial
    i F hF.1 U hU
  intro z
  obtain ⟨w, rfl⟩ := e.surjective z
  induction w using TensorProduct.induction_on with
  | zero => exact ⟨0, by simp⟩
  | tmul a m =>
      obtain ⟨b, rfl⟩ := i.app_surjective U hU a
      refine ⟨b • m, ?_⟩
      rw [res_smul]
      have : (i.app U).hom b ⊗ₜ[Γ(X, U)] m = ((i.app U).hom b) • ((1 : Γ(Y, i ⁻¹ᵁ U)) ⊗ₜ[Γ(X, U)] m) := by
        rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]
      rw [this, map_smul, he]
      rfl
  | add w₁ w₂ h₁ h₂ =>
      obtain ⟨m₁, hm₁⟩ := h₁
      obtain ⟨m₂, hm₂⟩ := h₂
      exact ⟨m₁ + m₂, by rw [map_add, hm₁, hm₂, map_add]⟩

def comap {X' Y' : Scheme.{u}} (𝒲 : Y'.TwoAffineOpenCover) (f : X' ⟶ Y') [IsAffineHom f] : X'.TwoAffineOpenCover where
  U0 := f ⁻¹ᵁ 𝒲.U0
  U1 := f ⁻¹ᵁ 𝒲.U1
  isAffineOpen_U0 := 𝒲.isAffineOpen_U0.preimage f
  isAffineOpen_U1 := 𝒲.isAffineOpen_U1.preimage f
  sup_eq_top := by rw [← Scheme.Hom.preimage_sup, 𝒲.sup_eq_top]; rfl
  isAffineOpen_inf := by rw [← Scheme.Hom.preimage_inf]; exact 𝒲.isAffineOpen_inf.preimage f

theorem exists_surjective_H1 [IsClosedImmersion i] (F : X.Modules) (hF : Scheme.Modules.IsInvertible F)
    (𝒲 : X.TwoAffineOpenCover) :
    ∃ f : (𝒲.sectionsOf x F).H1 →ₗ[k] ((comap 𝒲 i).sectionsOf (i ≫ x) ((Scheme.Modules.pullback i).obj F)).H1,
      Function.Surjective f := by
  let S := 𝒲.sectionsOf x F
  let S' := (comap 𝒲 i).sectionsOf (i ≫ x) ((Scheme.Modules.pullback i).obj F)

  have e0 : ∀ m0 : S.M0, S'.r0 (res i F 𝒲.U0 m0) = res i F (𝒲.U0 ⊓ 𝒲.U1) (S.r0 m0) := fun m0 => by
    change ((comap 𝒲 i).sectionsOf (i ≫ x) ((Scheme.Modules.pullback i).obj F)).r0 _ =
      res i F _ ((𝒲.sectionsOf x F).r0 m0)
    rw [Scheme.TwoAffineOpenCover.sectionsOf_r0_apply, Scheme.TwoAffineOpenCover.sectionsOf_r0_apply, res_map]
    rfl
  have e1 : ∀ m1 : S.M1, S'.r1 (res i F 𝒲.U1 m1) = res i F (𝒲.U0 ⊓ 𝒲.U1) (S.r1 m1) := fun m1 => by
    change ((comap 𝒲 i).sectionsOf (i ≫ x) ((Scheme.Modules.pullback i).obj F)).r1 _ =
      res i F _ ((𝒲.sectionsOf x F).r1 m1)
    rw [Scheme.TwoAffineOpenCover.sectionsOf_r1_apply, Scheme.TwoAffineOpenCover.sectionsOf_r1_apply, res_map]
    rfl

  let φ : S.M01 →ₗ[k] S'.H1 := (LinearMap.range S'.cechDiff).mkQ ∘ₗ
    (show S.M01 →ₗ[k] S'.M01 from resₗ i x F (𝒲.U0 ⊓ 𝒲.U1))
  have hφapply : ∀ m : S.M01, φ m = (LinearMap.range S'.cechDiff).mkQ (res i F (𝒲.U0 ⊓ 𝒲.U1) m) := fun m => rfl
  have hφ : LinearMap.range S.cechDiff ≤ LinearMap.ker φ := by
    rintro _ ⟨⟨m0, m1⟩, rfl⟩
    rw [LinearMap.mem_ker, hφapply, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
    refine ⟨(res i F 𝒲.U0 m0, res i F 𝒲.U1 m1), ?_⟩
    rw [TwoChartCech.Sections.cechDiff_apply, TwoChartCech.Sections.cechDiff_apply]
    change S'.r1 (res i F 𝒲.U1 m1) - S'.r0 (res i F 𝒲.U0 m0) = res i F _ (S.r1 m1 - S.r0 m0)
    rw [e0, e1]
    exact ((res i F (𝒲.U0 ⊓ 𝒲.U1)).map_sub _ _).symm
  refine ⟨(LinearMap.range S.cechDiff).liftQ φ hφ, ?_⟩
  rw [← LinearMap.range_eq_top, Submodule.range_liftQ, LinearMap.range_eq_top]
  intro z
  obtain ⟨z', rfl⟩ := (LinearMap.range S'.cechDiff).mkQ_surjective z
  obtain ⟨m, hm⟩ := res_surjective i F hF (𝒲.U0 ⊓ 𝒲.U1) 𝒲.isAffineOpen_inf z'
  exact ⟨m, by rw [hφapply, hm]⟩

theorem finrank_H1_pullback_le [IsClosedImmersion i] (F : X.Modules) (hF : Scheme.Modules.IsInvertible F)
    (𝒲 : X.TwoAffineOpenCover) [Module.Finite k (𝒲.sectionsOf x F).H1] :
    Module.finrank k ((comap 𝒲 i).sectionsOf (i ≫ x) ((Scheme.Modules.pullback i).obj F)).H1 ≤
      Module.finrank k (𝒲.sectionsOf x F).H1 := by
  obtain ⟨f, hf⟩ := exists_surjective_H1 i x F hF 𝒲
  rw [← LinearMap.range_eq_top] at hf
  rw [← finrank_top k, ← hf]
  exact LinearMap.finrank_range_le f

end AlgebraicGeometry.H1Dom

namespace AlgebraicGeometry
p2m_export "AlgebraicGeometry" "Scheme.Modules.Hom.app_smul Surjective SmoothOfRelativeDimension IsProper Scheme.Modules.pullback Scheme.Hom GeometricallyIntegral Scheme.Hom.appLE_comp_appLE Scheme.Hom.preimage_inf Scheme.Modules.Hom GeometricallyIntegral.isIntegral_of_subsingleton Spec IsIntegral Scheme IsClosedImmersion IsReduced Scheme.Modules.pullbackCongr Scheme.Modules.pullbackPushforwardAdjunction Scheme.Modules.pullbackId IsAffineOpen Scheme.Hom.preimage_sup Scheme.Modules IsAffineHom geometrically Scheme.Modules.pullbackComp Scheme.ΓSpecIso Scheme.Hom.appLE_eq_app Scheme.Modules.IsInvertible Scheme.TwoAffineOpenCover Scheme.TwoAffineOpenCover.algebraOfHom Scheme.TwoAffineOpenCover.moduleSectionsOfHom Scheme.TwoAffineOpenCover.sectionsOf_r0_apply Scheme.TwoAffineOpenCover.sectionsOf_r1_apply Scheme.Modules.dual Scheme.Modules.tensorPow_succ RelPicard.curveChange OModulePresheaf Scheme.Modules.pullbackTensorUnitObjIso RelPicard.isAlgEquivZero_of_isAlgEquivZero_pullback_curveChange_of_twoGluedSmoothCurves RelPicard.isAlgEquivZero_iff_eulerChar_sectionsOf_eq Scheme.Modules.IsInvertible.eulerChar_sectionsOf_tensor_eq_add_sub Scheme.Modules.IsInvertible.eulerChar_sectionsOf_dual_eq RelPicard.finrank_H0_unit_fibre_eq_one Scheme.TwoAffineOpenCover.exists_linearEquiv_sectionsOf_of_iso Scheme.TwoAffineOpenCover.exists_linearEquiv_sectionsOf_H0 Scheme.Modules.exists_linearEquiv_sections_pullback_of_isClosedImmersion_of_locallyTrivial Scheme.Modules.nonempty_pullback_tensorPow_iso OModulePresheaf.cechFinite_ofModules_of_locallyTrivial OModulePresheaf.cechFinite_toOrderedAffineCover_iff Scheme.TwoAffineOpenCover.ext_N2bC3"
namespace N2bCoreBwd
p2m_open "AlgebraicGeometry"

private theorem _root_.AlgebraicGeometry.Scheme.TwoAffineOpenCover.ext_N2bC3 {X : Scheme.{u}} {𝒱 𝒱' : X.TwoAffineOpenCover}
    (h0 : 𝒱.U0 = 𝒱'.U0) (h1 : 𝒱.U1 = 𝒱'.U1) : 𝒱 = 𝒱' := by
  cases 𝒱; cases 𝒱'; cases h0; cases h1; rfl

p2m_alias "P2MW.S_AlgebraicGeometry_RelPicard_isAlgEquivZero_of_finrank_H1_tensorPow_add_two_le_of_twoGluedSmoothCurves.AlgebraicGeometry.Scheme.TwoAffineOpenCover.ext_N2bC3" "AlgebraicGeometry.Scheme.TwoAffineOpenCover.ext_N2bC3"
theorem finrank_H0_H1_sectionsOf_eq_of_iso {k : Type u} [Field k] {X : Scheme.{u}} (x : X ⟶ Spec (CommRingCat.of k))
    {M M' : X.Modules} (e : M ≅ M') (𝒱 : X.TwoAffineOpenCover) :
    Module.finrank k (𝒱.sectionsOf x M).H0 = Module.finrank k (𝒱.sectionsOf x M').H0 ∧
      Module.finrank k (𝒱.sectionsOf x M).H1 = Module.finrank k (𝒱.sectionsOf x M').H1 := by
  obtain ⟨𝒱₁, h0, h1, ⟨e0⟩, ⟨e1⟩⟩ := Scheme.TwoAffineOpenCover.exists_linearEquiv_sectionsOf_of_iso x x (Iso.refl X)
    (Category.id_comp x) 𝒱 M' M (e ≪≫ ((Scheme.Modules.pullbackId X).app M').symm)
  have h0' : 𝒱₁.U0 = 𝒱.U0 := h0
  have h1' : 𝒱₁.U1 = 𝒱.U1 := h1
  obtain rfl : 𝒱₁ = 𝒱 := Scheme.TwoAffineOpenCover.ext_N2bC3 h0' h1'
  exact ⟨e0.finrank_eq, e1.finrank_eq⟩

theorem finrank_H0_sectionsOf_eq {k : Type u} [Field k] {X : Scheme.{u}} (x : X ⟶ Spec (CommRingCat.of k))
    (M : X.Modules) (𝒲 𝒲' : X.TwoAffineOpenCover) :
    Module.finrank k (𝒲.sectionsOf x M).H0 = Module.finrank k (𝒲'.sectionsOf x M).H0 := by
  letI := Scheme.TwoAffineOpenCover.moduleSectionsOfHom x M ⊤
  obtain ⟨e, -⟩ := Scheme.TwoAffineOpenCover.exists_linearEquiv_sectionsOf_H0 𝒲 x M
  obtain ⟨e', -⟩ := Scheme.TwoAffineOpenCover.exists_linearEquiv_sectionsOf_H0 𝒲' x M
  exact (e.symm.trans e').finrank_eq

section Curve

variable {k : Type u} [Field k] [IsAlgClosed k] {Y : Scheme.{u}} (y : Y ⟶ Spec (CommRingCat.of k))
  [IsIntegral Y] [IsProper y] [SmoothOfRelativeDimension 1 y] (𝒱 : Y.TwoAffineOpenCover)

def chi (G : Y.Modules) : ℤ :=
  (Module.finrank k (𝒱.sectionsOf y G).H0 : ℤ) - Module.finrank k (𝒱.sectionsOf y G).H1

omit [IsAlgClosed k] [IsIntegral Y] [IsProper y] [SmoothOfRelativeDimension 1 y] in
theorem chi_congr {G G' : Y.Modules} (e : G ≅ G') : chi y 𝒱 G = chi y 𝒱 G' := by
  obtain ⟨h0, h1⟩ := finrank_H0_H1_sectionsOf_eq_of_iso y e 𝒱
  simp only [chi, h0, h1]

theorem chi_tensor (G G' : Y.Modules) (hG : Scheme.Modules.IsInvertible G) (hG' : Scheme.Modules.IsInvertible G') :
    chi y 𝒱 (G ⊗ G') = chi y 𝒱 G + chi y 𝒱 G' - chi y 𝒱 (SheafOfModules.unit Y.ringCatSheaf) :=
  Scheme.Modules.IsInvertible.eulerChar_sectionsOf_tensor_eq_add_sub k y G G' hG hG' 𝒱

theorem chi_dual (G : Y.Modules) (hG : Scheme.Modules.IsInvertible G) :
    chi y 𝒱 (Scheme.Modules.dual G) = 2 * chi y 𝒱 (SheafOfModules.unit Y.ringCatSheaf) - chi y 𝒱 G :=
  Scheme.Modules.IsInvertible.eulerChar_sectionsOf_dual_eq k y G hG 𝒱

theorem chi_tensorPow (G : Y.Modules) (hG : Scheme.Modules.IsInvertible G) :
    ∀ n : ℕ, chi y 𝒱 (G.tensorPow n) - chi y 𝒱 (SheafOfModules.unit Y.ringCatSheaf) =
      n * (chi y 𝒱 G - chi y 𝒱 (SheafOfModules.unit Y.ringCatSheaf))
  | 0 => by
      change chi y 𝒱 (SheafOfModules.unit Y.ringCatSheaf) - _ = _
      simp
  | n + 1 => by
      rw [Scheme.Modules.tensorPow_succ, chi_tensor y 𝒱 _ _ (hG.tensorPow n) hG]
      have := chi_tensorPow G hG n
      push_cast
      linarith

end Curve

theorem finrank_H0_unit_eq_one {k : Type u} [Field k] [IsAlgClosed k] {Y : Scheme.{u}} (y : Y ⟶ Spec (CommRingCat.of k))
    [IsProper y] [SmoothOfRelativeDimension 1 y] [GeometricallyIntegral y] (𝒲 : Y.TwoAffineOpenCover) :
    Module.finrank k (𝒲.sectionsOf y (SheafOfModules.unit Y.ringCatSheaf)).H0 = 1 := by

  let P := pullback y (𝟙 (Spec (CommRingCat.of k)))
  haveI : IsIso (pullback.fst y (𝟙 (Spec (CommRingCat.of k)))) := inferInstance
  let φ : Y ≅ P := (asIso (pullback.fst y (𝟙 (Spec (CommRingCat.of k))))).symm
  have hφ : φ.hom ≫ pullback.snd y (𝟙 _) = y := by
    have hc : pullback.snd y (𝟙 (Spec (CommRingCat.of k))) = pullback.fst y (𝟙 _) ≫ y := by
      rw [pullback.condition, Category.comp_id]
    simp [φ, hc]

  haveI : IsAffineHom (pullback.fst y (𝟙 (Spec (CommRingCat.of k)))) := inferInstance
  let 𝒱' : P.TwoAffineOpenCover := H1Dom.comap 𝒲 (pullback.fst y (𝟙 (Spec (CommRingCat.of k))))
  have h1 := RelPicard.finrank_H0_unit_fibre_eq_one y k (𝟙 _) 𝒱'
  obtain ⟨𝒱₁, -, -, ⟨e0⟩, -⟩ := Scheme.TwoAffineOpenCover.exists_linearEquiv_sectionsOf_of_iso y (pullback.snd y (𝟙 _))
    φ hφ 𝒱' (𝟙_ P.Modules) (SheafOfModules.unit Y.ringCatSheaf) (Scheme.Modules.pullbackTensorUnitObjIso φ.hom).symm
  rw [finrank_H0_sectionsOf_eq y _ 𝒲 𝒱₁, e0.finrank_eq]
  exact h1

end AlgebraicGeometry.N2bCoreBwd

namespace AlgebraicGeometry
p2m_export "AlgebraicGeometry" "Scheme.Modules.Hom.app_smul Surjective SmoothOfRelativeDimension IsProper Scheme.Modules.pullback Scheme.Hom GeometricallyIntegral Scheme.Hom.appLE_comp_appLE Scheme.Hom.preimage_inf Scheme.Modules.Hom GeometricallyIntegral.isIntegral_of_subsingleton Spec IsIntegral Scheme IsClosedImmersion IsReduced Scheme.Modules.pullbackCongr Scheme.Modules.pullbackPushforwardAdjunction Scheme.Modules.pullbackId IsAffineOpen Scheme.Hom.preimage_sup Scheme.Modules IsAffineHom geometrically Scheme.Modules.pullbackComp Scheme.ΓSpecIso Scheme.Hom.appLE_eq_app Scheme.Modules.IsInvertible Scheme.TwoAffineOpenCover Scheme.TwoAffineOpenCover.algebraOfHom Scheme.TwoAffineOpenCover.moduleSectionsOfHom Scheme.TwoAffineOpenCover.sectionsOf_r0_apply Scheme.TwoAffineOpenCover.sectionsOf_r1_apply Scheme.Modules.dual Scheme.Modules.tensorPow_succ RelPicard.curveChange OModulePresheaf Scheme.Modules.pullbackTensorUnitObjIso RelPicard.isAlgEquivZero_of_isAlgEquivZero_pullback_curveChange_of_twoGluedSmoothCurves RelPicard.isAlgEquivZero_iff_eulerChar_sectionsOf_eq Scheme.Modules.IsInvertible.eulerChar_sectionsOf_tensor_eq_add_sub Scheme.Modules.IsInvertible.eulerChar_sectionsOf_dual_eq RelPicard.finrank_H0_unit_fibre_eq_one Scheme.TwoAffineOpenCover.exists_linearEquiv_sectionsOf_of_iso Scheme.TwoAffineOpenCover.exists_linearEquiv_sectionsOf_H0 Scheme.Modules.exists_linearEquiv_sections_pullback_of_isClosedImmersion_of_locallyTrivial Scheme.Modules.nonempty_pullback_tensorPow_iso OModulePresheaf.cechFinite_ofModules_of_locallyTrivial OModulePresheaf.cechFinite_toOrderedAffineCover_iff Scheme.TwoAffineOpenCover.ext_N2bC3"
namespace N2bCoreBwd
p2m_open "AlgebraicGeometry"

def tensorPowIso {X : Scheme.{u}} {L L' : X.Modules} (e : L ≅ L') : ∀ n : ℕ, L.tensorPow n ≅ L'.tensorPow n
  | 0 => Iso.refl _
  | n + 1 => tensorPowIso e n ⊗ᵢ e

theorem finite_H1 {k : Type u} [Field k] {X : Scheme.{u}} (x : X ⟶ Spec (CommRingCat.of k)) [IsProper x]
    (G : X.Modules) (hG : Scheme.Modules.IsInvertible G) (𝒲 : X.TwoAffineOpenCover) :
    Module.Finite k (𝒲.sectionsOf x G).H1 := by
  have hcf := OModulePresheaf.cechFinite_ofModules_of_locallyTrivial x G hG.1 𝒲.toOrderedAffineCover
  exact ((OModulePresheaf.cechFinite_toOrderedAffineCover_iff _ _).mp hcf).2

theorem component {k : Type u} [Field k] [IsAlgClosed k] {X Y : Scheme.{u}} (x : X ⟶ Spec (CommRingCat.of k)) [IsProper x]
    (y : Y ⟶ Spec (CommRingCat.of k)) [IsProper y] [SmoothOfRelativeDimension 1 y] [GeometricallyIntegral y]
    (j : Y ⟶ X) [IsClosedImmersion j] (hj : j ≫ x = y)
    (L : X.Modules) (hL : Scheme.Modules.IsInvertible L) (K : ℕ) (𝒲 : X.TwoAffineOpenCover)
    (hpos : Module.finrank k (𝒲.sectionsOf x (L.tensorPow K)).H1 + 2 ≤ K)
    (hneg : Module.finrank k (𝒲.sectionsOf x ((Scheme.Modules.dual L).tensorPow K)).H1 + 2 ≤ K) :
    IsAlgEquivZero y ((Scheme.Modules.pullback j).obj L) := by
  subst hj
  haveI : IsIntegral Y := GeometricallyIntegral.isIntegral_of_subsingleton (j ≫ x)
  let 𝒲j : Y.TwoAffineOpenCover := H1Dom.comap 𝒲 j
  have hLj : Scheme.Modules.IsInvertible ((Scheme.Modules.pullback j).obj L) := hL.pullback j
  by_contra hne

  have hd : chi (j ≫ x) 𝒲j ((Scheme.Modules.pullback j).obj L) ≠ chi (j ≫ x) 𝒲j (SheafOfModules.unit Y.ringCatSheaf) := by
    intro h
    exact hne ((RelPicard.isAlgEquivZero_iff_eulerChar_sectionsOf_eq k (j ≫ x) _ hLj 𝒲j).mpr h)

  have hH0 := finrank_H0_unit_eq_one (j ≫ x) 𝒲j
  have hchi1 : chi (j ≫ x) 𝒲j (SheafOfModules.unit Y.ringCatSheaf) ≤ 1 := by
    simp only [chi, hH0]
    push_cast
    linarith [Int.natCast_nonneg (Module.finrank k (𝒲j.sectionsOf (j ≫ x) (SheafOfModules.unit Y.ringCatSheaf)).H1)]
  set a := chi (j ≫ x) 𝒲j ((Scheme.Modules.pullback j).obj L) - chi (j ≫ x) 𝒲j (SheafOfModules.unit Y.ringCatSheaf)
    with ha
  have ha0 : a ≠ 0 := sub_ne_zero.mpr hd
  rcases lt_or_gt_of_ne ha0 with hlt | hgt
  ·
    obtain ⟨e⟩ := Scheme.Modules.nonempty_pullback_tensorPow_iso j L K
    haveI := finite_H1 x (L.tensorPow K) (hL.tensorPow K) 𝒲
    have hdom := H1Dom.finrank_H1_pullback_le j x (L.tensorPow K) (hL.tensorPow K) 𝒲
    have hiso := (finrank_H0_H1_sectionsOf_eq_of_iso (j ≫ x) e 𝒲j).2
    have hpow := chi_tensorPow (j ≫ x) 𝒲j _ hLj K
    rw [← ha] at hpow
    have hKa : (K : ℤ) * a ≤ -K := by nlinarith

    have hchiG : -(Module.finrank k (𝒲j.sectionsOf (j ≫ x) (((Scheme.Modules.pullback j).obj L).tensorPow K)).H1 : ℤ) ≤
        chi (j ≫ x) 𝒲j (((Scheme.Modules.pullback j).obj L).tensorPow K) := by
      simp only [chi]
      linarith [Int.natCast_nonneg (Module.finrank k (𝒲j.sectionsOf (j ≫ x) (((Scheme.Modules.pullback j).obj L).tensorPow K)).H0)]
    have h1 : (Module.finrank k (𝒲j.sectionsOf (j ≫ x) ((Scheme.Modules.pullback j).obj (L.tensorPow K))).H1 : ℤ) ≤
        Module.finrank k (𝒲.sectionsOf x (L.tensorPow K)).H1 := by exact_mod_cast hdom
    rw [hiso] at h1
    have h2 : (Module.finrank k (𝒲.sectionsOf x (L.tensorPow K)).H1 : ℤ) + 2 ≤ K := by exact_mod_cast hpos
    linarith
  ·
    obtain ⟨e₁⟩ := Scheme.Modules.nonempty_pullback_tensorPow_iso j (Scheme.Modules.dual L) K
    obtain ⟨eD⟩ := hL.pullback_dual j
    have e := e₁ ≪≫ tensorPowIso eD K
    haveI := finite_H1 x ((Scheme.Modules.dual L).tensorPow K) (hL.dual.1.tensorPow K) 𝒲
    have hdom := H1Dom.finrank_H1_pullback_le j x ((Scheme.Modules.dual L).tensorPow K) (hL.dual.1.tensorPow K) 𝒲
    have hiso := (finrank_H0_H1_sectionsOf_eq_of_iso (j ≫ x) e 𝒲j).2
    have hdual := chi_dual (j ≫ x) 𝒲j _ hLj
    have hpow := chi_tensorPow (j ≫ x) 𝒲j _ hLj.dual.1 K
    rw [hdual] at hpow
    have hKa : (K : ℤ) * (-a) ≤ -K := by nlinarith
    have hchiG : -(Module.finrank k (𝒲j.sectionsOf (j ≫ x)
        ((Scheme.Modules.dual ((Scheme.Modules.pullback j).obj L)).tensorPow K)).H1 : ℤ) ≤
        chi (j ≫ x) 𝒲j ((Scheme.Modules.dual ((Scheme.Modules.pullback j).obj L)).tensorPow K) := by
      simp only [chi]
      linarith [Int.natCast_nonneg (Module.finrank k (𝒲j.sectionsOf (j ≫ x)
        ((Scheme.Modules.dual ((Scheme.Modules.pullback j).obj L)).tensorPow K)).H0)]
    have h1 : (Module.finrank k (𝒲j.sectionsOf (j ≫ x)
        ((Scheme.Modules.pullback j).obj ((Scheme.Modules.dual L).tensorPow K))).H1 : ℤ) ≤
        Module.finrank k (𝒲.sectionsOf x ((Scheme.Modules.dual L).tensorPow K)).H1 := by exact_mod_cast hdom
    rw [hiso] at h1
    have h2 : (Module.finrank k (𝒲.sectionsOf x ((Scheme.Modules.dual L).tensorPow K)).H1 : ℤ) + 2 ≤ K := by
      exact_mod_cast hneg
    rw [ha] at hKa
    linarith

theorem curveChange_fst {R : Type u} [CommRing R] {C C' T : Scheme.{u}} {c : C ⟶ Spec (CommRingCat.of R)}
    {c' : C' ⟶ Spec (CommRingCat.of R)} (f : C' ⟶ C) (hf : f ≫ c = c') (t : T ⟶ Spec (CommRingCat.of R)) :
    RelPicard.curveChange f hf t ≫ pullback.fst c t = pullback.fst c' t ≫ f := by
  delta RelPicard.curveChange
  exact pullback.lift_fst _ _ _

theorem main {k : Type u} [Field k] [IsAlgClosed k]
    {X C₁ C₂ : Scheme.{u}} (x : X ⟶ Spec (CommRingCat.of k)) [IsProper x] (hXred : IsReduced X)
    (c₁ : C₁ ⟶ Spec (CommRingCat.of k)) (c₂ : C₂ ⟶ Spec (CommRingCat.of k))
    [IsProper c₁] [SmoothOfRelativeDimension 1 c₁] [GeometricallyIntegral c₁]
    [IsProper c₂] [SmoothOfRelativeDimension 1 c₂] [GeometricallyIntegral c₂]
    (i₁ : SchemeHomOver c₁ x) (i₂ : SchemeHomOver c₂ x) [IsClosedImmersion i₁.1] [IsClosedImmersion i₂.1]
    (hjs : ∀ z : X, z ∈ Set.range i₁.1.base ∨ z ∈ Set.range i₂.1.base)
    (hcr : IsReduced (pullback i₁.1 i₂.1)) (s : ℕ) (hs : Nat.card ↥(pullback i₁.1 i₂.1) = s) (hs0 : 0 < s)
    (L : X.Modules) (hL : Scheme.Modules.IsInvertible L) (K : ℕ) (𝒲 : X.TwoAffineOpenCover)
    (hpos : Module.finrank k (𝒲.sectionsOf x (L.tensorPow K)).H1 + 2 ≤ K)
    (hneg : Module.finrank k (𝒲.sectionsOf x ((Scheme.Modules.dual L).tensorPow K)).H1 + 2 ≤ K) :
    IsAlgEquivZero x L := by
  have h₁ := component x c₁ i₁.1 i₁.2 L hL K 𝒲 hpos hneg
  have h₂ := component x c₂ i₂.1 i₂.2 L hL K 𝒲 hpos hneg

  have lift : ∀ {Y : Scheme.{u}} (y : Y ⟶ Spec (CommRingCat.of k)) (i : SchemeHomOver y x),
      IsAlgEquivZero y ((Scheme.Modules.pullback i.1).obj L) →
      IsAlgEquivZero (pullback.snd y (𝟙 _))
        ((Scheme.Modules.pullback (RelPicard.curveChange i.1 i.2 (𝟙 _))).obj
          ((Scheme.Modules.pullback (pullback.fst x (𝟙 _))).obj L)) := by
    intro Y y i h
    have h' := h.pullback (pullback.fst y (𝟙 _)) (a' := pullback.snd y (𝟙 _))
      (by rw [pullback.condition, Category.comp_id])
    refine h'.of_iso ?_
    exact (Scheme.Modules.pullbackComp _ _).app L ≪≫
      (Scheme.Modules.pullbackCongr (curveChange_fst i.1 i.2 (𝟙 _)).symm).app L ≪≫
      ((Scheme.Modules.pullbackComp _ _).app L).symm
  have hglue := RelPicard.isAlgEquivZero_of_isAlgEquivZero_pullback_curveChange_of_twoGluedSmoothCurves x hXred c₁ c₂
    i₁ i₂ hjs hcr s hs hs0 k (𝟙 _) ((Scheme.Modules.pullback (pullback.fst x (𝟙 _))).obj L) (hL.pullback _)
    (lift c₁ i₁ h₁) (lift c₂ i₂ h₂)

  let s₀ : X ⟶ pullback x (𝟙 (Spec (CommRingCat.of k))) := pullback.lift (𝟙 X) x (by simp)
  have hs₀ : s₀ ≫ pullback.snd x (𝟙 _) = x := pullback.lift_snd _ _ _
  have h := hglue.pullback s₀ (a' := x) hs₀
  refine h.of_iso ?_
  exact (Scheme.Modules.pullbackComp _ _).app L ≪≫
    (Scheme.Modules.pullbackCongr (show s₀ ≫ pullback.fst x (𝟙 _) = 𝟙 X from pullback.lift_fst _ _ _)).app L ≪≫
    (Scheme.Modules.pullbackId X).app L

end AlgebraicGeometry.N2bCoreBwd

end

theorem solution
    {k : Type u} [Field k] [IsAlgClosed k]
    {X C₁ C₂ : Scheme.{u}} (x : X ⟶ Spec (CommRingCat.of k)) [IsProper x] (hXred : IsReduced X)
    (c₁ : C₁ ⟶ Spec (CommRingCat.of k)) (c₂ : C₂ ⟶ Spec (CommRingCat.of k))
    [IsProper c₁] [SmoothOfRelativeDimension 1 c₁] [GeometricallyIntegral c₁]
    [IsProper c₂] [SmoothOfRelativeDimension 1 c₂] [GeometricallyIntegral c₂]
    (i₁ : SchemeHomOver c₁ x) (i₂ : SchemeHomOver c₂ x) [IsClosedImmersion i₁.1] [IsClosedImmersion i₂.1]
    (hjs : ∀ z : X, z ∈ Set.range i₁.1.base ∨ z ∈ Set.range i₂.1.base)
    (hcr : IsReduced (pullback i₁.1 i₂.1)) (s : ℕ) (hs : Nat.card ↥(pullback i₁.1 i₂.1) = s) (hs0 : 0 < s)
    (L : X.Modules) (hL : Scheme.Modules.IsInvertible L) (K : ℕ) (𝒲 : X.TwoAffineOpenCover)
    (hpos : Module.finrank k (𝒲.sectionsOf x (L.tensorPow K)).H1 + 2 ≤ K)
    (hneg : Module.finrank k (𝒲.sectionsOf x ((Scheme.Modules.dual L).tensorPow K)).H1 + 2 ≤ K) :
    IsAlgEquivZero x L :=
  AlgebraicGeometry.N2bCoreBwd.main x hXred c₁ c₂ i₁ i₂ hjs hcr s hs hs0 L hL K 𝒲 hpos hneg

end S_AlgebraicGeometry_RelPicard_isAlgEquivZero_of_finrank_H1_tensorPow_add_two_le_of_twoGluedSmoothCurves
end P2MW
export P2MW.S_AlgebraicGeometry_RelPicard_isAlgEquivZero_of_finrank_H1_tensorPow_add_two_le_of_twoGluedSmoothCurves (solution)
