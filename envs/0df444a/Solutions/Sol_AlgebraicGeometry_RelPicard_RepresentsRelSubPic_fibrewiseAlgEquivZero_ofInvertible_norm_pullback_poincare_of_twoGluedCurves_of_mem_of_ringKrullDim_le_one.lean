-- Prove2me | solution 1 for AlgebraicGeometry.RelPicard.RepresentsRelSubPic.fibrewiseAlgEquivZero_ofInvertible_norm_pullback_poincare_of_twoGluedCurves_of_mem_of_ringKrullDim_le_one
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:03.589526+00:00
-- url     : https://prove2.me/submissions/ca1bd8a5-f9b9-5e88-b469-a5401ed797d1

import Mathlib
import Definitions.Def_AlgebraicGeometry_ModulesPullbackMonoidal
import Theorems.Thm_AlgebraicGeometry_RelPicard_IsAlgEquivZero_pullback_ofInvertible_of_iso_normModule_morphismRestrict
import Theorems.Thm_AlgebraicGeometry_TwoGluedCurves_isAlgEquivZero_fibre_of_isAlgEquivZero_fibre_of_preconnectedSpace
import Theorems.Thm_AlgebraicGeometry_RelPicard_geometricallyConnected_of_representsRelSubPic_algEquivZeroCut
import Theorems.Thm_AlgebraicGeometry_RelPicard_RepresentsRelSubPic_nonempty_pullback_zeroSection_norm_pullback_poincare_iso_unit_of_mem_of_ringKrullDim_le_one
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_IsInvertible_nonempty_iso_tensorUnit_of_field
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import Definitions.Def_AlgebraicGeometry_RepresentsRelSubPic
import Definitions.Def_AlgebraicGeometry_RelPicardAlgEquivZeroCut
import Definitions.Def_AlgebraicGeometry_RelPicardAlgEquivZeroGroupCut
import Definitions.Def_AlgebraicGeometry_RelPicardPullback
import Definitions.Def_AlgebraicGeometry_ModulesRigidify
import Definitions.Def_AlgebraicGeometry_RigidifiedLineBundleOfInvertible
import Definitions.Def_AlgebraicGeometry_ModulesNormModule
import Definitions.Def_AlgebraicGeometry_SmoothProperCurveBase
import Definitions.Def_AlgebraicGeometry_RelativePic0DesignationBaseChange
import Definitions.Def_GoodReductionJacobian_RelativeGroupLawBaseChange
import Definitions.Def_AlgebraicGeometry_NeronModelEndomorphismExtension
import Definitions.Def_AlgebraicGeometry_TwoAffineOpenCover
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_RelPicard_RepresentsRelSubPic_fibrewiseAlgEquivZero_ofInvertible_norm_pullback_poincare_of_twoGluedCurves_of_mem_of_ringKrullDim_le_one
p2m_attr_erase "instance" "AlgebraicGeometry.OModulePresheaf.isScalarTower AlgebraicGeometry.Scheme.OrderedAffineCover.instLinearOrder AlgebraicGeometry.OModulePresheaf.module AlgebraicGeometry.Scheme.OrderedAffineCover.instFintype AlgebraicGeometry.Scheme.OrderedAffineCover.instFintypeIdx AlgebraicGeometry.OModulePresheaf.addCommGroup AlgebraicGeometry.Scheme.OrderedAffineCover.instDecidableEqIdx AlgebraicGeometry.OModulePresheaf.moduleSections AlgebraicGeometry.OModulePresheaf.instSubsingletonObjZero AlgebraicGeometry.OModulePresheaf.Leray.relAltC_scalarTower AlgebraicGeometry.OModulePresheaf.Leray.ker_relAltd_modΓ AlgebraicGeometry.OModulePresheaf.Leray.relAltC_modΓ AlgebraicGeometry.OModulePresheaf.Leray.biC_abGrp AlgebraicGeometry.OModulePresheaf.Leray.relAltH_modΓ AlgebraicGeometry.OModulePresheaf.Leray.ker_relAltd_smul AlgebraicGeometry.OModulePresheaf.Leray.relAltH_scalarTower AlgebraicGeometry.OModulePresheaf.Leray.relAltH_smul AlgebraicGeometry.OModulePresheaf.Leray.biC_module AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instDecidableEqIdx AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instFintype AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instLinearOrder AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instFintypeIdx DoubleComplex.instModuleE₂I DoubleComplex.Bounded.modR DoubleComplex.instModuleE₂II DoubleComplex.instAddCommGroupE₂II DoubleComplex.Bounded.abGrp DoubleComplex.instAddCommGroupE₂I AlgebraicGeometry.ChowDatum.hι_closed AlgebraicGeometry.ChowDatumProj.hιN_closed AlgebraicGeometry.ChowDatumProj.hp_proper AlgebraicGeometry.ChowDatum.hp_isoU AlgebraicGeometry.ChowDatum.hp_proper AlgebraicGeometry.ProjSpace.algebraAway AlgebraicGeometry.ProjSpace.instIsProperProdOverπ AlgebraicGeometry.ChowDatumProj.hp_isoU AlgebraicGeometry.ProjSpace.isProper_π AlgebraicGeometry.ProjSpace.finiteType_mvPolynomial ProjSpaceCech.GradedModule.H.module ProjSpaceCech.GradedModule.H.addCommGroup"
p2m_attr_erase "instance" "ProjSpaceCech.GradedModule.sec.instAdd ProjSpaceCech.GradedModule.sec.instNeg ProjSpaceCech.GradedModule.acg ProjSpaceCech.GradedModule.Frac.setoid ProjSpaceCech.GradedModule.modR ProjSpaceCech.GradedModule.sec.instModule ProjSpaceCech.GradedModule.sec.instAddCommGroup ProjSpaceCech.GradedModule.sec.instZero ProjSpaceCech.GradedModule.Presentation.fJ ProjSpaceCech.GradedModule.sec.instSMul ProjSpaceCech.Twist.H.module ProjSpaceCech.Idx.instFintype ProjSpaceCech.Twist.H.addCommGroup ProjSpaceCech.Idx.instDecidableEq ProjSpaceCech.Twist.Mon.instDecidableEq ProjSpaceCech.Twist.cochain.instAddCommGroup ProjSpaceCech.Twist.cochain.instModule AlgebraicGeometry.RelEffCartierDiv.isIso_subschemeIota_snd_of_degree_one AlgebraicGeometry.isIso_ker_graphOver_subschemeIota_snd AlgebraicGeometry.isClosedImmersion_graphOver AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instNeg AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instSMulInt AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instAddCommGroup AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instAdd AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instSub AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instModuleCarrierObjOppositeOpensCarrierCarrierCommRingCatPresheafOpOpensTop AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instSMulCarrierObjOppositeOpensCarrierCarrierCommRingCatPresheafOpOpensTop AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instSMulNat AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instZero AlgebraicGeometry.RelEffCartierDiv.subsingleton_of_degree_zero AlgebraicCurve.Place.instIsScalarTowerSubtypeMemValuationSubringToValuationSubring AlgebraicCurve.Divisor.instDistribMulActionAlgEquiv AlgebraicCurve.Place.instSMulAlgEquiv AlgebraicCurve.Place.instIsPrincipalIdealRingSubtypeMemValuationSubringToValuationSubring AlgebraicCurve.Place.instIsDiscreteValuationRingSubtypeMemValuationSubringToValuationSubring AlgebraicCurve.Pic0.instDistribMulActionAlgEquiv AlgebraicCurve.Place.instAlgebraSubtypeMemValuationSubringToValuationSubring AlgebraicCurve.Place.instMulActionAlgEquiv AlgebraicCurve.Pic0.instSMulAlgEquiv AlgebraicCurve.IsCurveOver.instNontrivialKaehler"
p2m_attr_erase "instance" "AlgebraicCurve.IsCurveOver.instFreeKaehler AlgebraicCurve.IsCurveOver.toHasPrincipalDivisors AlgebraicCurve.IsCurveOver.instFiniteResidue AlgebraicCurve.CurveModel.isProper AlgebraicCurve.CurveModel.isIntegral AlgebraicCurve.CurveModel.smooth AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.instFundamentalIdentityOfSumRamificationInertia AlgebraicCurve.Place.instIsScalarTowerResidueFieldRestrictPushforward AlgebraicCurve.Place.instAlgebraResidueFieldRestrictPushforward AlgebraicCurve.Place.instIsLocalHomRestrictInclusion AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.SemilinearAut.instDistribMulActionSubtypeProdRingAutMemSubgroupPic0 AlgebraicCurve.SemilinearAut.instDistribMulActionSubtypeProdRingAutMemSubgroupDivisor AlgebraicCurve.Pic0.instModuleZModTorsion AlgebraicCurve.SemilinearAut.instSMulSubtypeProdRingAutMemSubgroupPlace AlgebraicCurve.SemilinearAut.instDistribMulActionTorsion AlgebraicCurve.SemilinearAut.instSMulSubtypeProdRingAutMemSubgroupPic0 AlgebraicCurve.SemilinearAut.instSMulTorsion AlgebraicCurve.SemilinearAut.instMulActionSubtypeProdRingAutMemSubgroupPlace AlgebraicCurve.SemilinearAut.instSMulCommClassZModTorsion AlgebraicCurve.SemilinearAut.instMulSemiringActionSubtypeProdRingAutMemSubgroup instDecEqAlgebraicClosureRat WeierstrassCurve.Affine.Point.instDistribMulActionAlgEquiv WeierstrassCurve.Affine.Point.instModuleZModTorsionBy WeierstrassCurve.Affine.Point.instSMulTorsionBy WeierstrassCurve.Affine.Point.instDistribMulActionTorsionBy WeierstrassCurve.Affine.Point.instSMulAlgEquiv WeierstrassCurve.Affine.Point.instSMulCommClassAlgEquivZModTorsionBy AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions AlgebraicCurve.instHasLocalResidue_of_hasCanonicalLocalResidueK AlgebraicCurve.instHasCanonicalLocalResidueK_of_hasCanonicalLocalResidueKStar AlgebraicCurve.Place.kw_ffgc_finiteDimensional_adicCompletion instAlgebraSubtypeMemValuationSubring_definitions AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersIntegersCompletion"
p2m_attr_erase "instance" "ModularCurve.KwF4gRRTate.instAlgebraKAdicCompletionIntegers AlgebraicCurve.Place.kw_ffgc_continuousSMul_adicCompletionComap AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersCompletionCompletion IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions AlgebraicCurve.instHasCanonicalLocalResidueK AlgebraicCurve.Place.instAlgebra_restrictResidueField AlgebraicCurve.Place.instIsScalarTower_restrictResidueField AlgebraicCurve.instHasLocalResidue AlgebraicCurve.HasSeparableResidue.of_perfectField_of_isCurveOver AlgebraicCurve.HasSeparableResidue.of_perfectField AlgebraicCurve.Place.instIsLocalHom_restrictSubringHom AlgebraicCurve.instHasCanonicalLocalResidueKStar ModularCurve.KwNo6Pin.isLocalRing_completion SheafOfModules.isIso_ihomModelToIhom"
p2m_attr_erase "simp" "PresheafOfModules.pushforwardCongr_inv_app_app_apply PresheafOfModules.pushforwardNatTrans_app_app_apply PresheafOfModules.pushforwardCongr_hom_app_app_apply AlgebraicGeometry.tilde.functorCompPullbackSpecIso_app TwoChartCech.Mumford.dK_apply TwoChartCech.Mumford.ι0_apply TwoChartCech.Mumford.ι1_apply TwoChartCech.KerCoprod.dK_apply TwoChartCech.KerCoprod.ι1_apply TwoChartCech.KerCoprod.ι0_apply AlgebraicGeometry.Scheme.Modules.tensorSections_zero_right AlgebraicGeometry.Scheme.Modules.map_unitSection AlgebraicGeometry.Scheme.Modules.tensorSectionsBilin_apply AlgebraicGeometry.Scheme.Modules.tensorPowSection_zero AlgebraicGeometry.Scheme.Modules.tensorSections_zero_left AlgebraicGeometry.Scheme.Modules.tensorPow_zero AlgebraicGeometry.Scheme.Modules.tensorPow_succ AlgebraicGeometry.Scheme.Modules.toUnitSection_ofUnitSection AlgebraicGeometry.Scheme.Modules.pullbackSection_def AlgebraicGeometry.Scheme.Modules.ofUnitSection_toUnitSection AlgebraicGeometry.RelEffCartierDiv.toRelEffDivisor_ofRelEffDivisor AlgebraicGeometry.RelEffCartierDiv.toRelEffDivisor_I AlgebraicGeometry.mapOnProdOver_fst_assoc AlgebraicGeometry.RelEffCartierDiv.mk.sizeOf_spec AlgebraicGeometry.RelEffCartierDiv.mk.injEq AlgebraicGeometry.mapOnProdOver_snd AlgebraicGeometry.mapOnProdOver_fst AlgebraicGeometry.mapOnProdOver_snd_assoc AlgebraicGeometry.mapOnProdOver_id AlgebraicCurve.RelEffDivisor.mk.sizeOf_spec AlgebraicCurve.mapOnProd_fst AlgebraicCurve.mapOnProd_fst_assoc AlgebraicCurve.mapOnProd_snd AlgebraicCurve.UnivDivisorPack.mk.injEq AlgebraicCurve.RelEffDivisor.mk.injEq AlgebraicCurve.UnivDivisorPack.mk.sizeOf_spec AlgebraicCurve.mapOnProd_snd_assoc AlgebraicGeometry.RelPicard.thetaBundle_def AlgebraicGeometry.RelPicard.picardBundle_def AlgebraicGeometry.Scheme.OrderedAffineCover.mk.injEq"
p2m_attr_erase "simp" "AlgebraicGeometry.OModulePresheaf.mk.sizeOf_spec AlgebraicGeometry.Scheme.OrderedAffineCover.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.mk.injEq AlgebraicGeometry.OModulePresheaf.prod_obj AlgebraicGeometry.OModulePresheaf.restrOpen_obj AlgebraicGeometry.OModulePresheaf.DevissageStep.mk.injEq AlgebraicGeometry.OModulePresheaf.pushforward_obj AlgebraicGeometry.OModulePresheaf.im_obj AlgebraicGeometry.OModulePresheaf.pow_obj AlgebraicGeometry.OModulePresheaf.fstHom_app AlgebraicGeometry.OModulePresheaf.ker_obj AlgebraicGeometry.OModulePresheaf.coker_obj AlgebraicGeometry.OModulePresheaf.DevissageStep.mk.sizeOf_spec AlgebraicGeometry.Scheme.OrderedAffineCover.preimage_U AlgebraicGeometry.OModulePresheaf.sndHom_app AlgebraicGeometry.OModulePresheaf.Hom.mk.injEq AlgebraicGeometry.OModulePresheaf.Hom.id_app AlgebraicGeometry.OModulePresheaf.AffHom.appSections_apply AlgebraicGeometry.OModulePresheaf.AffHom.comp_app AlgebraicGeometry.OModulePresheaf.AffSES.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.AffHom.kerMap_coe AlgebraicGeometry.OModulePresheaf.AffHom.id_app AlgebraicGeometry.OModulePresheaf.Hom.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.Hom.toAffHom_app AlgebraicGeometry.OModulePresheaf.SES.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.AffHom.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.Hom.comp_app AlgebraicGeometry.OModulePresheaf.SES.mk.injEq AlgebraicGeometry.OModulePresheaf.AffHom.mk.injEq AlgebraicGeometry.OModulePresheaf.Hom.appSections_apply AlgebraicGeometry.OModulePresheaf.AffSES.mk.injEq AlgebraicGeometry.OModulePresheaf.Leray.restrictToPreimage_U AlgebraicGeometry.Scheme.OrderedAffineCover.toCoverOf_U AlgebraicGeometry.Scheme.OrderedAffineCoverOf.mk.sizeOf_spec AlgebraicGeometry.Scheme.OrderedAffineCoverOf.mk.injEq AlgebraicGeometry.Scheme.OrderedAffineCover.restrict_U DoubleComplex.Bounded.mk.injEq DoubleComplex.Bounded.mk.sizeOf_spec DoubleComplex.Convergence.mk.injEq DoubleComplex.Convergence.mk.sizeOf_spec"
p2m_attr_erase "simp" "DoubleComplex.SubQuot.mk.sizeOf_spec DoubleComplex.SubQuot.mk.injEq AlgebraicGeometry.ChowDatumProj.mk.sizeOf_spec AlgebraicGeometry.ChowDatum.mk.sizeOf_spec AlgebraicGeometry.ChowDatumProj.mk.injEq AlgebraicGeometry.ChowDatum.mk.injEq ProjSpaceCech.GradedModule.mk.injEq ProjSpaceCech.GradedModule.mk.sizeOf_spec ProjSpaceCech.GradedModule.Frac.mk.sizeOf_spec ProjSpaceCech.GradedModule.Presentation.mk.injEq ProjSpaceCech.GradedModule.Frac.mk.injEq ProjSpaceCech.GradedModule.Presentation.mk.sizeOf_spec ProjSpaceCech.GradedModule.Hom.shift_toLinearMap ProjSpaceCech.GradedModule.Hom.mk.sizeOf_spec ProjSpaceCech.GradedModule.Hom.mk.injEq AlgebraicGeometry.RelPicard.fst_toProdSpec AlgebraicGeometry.RelPicard.toProdSpec_fst_assoc AlgebraicGeometry.RelPicard.pointsSubBasepointModule_cons AlgebraicGeometry.RelPicard.pointsSubBasepointModule_nil AlgebraicGeometry.RelPicard.fst_toProdSpec_assoc AlgebraicGeometry.RelPicard.toProdSpec_fst AlgebraicGeometry.graphOver_fst_assoc AlgebraicGeometry.RelEffCartierDiv.toPoint_comp AlgebraicGeometry.RelEffCartierDiv.toPoint_comp_assoc AlgebraicGeometry.graphOver_fst AlgebraicGeometry.RelEffCartierDiv.ofPoint_I AlgebraicGeometry.graphOver_snd AlgebraicGeometry.graphOver_snd_assoc AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.sub_app AlgebraicGeometry.Scheme.IdealSheafData.sres_sresTop AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.add_app AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.mk.sizeOf_spec AlgebraicGeometry.Scheme.IdealSheafData.coe_resLE AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.smul_app AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.coe_ofLE_app AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.ideal_range AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.zero_app AlgebraicGeometry.Scheme.IdealSheafData.sres_sres AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.comp_app AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.neg_app"
p2m_attr_erase "simp" "AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.id_app AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.coe_mulRight_app AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.nsmul_app AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.mk.injEq AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.zsmul_app AlgebraicGeometry.prodKerGraph_one AlgebraicGeometry.fibrePowOver.proj_comp AlgebraicGeometry.prodKerGraph_zero AlgebraicGeometry.RelEffCartierDiv.empty_I AlgebraicGeometry.fibrePowOver.proj_comp_assoc AlgebraicCurve.SymmetricPowerPackage.mk.sizeOf_spec AlgebraicCurve.SymmetricPowerPackage.mk.injEq AlgebraicCurve.Place.mk.injEq AlgebraicCurve.Divisor.degree_single AlgebraicCurve.Divisor.smul_single AlgebraicCurve.Place.smul_toValuationSubring AlgebraicCurve.Place.heightOneSpectrum_asIdeal AlgebraicCurve.Place.coe_algebraMap AlgebraicCurve.Place.ord_one AlgebraicCurve.Place.coe_smulRingEquiv_apply AlgebraicCurve.Pic0.coe_degZeroSMulHom AlgebraicCurve.Place.deg_smul AlgebraicCurve.Pic0.mk_zero AlgebraicCurve.Place.mk.sizeOf_spec AlgebraicCurve.Divisor.degree_smul AlgebraicCurve.Pic0.mk_add AlgebraicCurve.Place.ord_zero AlgebraicCurve.Place.ofHeightOneSpectrum_toValuationSubring AlgebraicCurve.mulAdele_apply AlgebraicCurve.residuePairing_apply_coe AlgebraicCurve.mem_adeleBdd AlgebraicCurve.weilSmul_one AlgebraicCurve.diagonalHom_apply AlgebraicCurve.weilSmul_apply AlgebraicCurve.adeleSpaceMul_coe AlgebraicCurve.mulAdele_one AlgebraicCurve.CurveModel.mk.injEq AlgebraicCurve.CurveModel.mk.sizeOf_spec AlgebraicCurve.coe_cechH0Equiv_apply AlgebraicCurve.cechH1ToH1_mk"
p2m_attr_erase "simp" "AlgebraicCurve.lSpaceOn_univ AlgebraicCurve.lSpaceOn_empty AlgebraicCurve.Place.congrEquiv_symm_apply AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply AlgebraicCurve.RationalFunctionField.deg_placeOfPoint AlgebraicCurve.Divisor.mapRestrict_single AlgebraicCurve.Divisor.pushforward_single AlgebraicCurve.Place.coe_restrictInclusion AlgebraicCurve.Place.mem_fiber AlgebraicCurve.Place.restrict_toValuationSubring AlgebraicCurve.Divisor.degree_pushforward AlgebraicCurve.Place.restrictResidueMap_residue AlgebraicCurve.Pic0.coe_pushforwardDegZeroHom AlgebraicCurve.Pic0.coe_pullbackDegZeroHom AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal AlgebraicCurve.IsFrobeniusEndo.frobNormRingHom_apply ModularCurve.frobeniusPushforwardGeomLevelPic0_mk ModularCurve.coe_frobeniusGeomLevelEquiv_apply ModularCurve.coe_frobeniusPushforwardGeomLevelDegZero ModularCurve.heckeFibreGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusGeomLevel_apply_coe ModularCurve.frobeniusPullbackGeomLevelPic0OfIsCurveOver_mk ModularCurve.coe_heckeFibreGeomLevelDegZero ModularCurve.coe_frobeniusPullbackGeomLevelDegZero ModularCurve.frobeniusPullbackGeomLevelPic0_mk ModularCurve.frobeniusPullbackGeomLevel_single ModularCurve.heckeFibreGeomLevelPic0_mk ModularCurve.frobeniusPushforwardGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusPushforwardGeomLevel_single ModularCurve.qExpandAlgC_apply AlgebraicCurve.Divisor.degree_pushforwardAlong AlgebraicCurve.Pic0.coe_degZeroCorrespondence AlgebraicCurve.Place.mem_fiberAlong"
p2m_attr_erase "simp" "AlgebraicCurve.SemilinearAut.toRingAut_inv AlgebraicCurve.SemilinearAut.smul_def AlgebraicCurve.SemilinearAut.smul_single AlgebraicCurve.SemilinearAut.smul_toValuationSubring AlgebraicCurve.SemilinearAut.baseAut_inv AlgebraicCurve.SemilinearAut.baseAut_ofAlgAut AlgebraicCurve.SemilinearAut.toRingAut_ofAlgAut AlgebraicCurve.SemilinearAut.torsionRep_apply AlgebraicCurve.SemilinearAut.toRingAut_one AlgebraicCurve.SemilinearAut.deg_smul AlgebraicCurve.SemilinearAut.degree_smul AlgebraicCurve.SemilinearAut.coe_degZeroSMulHom AlgebraicCurve.SemilinearAut.baseAut_mul AlgebraicCurve.SemilinearAut.coe_smulValuationSubringEquiv_apply AlgebraicCurve.SemilinearAut.baseAut_one AlgebraicCurve.SemilinearAut.ofAlgAut_smul AlgebraicCurve.SemilinearAut.coe_torsion_smul AlgebraicCurve.SemilinearAut.toRingAut_mul AlgebraicCurve.coe_frobeniusPushforwardDegZero AlgebraicCurve.IsFrobeniusEndo.coe_frobeniusPullbackDegZero ModularCurve.jqNModC_one ModularCurve.qExpand_coeff_mul ModularCurve.qExpandₐ_apply ModularCurve.jqN_one ModularCurve.qExpand_single ModularCurve.dedekindPsi_one ModularCurve.ModularPolynomialData.mk.sizeOf_spec ModularCurve.evalAtJ_X ModularCurve.ModularPolynomialData.mk.injEq ModularCurve.constantCoeff_jNum ModularCurve.constantCoeff_eisenstein4 ModularCurve.qExpand_C ModularCurve.coeff_jq_neg_one ModularCurve.constantCoeff_jNumQ ModularCurve.reduceModBivar_C_X ModularCurve.laurentMap_coeff ModularCurve.reduceModBivar_X ModularCurve.laurentMap_single ModularCurve.evalAtJInt_X ModularCurve.evalAtJMod_X"
p2m_attr_erase "simp" "ModularCurve.jqNMod_one ModularCurve.aeval_heckeGen ModularCurve.coe_mTorsionGaloisRep_apply ModularCurve.eisensteinSystem_of_dvd ModularCurve.eisensteinSystem_of_not_dvd FreyPackage.mk.sizeOf_spec FreyPackage.mk.injEq WeierstrassCurve.Affine.Point.galoisRepModuleEnd_apply AlgebraicCurve.RationalFunctionField.placeInfty_toValuationSubring AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none AlgebraicCurve.Divisor.evalFun_zero AlgebraicCurve.Place.evalAt_one AlgebraicCurve.Place.differentialCoeff_zero AlgebraicCurve.Place.differentialCoeff_dCoord AlgebraicCurve.TranscendenceTower.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.injEq AlgebraicCurve.TranscendenceTower.mk.injEq AlgebraicCurve.PoleDivisorPackage.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.sizeOf_spec AlgebraicCurve.PoleDivisorPackage.mk.injEq AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.sizeOf_spec AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.injEq AlgebraicCurve.adeleSingle_coe AlgebraicCurve.kaehlerResidueTermKFam_apply AlgebraicCurve.Place.LocalResidueData.mk.injEq AlgebraicCurve.Place.LocalResidueData.mk.sizeOf_spec AlgebraicCurve.Place.kw_ffgc_adicCompletionComapIntegers_coe AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.sizeOf_spec AlgebraicCurve.Place.mem_simplePoleSubmodule AlgebraicCurve.Place.coe_uniformizerSubring ModularCurve.Lg37.Lg37CompletionSection.mk.injEq AlgebraicCurve.Place.CoefficientFieldSection.mk.injEq AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.injEq ModularCurve.Lg37.Lg37CompletionSection.mk.sizeOf_spec AlgebraicCurve.Place.CoefficientFieldSection.mk.sizeOf_spec AlgebraicCurve.Place.poleSubmodule_one AlgebraicCurve.Place.mem_poleSubmodule"
p2m_attr_erase "simp" "PresheafOfModules.InternalHom.IsSheafAux.appAt_toPresheafHom SheafOfModules.ihomSectionsEquivFamily_unit AlgebraicGeometry.Scheme.Modules.restrictHomEquivFamily_apply SheafOfModules.ihomEval_unit_app AlgebraicGeometry.Scheme.Modules.ihomEval_zero_right AlgebraicGeometry.Scheme.Modules.ihomEval_zero_left AlgebraicGeometry.Scheme.Modules.homOfFamily_app_apply SheafOfModules.unit_ihomSectionsEquivFamily AlgebraicGeometry.Scheme.Modules.familyOfHom_app AlgebraicGeometry.Scheme.Modules.restrictUnitIso_hom_app_apply AlgebraicGeometry.Scheme.Modules.restrictUnitIso_inv_app_apply AlgebraicGeometry.Scheme.Modules.restrictHomOfFamily_app_apply AlgebraicGeometry.Scheme.Modules.restrictHomEquivFamily_symm_apply AlgebraicGeometry.Scheme.Modules.pullbackLocalSection_neg AlgebraicGeometry.Scheme.Modules.pullbackLocalSection_zero AlgebraicGeometry.Scheme.Modules.pullbackLocalSection_sub AlgebraicGeometry.Scheme.Modules.pullbackLocalSection_add AlgebraicGeometry.SmoothProperCurve.FiniteMapData.twoAffineOpenCover_U1 AlgebraicGeometry.SmoothProperCurve.FiniteMapData.mk.injEq AlgebraicGeometry.SmoothProperCurve.FiniteMapData.mk.sizeOf_spec AlgebraicGeometry.SmoothProperCurve.FiniteMapData.twoAffineOpenCover_U0"

set_option autoImplicit false

p2m_open "CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory AlgebraicGeometry P2MW.S_AlgebraicGeometry_RelPicard_RepresentsRelSubPic_fibrewiseAlgEquivZero_ofInvertible_norm_pullback_poincare_of_twoGluedCurves_of_mem_of_ringKrullDim_le_one.AlgebraicGeometry NeronModelInfra GoodReductionJacobian AlgebraicGeometry.RelPicard P2MW.S_AlgebraicGeometry_RelPicard_RepresentsRelSubPic_fibrewiseAlgEquivZero_ofInvertible_norm_pullback_poincare_of_twoGluedCurves_of_mem_of_ringKrullDim_le_one.AlgebraicGeometry.RelPicard AlgebraicGeometry.SmoothProperCurve"

universe u

noncomputable section

namespace AlgebraicGeometry
p2m_export "AlgebraicGeometry" "Scheme.Hom.resLE_comp_ι Spec.map_preimage IsLocallyNoetherian Surjective SmoothOfRelativeDimension IsProper morphismRestrict_ι Scheme.Modules.pullback Scheme.Hom GeometricallyIntegral stalkwise IsFinite isPullback_morphismRestrict LocallyOfFiniteType Spec IsIntegral Spec.map Scheme Flat Scheme.Hom.finrank_of_isPullback IsClosedImmersion IsReduced Spec.preimage Scheme.Modules.pullbackCongr morphismRestrict_ι_assoc IsAffineOpen Scheme.Modules Scheme.Hom.resLE_comp_ι_assoc LocallyOfFinitePresentation geometrically Scheme.Modules.pullbackComp Scheme.Modules.pullbackTensorObjIso Scheme.Modules.pullbackTensorUnitObjIso RelPicard.IsAlgEquivZero.pullback_ofInvertible_of_iso_normModule_morphismRestrict Scheme.Modules.IsInvertible Scheme.Modules.pullbackUnitIso RelPicard.RepresentsRelSubPic RelPicard.IsAlgEquivZero Scheme.Modules.normModule TwoGluedCurves.isAlgEquivZero_fibre_of_isAlgEquivZero_fibre_of_preconnectedSpace RelPicard.RepresentsRelSubPic.nonempty_pullback_zeroSection_norm_pullback_poincare_iso_unit_of_mem_of_ringKrullDim_le_one Scheme.Modules.IsInvertible.nonempty_iso_tensorUnit_of_field"
namespace RelPicard
p2m_export "AlgebraicGeometry.RelPicard" "IsAlgEquivZero.pullback_ofInvertible_of_iso_normModule_morphismRestrict baseChangeSnd RigidifiedLineBundle RepresentsRelSubPic fibreAt IsAlgEquivZero FibrewiseAlgEquivZero IsAlgEquivZero.of_iso geometricallyIntegral_id_Spec algEquivZeroCut curveChange curveChange_snd rigCorrection RigidifiedLineBundle.ofInvertible RigidifiedLineBundle.ofInvertible_L_eq_tensor geometricallyConnected_of_representsRelSubPic_algEquivZeroCut RepresentsRelSubPic.nonempty_pullback_zeroSection_norm_pullback_poincare_iso_unit_of_mem_of_ringKrullDim_le_one"
namespace CutAuxH7C
p2m_open "AlgebraicGeometry.RelPicard AlgebraicGeometry"

p2m_open "CategoryTheory.MonoidalCategory"

theorem nonempty_pullback_fst_ofInvertible_iso {R : Type u} [CommRing R] {C : Scheme.{u}}
    {c : C ⟶ Spec (CommRingCat.of R)} {ε : SchemeHomOver (𝟙 (Spec (CommRingCat.of R))) c}
    {T : Scheme.{u}} {t : T ⟶ Spec (CommRingCat.of R)} (L : (pullback c t).Modules)
    (hL : Scheme.Modules.IsInvertible L) {k : Type u} [Field k] (s : Spec (CommRingCat.of k) ⟶ T) :
    Nonempty ((Scheme.Modules.pullback (pullback.fst (pullback.snd c t) s)).obj (RigidifiedLineBundle.ofInvertible (ε := ε) L hL).L ≅
      (Scheme.Modules.pullback (pullback.fst (pullback.snd c t) s)).obj L) := by
  rw [RigidifiedLineBundle.ofInvertible_L_eq_tensor]

  have hD : Scheme.Modules.IsInvertible (rigCorrection ε t L) := ((hL.pullback _).dual).1
  obtain ⟨u⟩ := Scheme.Modules.IsInvertible.nonempty_iso_tensorUnit_of_field k _ (hD.pullback s)
  refine ⟨Scheme.Modules.pullbackTensorObjIso _ _ _ ≪≫ (Iso.refl _ ⊗ᵢ ?_) ≪≫ ρ_ _⟩
  exact (Scheme.Modules.pullbackComp _ _).app _ ≪≫
    (Scheme.Modules.pullbackCongr (pullback.condition (f := pullback.snd c t) (g := s))).app _ ≪≫
    ((Scheme.Modules.pullbackComp _ _).app _).symm ≪≫
    (Scheme.Modules.pullback _).mapIso u ≪≫ Scheme.Modules.pullbackTensorUnitObjIso _

theorem isAlgEquivZero_unit {k : Type} [Field k] {A : Scheme.{0}} (a : A ⟶ Spec (CommRingCat.of k)) :
    IsAlgEquivZero a (SheafOfModules.unit A.ringCatSheaf : A.Modules) := by
  refine ⟨Spec (CommRingCat.of k), 𝟙 _, inferInstance, geometricallyIntegral_id_Spec k,
    (SheafOfModules.unit _ : (pullback a (𝟙 _)).Modules), ⟨fun _ => ⟨⊤, trivial, ⟨Scheme.Modules.pullbackUnitIso _⟩⟩⟩,
    ⟨𝟙 _, Category.id_comp _⟩, ⟨𝟙 _, Category.id_comp _⟩, ⟨Scheme.Modules.pullbackUnitIso _⟩,
    ⟨Scheme.Modules.pullbackUnitIso _ ≪≫ (Scheme.Modules.pullbackUnitIso _).symm⟩⟩

end AlgebraicGeometry.RelPicard.CutAuxH7C

end

namespace AlgebraicGeometry
p2m_export "AlgebraicGeometry" "Scheme.Hom.resLE_comp_ι Spec.map_preimage IsLocallyNoetherian Surjective SmoothOfRelativeDimension IsProper morphismRestrict_ι Scheme.Modules.pullback Scheme.Hom GeometricallyIntegral stalkwise IsFinite isPullback_morphismRestrict LocallyOfFiniteType Spec IsIntegral Spec.map Scheme Flat Scheme.Hom.finrank_of_isPullback IsClosedImmersion IsReduced Spec.preimage Scheme.Modules.pullbackCongr morphismRestrict_ι_assoc IsAffineOpen Scheme.Modules Scheme.Hom.resLE_comp_ι_assoc LocallyOfFinitePresentation geometrically Scheme.Modules.pullbackComp Scheme.Modules.pullbackTensorObjIso Scheme.Modules.pullbackTensorUnitObjIso RelPicard.IsAlgEquivZero.pullback_ofInvertible_of_iso_normModule_morphismRestrict Scheme.Modules.IsInvertible Scheme.Modules.pullbackUnitIso RelPicard.RepresentsRelSubPic RelPicard.IsAlgEquivZero Scheme.Modules.normModule TwoGluedCurves.isAlgEquivZero_fibre_of_isAlgEquivZero_fibre_of_preconnectedSpace RelPicard.RepresentsRelSubPic.nonempty_pullback_zeroSection_norm_pullback_poincare_iso_unit_of_mem_of_ringKrullDim_le_one Scheme.Modules.IsInvertible.nonempty_iso_tensorUnit_of_field"
namespace RelPicard
p2m_export "AlgebraicGeometry.RelPicard" "IsAlgEquivZero.pullback_ofInvertible_of_iso_normModule_morphismRestrict baseChangeSnd RigidifiedLineBundle RepresentsRelSubPic fibreAt IsAlgEquivZero FibrewiseAlgEquivZero IsAlgEquivZero.of_iso geometricallyIntegral_id_Spec algEquivZeroCut curveChange curveChange_snd rigCorrection RigidifiedLineBundle.ofInvertible RigidifiedLineBundle.ofInvertible_L_eq_tensor geometricallyConnected_of_representsRelSubPic_algEquivZeroCut RepresentsRelSubPic.nonempty_pullback_zeroSection_norm_pullback_poincare_iso_unit_of_mem_of_ringKrullDim_le_one"
namespace CutAuxH7C
p2m_open "AlgebraicGeometry.RelPicard AlgebraicGeometry"

theorem asIdeal_base_eq_ker {A : Type} [CommRing A] {k : Type} [Field k] (φ : CommRingCat.of A ⟶ CommRingCat.of k)
    (y : Spec (CommRingCat.of k)) : ((Spec.map φ).base y).asIdeal = RingHom.ker φ.hom := by
  have hy : y.asIdeal = ⊥ := by
    have := y.2
    exact Ideal.eq_bot_of_prime y.asIdeal
  show (PrimeSpectrum.comap φ.hom y).asIdeal = _
  rw [PrimeSpectrum.comap_asIdeal, hy, ← RingHom.ker_eq_comap_bot]

end AlgebraicGeometry.RelPicard.CutAuxH7C

open AlgebraicGeometry.RelPicard.CutAuxH7C in
set_option maxHeartbeats 6400000 in
theorem solution

    (R : Type) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    {C C' : Scheme.{0}} (c : C ⟶ Spec (CommRingCat.of R)) (c' : C' ⟶ Spec (CommRingCat.of R)) [IsProper c]
    [IsIntegral C] [IsLocallyNoetherian C] (hCnorm : ∀ x : C, IsIntegrallyClosed (C.presheaf.stalk x))
    (ε : SchemeHomOver (𝟙 (Spec (CommRingCat.of R))) c)

    (hsf : ∀ (k : Type) [Field k] [IsAlgClosed k] (f : R →+* k), RingHom.ker f ≠ ⊥ →
      ∃ (C₁ C₂ : Scheme.{0}) (c₁ : C₁ ⟶ Spec (CommRingCat.of k)) (c₂ : C₂ ⟶ Spec (CommRingCat.of k))
        (_ : IsProper c₁) (_ : SmoothOfRelativeDimension 1 c₁) (_ : GeometricallyIntegral c₁)
        (_ : IsProper c₂) (_ : SmoothOfRelativeDimension 1 c₂) (_ : GeometricallyIntegral c₂)
        (i₁ : SchemeHomOver c₁ (pullback.snd c (Spec.map (CommRingCat.ofHom f))))
        (i₂ : SchemeHomOver c₂ (pullback.snd c (Spec.map (CommRingCat.ofHom f))))
        (_ : IsClosedImmersion i₁.1) (_ : IsClosedImmersion i₂.1) (n : ℕ)
        (_ : C₁.TwoAffineOpenCover) (_ : C₂.TwoAffineOpenCover),
        IsReduced (pullback c (Spec.map (CommRingCat.ofHom f))) ∧
        (∀ z : ↥(pullback c (Spec.map (CommRingCat.ofHom f))), z ∈ Set.range i₁.1.base ∨ z ∈ Set.range i₂.1.base) ∧
        IsReduced (pullback i₁.1 i₂.1) ∧ Nat.card ↥(pullback i₁.1 i₂.1) = n ∧ 0 < n)

    (π₁ π₂ : SchemeHomOver c' c) [IsFinite π₂.1] [Surjective π₂.1]

    (D : RelativePic0Designation R c)
    (hD : RepresentsRelSubPic c ε (algEquivZeroCut c ε) D)

    [IsIntegral ↑(pullback c' D.toBase)] [IsIntegral ↑(pullback c D.toBase)]
    (hnorm : ∀ U : (pullback c D.toBase).Opens, IsAffineOpen U →
      IsIntegrallyClosed Γ(pullback c D.toBase, U))
    [LocallyOfFiniteType D.toBase]

    (Nm : ∀ ⦃X Y : Scheme.{0}⦄, (X ⟶ Y) → X.Modules → Y.Modules)
    (hNm :
      ∀ ⦃X Y : Scheme.{0}⦄ (π : X ⟶ Y) [IsFinite π] [Surjective π] [IsIntegral X] [IsIntegral Y],
        (∀ U : Y.Opens, IsAffineOpen U → IsIntegrallyClosed Γ(Y, U)) →

        (∀ L : X.Modules, Scheme.Modules.IsInvertible L → Scheme.Modules.IsInvertible (Nm π L)) ∧

        (∀ L L' : X.Modules, Scheme.Modules.IsInvertible L → Nonempty (L ≅ L') →
          Nonempty (Nm π L ≅ Nm π L')) ∧

        (∀ L L' : X.Modules, Scheme.Modules.IsInvertible L → Scheme.Modules.IsInvertible L' →
          Nonempty (Nm π (L ⊗ L') ≅ Nm π L ⊗ Nm π L')) ∧

        Nonempty (Nm π (𝟙_ X.Modules) ≅ 𝟙_ Y.Modules) ∧

        (∀ ⦃X' Y' : Scheme.{0}⦄ (g : Y' ⟶ Y) (π' : X' ⟶ Y') (g' : X' ⟶ X), IsPullback g' π' π g →
          ∀ [Flat g] [IsIntegral X'] [IsIntegral Y'],
          (∀ U : Y'.Opens, IsAffineOpen U → IsIntegrallyClosed Γ(Y', U)) →
          ∀ L : X.Modules, Scheme.Modules.IsInvertible L →
            Nonempty ((Scheme.Modules.pullback g).obj (Nm π L) ≅
              Nm π' ((Scheme.Modules.pullback g').obj L))) ∧

        (∀ (V : Y.Opens) (d : ℕ), Flat (π ∣_ V) → LocallyOfFinitePresentation (π ∣_ V) →
          (∀ y : V, (π ∣_ V).finrank y = d) →
          ∀ L : X.Modules, Scheme.Modules.IsInvertible L →
            Nonempty ((Scheme.Modules.pullback V.ι).obj (Nm π L) ≅
              Scheme.Modules.normModule (π ∣_ V) d ((Scheme.Modules.pullback (π ⁻¹ᵁ V).ι).obj L))))
    (hinv : Scheme.Modules.IsInvertible
      (Nm (curveChange π₂.1 π₂.2 D.toBase) ((Scheme.Modules.pullback (curveChange π₁.1 π₁.2 D.toBase)).obj hD.poincare.L)))

    (V : C.Opens) (d : ℕ) [Flat (π₂.1 ∣_ V)] [LocallyOfFinitePresentation (π₂.1 ∣_ V)]
    (hrk : ∀ y : V, (π₂.1 ∣_ V).finrank y = d)
    (hVcodim : ∀ x : C, ringKrullDim (C.presheaf.stalk x) ≤ 1 → x ∈ V)
    (hVgen : ∀ x : C, (c.base x).asIdeal = ⊥ → x ∈ V) :
    FibrewiseAlgEquivZero (RigidifiedLineBundle.ofInvertible (ε := ε)
      (Nm (curveChange π₂.1 π₂.2 D.toBase) ((Scheme.Modules.pullback (curveChange π₁.1 π₁.2 D.toBase)).obj hD.poincare.L))
      hinv) := by
  intro k _ _ s
  classical

  let M : (pullback c D.toBase).Modules :=
    Nm (curveChange π₂.1 π₂.2 D.toBase) ((Scheme.Modules.pullback (curveChange π₁.1 π₁.2 D.toBase)).obj hD.poincare.L)
  have hM : Scheme.Modules.IsInvertible M := hinv

  let toκ : R →+* k := (Spec.preimage (s ≫ D.toBase)).hom
  have htoκ : Spec.map (CommRingCat.ofHom toκ) = s ≫ D.toBase := by
    simp only [toκ, CommRingCat.ofHom_hom, Spec.map_preimage]
  by_cases hker : RingHom.ker toκ = ⊥
  ·

    have sqF : IsPullback (pullback.fst (c') D.toBase) (curveChange π₂.1 π₂.2 D.toBase) π₂.1 (pullback.fst (c) D.toBase) := by
      have big : IsPullback ((curveChange π₂.1 π₂.2 D.toBase) ≫ (pullback.snd (c) D.toBase)) (pullback.fst (c') D.toBase) D.toBase (π₂.1 ≫ (c)) := by
        rw [curveChange_snd, π₂.2]
        exact (IsPullback.of_hasPullback (c') D.toBase).flip
      have hcomm : (curveChange π₂.1 π₂.2 D.toBase) ≫ (pullback.fst (c) D.toBase) = (pullback.fst (c') D.toBase) ≫ π₂.1 := by
        simp only [curveChange, pullback.lift_fst]
      exact (IsPullback.of_right big hcomm (IsPullback.of_hasPullback (c) D.toBase).flip).flip
    haveI : IsFinite (curveChange π₂.1 π₂.2 D.toBase) := MorphismProperty.of_isPullback (P := @IsFinite) sqF inferInstance
    haveI : Surjective (curveChange π₂.1 π₂.2 D.toBase) := MorphismProperty.of_isPullback (P := @Surjective) sqF inferInstance
    have big2 : IsPullback (((curveChange π₂.1 π₂.2 D.toBase) ⁻¹ᵁ ((pullback.fst (c) D.toBase) ⁻¹ᵁ V)).ι ≫ (pullback.fst (c') D.toBase)) ((curveChange π₂.1 π₂.2 D.toBase) ∣_ ((pullback.fst (c) D.toBase) ⁻¹ᵁ V)) π₂.1 ((((pullback.fst (c) D.toBase) ⁻¹ᵁ V)).ι ≫ (pullback.fst (c) D.toBase)) :=
      (isPullback_morphismRestrict (curveChange π₂.1 π₂.2 D.toBase) ((pullback.fst (c) D.toBase) ⁻¹ᵁ V)).flip.paste_horiz sqF
    have hle : (curveChange π₂.1 π₂.2 D.toBase) ⁻¹ᵁ ((pullback.fst (c) D.toBase) ⁻¹ᵁ V) ≤ (pullback.fst (c') D.toBase) ⁻¹ᵁ (π₂.1 ⁻¹ᵁ V) := by
      intro x hx
      show ((pullback.fst (c') D.toBase) ≫ π₂.1).base x ∈ V
      rw [sqF.w]
      exact hx
    rw [← Scheme.Hom.resLE_comp_ι (pullback.fst (c') D.toBase) hle, ← Scheme.Hom.resLE_comp_ι (pullback.fst (c) D.toBase) (le_refl ((pullback.fst (c) D.toBase) ⁻¹ᵁ V))] at big2
    have right : IsPullback (π₂.1 ⁻¹ᵁ V).ι (π₂.1 ∣_ V) π₂.1 V.ι := (isPullback_morphismRestrict π₂.1 V).flip
    have sqFV : IsPullback ((pullback.fst (c') D.toBase).resLE (π₂.1 ⁻¹ᵁ V) ((curveChange π₂.1 π₂.2 D.toBase) ⁻¹ᵁ ((pullback.fst (c) D.toBase) ⁻¹ᵁ V)) hle) ((curveChange π₂.1 π₂.2 D.toBase) ∣_ ((pullback.fst (c) D.toBase) ⁻¹ᵁ V)) (π₂.1 ∣_ V)
        ((pullback.fst (c) D.toBase).resLE V ((pullback.fst (c) D.toBase) ⁻¹ᵁ V) (le_refl _)) := by
      refine IsPullback.of_right big2 ?_ right
      rw [← cancel_mono V.ι]
      simp only [Category.assoc, Scheme.Hom.resLE_comp_ι]
      rw [morphismRestrict_ι, Scheme.Hom.resLE_comp_ι_assoc, sqF.w, morphismRestrict_ι_assoc]
    haveI : Flat ((curveChange π₂.1 π₂.2 D.toBase) ∣_ ((pullback.fst (c) D.toBase) ⁻¹ᵁ V)) := MorphismProperty.of_isPullback (P := @Flat) sqFV inferInstance
    haveI : LocallyOfFinitePresentation ((curveChange π₂.1 π₂.2 D.toBase) ∣_ ((pullback.fst (c) D.toBase) ⁻¹ᵁ V)) :=
      MorphismProperty.of_isPullback (P := @LocallyOfFinitePresentation) sqFV inferInstance
    haveI : IsFinite (π₂.1 ∣_ V) := MorphismProperty.of_isPullback (P := @IsFinite) (isPullback_morphismRestrict π₂.1 V).flip inferInstance
    have hrkD : ∀ y : ((pullback.fst (c) D.toBase) ⁻¹ᵁ V), ((curveChange π₂.1 π₂.2 D.toBase) ∣_ ((pullback.fst (c) D.toBase) ⁻¹ᵁ V)).finrank y = d := fun y => by
      rw [Scheme.Hom.finrank_of_isPullback _ _ _ _ sqFV y]
      exact hrk _

    obtain ⟨-, -, -, -, -, he⟩ := hNm (curveChange π₂.1 π₂.2 D.toBase) hnorm
    have hP : Scheme.Modules.IsInvertible hD.poincare.L := hD.poincare.isInvertible
    have hL' : Scheme.Modules.IsInvertible ((Scheme.Modules.pullback (curveChange π₁.1 π₁.2 D.toBase)).obj hD.poincare.L) := hP.pullback _
    have hMV := he ((pullback.fst (c) D.toBase) ⁻¹ᵁ V) d inferInstance inferInstance hrkD _ hL'

    have hfae : ∀ (k' : Type) [Field k'] [IsAlgClosed k'] (s' : Spec (CommRingCat.of k') ⟶ D.P),
        IsAlgEquivZero (fibreAt (c') D.toBase s')
          ((Scheme.Modules.pullback (pullback.fst (pullback.snd (c') D.toBase) s')).obj
            ((Scheme.Modules.pullback (curveChange π₁.1 π₁.2 D.toBase)).obj hD.poincare.L)) := by
      intro k' _ _ s'
      let e : pullback (pullback.snd (c') D.toBase) s' ⟶ pullback (pullback.snd (c) D.toBase) s' :=
        pullback.map _ _ _ _ (curveChange π₁.1 π₁.2 D.toBase) (𝟙 _) (𝟙 D.P) (by rw [Category.comp_id, curveChange_snd]) (by simp)
      have he' : e ≫ fibreAt (c) D.toBase s' = fibreAt (c') D.toBase s' := by
        simp only [e, fibreAt, pullback.lift_snd, Category.comp_id]
      have hfst : e ≫ pullback.fst (pullback.snd (c) D.toBase) s' = pullback.fst (pullback.snd (c') D.toBase) s' ≫ (curveChange π₁.1 π₁.2 D.toBase) := by
        simp only [e, pullback.lift_fst]
      refine IsAlgEquivZero.of_iso ?_ ((hD.poincare_mem k' s').pullback e he')
      exact (Scheme.Modules.pullbackComp _ _).app hD.poincare.L ≪≫
        (Scheme.Modules.pullbackCongr hfst).app hD.poincare.L ≪≫
        ((Scheme.Modules.pullbackComp _ _).app hD.poincare.L).symm

    have hcomm : (pullback.fst (pullback.snd c D.toBase) s ≫ (pullback.fst c D.toBase)) ≫ c = fibreAt c D.toBase s ≫ Spec.map (CommRingCat.ofHom toκ) := by
      rw [htoκ, Category.assoc, pullback.condition, ← Category.assoc, pullback.condition, Category.assoc]
      rfl
    have hs : ∀ x, (pullback.fst (pullback.snd c D.toBase) s).base x ∈ ((pullback.fst c D.toBase) ⁻¹ᵁ V) := by
      intro x
      show (pullback.fst (pullback.snd c D.toBase) s ≫ (pullback.fst c D.toBase)).base x ∈ V
      apply hVgen
      show (((pullback.fst (pullback.snd c D.toBase) s ≫ (pullback.fst c D.toBase)) ≫ c).base x).asIdeal = ⊥
      rw [hcomm]
      show ((Spec.map (CommRingCat.ofHom toκ)).base ((fibreAt c D.toBase s).base x)).asIdeal = ⊥
      rw [asIdeal_base_eq_ker]
      exact hker

    exact AlgebraicGeometry.RelPicard.IsAlgEquivZero.pullback_ofInvertible_of_iso_normModule_morphismRestrict
      π₂.1 π₂.2 _ hL' hfae _ hinv ((pullback.fst (c) D.toBase) ⁻¹ᵁ V) d hrkD hMV k s hs
  ·

    have h0 := (AlgebraicGeometry.RelPicard.RepresentsRelSubPic.nonempty_pullback_zeroSection_norm_pullback_poincare_iso_unit_of_mem_of_ringKrullDim_le_one
      R c c' hCnorm ε π₁ π₂ D hD hnorm Nm hNm hinv V d hrk hVcodim).1

    let Xk : Scheme.{0} := pullback c (Spec.map (CommRingCat.ofHom toκ))
    let x : Xk ⟶ Spec (CommRingCat.of k) := pullback.snd _ _
    obtain ⟨C₁, C₂, c₁, c₂, hpr₁, hsm₁, hgi₁, hpr₂, hsm₂, hgi₂, i₁, i₂, hci₁, hci₂, n, 𝒱₁, 𝒱₂, hXred, hcover, hcr, hn, hn0⟩ :=
      hsf k toκ hker
    haveI := hpr₁; haveI := hsm₁; haveI := hgi₁; haveI := hpr₂; haveI := hsm₂; haveI := hgi₂; haveI := hci₁; haveI := hci₂

    let Dk : Scheme.{0} := pullback D.toBase (Spec.map (CommRingCat.ofHom toκ))
    let σ : Dk ⟶ Spec (CommRingCat.of k) := pullback.snd _ _
    haveI : ConnectedSpace ↥Dk :=
      (geometricallyConnected_of_representsRelSubPic_algEquivZeroCut R c ε D hD).geometrically_connectedSpace
        (Spec.map (CommRingCat.ofHom toκ)) (pullback.fst _ _) (pullback.snd _ _) (IsPullback.of_hasPullback _ _)

    let φ : pullback x σ ⟶ pullback (c) D.toBase :=
      pullback.map x σ (c) D.toBase (pullback.fst _ _) (pullback.fst _ _) (Spec.map (CommRingCat.ofHom toκ))
        pullback.condition.symm pullback.condition.symm
    let L : (pullback x σ).Modules := (Scheme.Modules.pullback φ).obj M
    have hL : Scheme.Modules.IsInvertible L := hM.pullback φ

    let z : Spec (CommRingCat.of k) ⟶ Dk :=
      pullback.lift (Spec.map (CommRingCat.ofHom toκ) ≫ D.zeroSection) (𝟙 _) (by rw [Category.assoc, D.zeroSection_toBase]; simp)
    have h₀ : IsAlgEquivZero (fibreAt x σ z) ((Scheme.Modules.pullback (pullback.fst (pullback.snd x σ) z)).obj L) := by

      let fz := pullback.fst (pullback.snd x σ) z
      let zs : SchemeHomOver (𝟙 (Spec (CommRingCat.of R))) D.toBase := ⟨D.zeroSection, D.zeroSection_toBase⟩
      let g : pullback (pullback.snd x σ) z ⟶ pullback (c) (𝟙 (Spec (CommRingCat.of R))) :=
        pullback.lift (fz ≫ φ ≫ pullback.fst _ _) (fz ≫ φ ≫ pullback.fst _ _ ≫ c) (by simp)
      have hg : g ≫ baseChangeSnd (c) zs = fz ≫ φ := by
        apply pullback.hom_ext
        · simp only [g, baseChangeSnd, Category.assoc, pullback.lift_fst, pullback.lift_fst_assoc, Category.comp_id]
        ·
          simp only [g, baseChangeSnd, zs, φ, fz, Category.assoc, pullback.lift_snd, pullback.lift_snd_assoc,
            pullback.lift_fst_assoc]
          have h1 : pullback.fst (pullback.snd x σ) z ≫ pullback.snd x σ = pullback.snd (pullback.snd x σ) z ≫ z :=
            pullback.condition
          have h2 : z ≫ pullback.fst D.toBase (Spec.map (CommRingCat.ofHom toκ)) = Spec.map (CommRingCat.ofHom toκ) ≫ D.zeroSection :=
            pullback.lift_fst _ _ _
          have h3 : z ≫ pullback.snd D.toBase (Spec.map (CommRingCat.ofHom toκ)) = 𝟙 _ := pullback.lift_snd _ _ _
          rw [reassoc_of% h1, h2]

          have h4 : pullback.fst (c) (Spec.map (CommRingCat.ofHom toκ)) ≫ c =
              x ≫ Spec.map (CommRingCat.ofHom toκ) := pullback.condition
          rw [reassoc_of% h4]
          have h5 : pullback.fst (pullback.snd x σ) z ≫ pullback.fst x σ ≫ x =
              pullback.snd (pullback.snd x σ) z ≫ z ≫ σ := by
            rw [pullback.condition, ← Category.assoc, h1, Category.assoc]
          rw [reassoc_of% h5, reassoc_of% h3]
      have e : (Scheme.Modules.pullback fz).obj L ≅ SheafOfModules.unit _ :=
        (Scheme.Modules.pullbackComp fz φ).app M ≪≫ (Scheme.Modules.pullbackCongr hg.symm).app M ≪≫
          ((Scheme.Modules.pullbackComp g (baseChangeSnd (c) zs)).app M).symm ≪≫
          (Scheme.Modules.pullback g).mapIso h0.some ≪≫ Scheme.Modules.pullbackUnitIso g
      exact (isAlgEquivZero_unit (fibreAt x σ z)).of_iso e.symm

    let sk : Spec (CommRingCat.of k) ⟶ Dk := pullback.lift s (𝟙 _) (by rw [Category.id_comp, htoκ])
    have hAEZ := TwoGluedCurves.isAlgEquivZero_fibre_of_isAlgEquivZero_fibre_of_preconnectedSpace k x hXred
      c₁ c₂ i₁ i₂ hcover hcr n hn hn0 𝒱₁ 𝒱₂ σ L hL z h₀ k sk

    let fF := pullback.fst (pullback.snd (c) D.toBase) s
    have hF : fF ≫ pullback.snd (c) D.toBase = pullback.snd _ s ≫ s := pullback.condition

    let eX : pullback (pullback.snd (c) D.toBase) s ⟶ Xk :=
      pullback.lift (fF ≫ pullback.fst _ _) (pullback.snd _ s)
        (by rw [Category.assoc, pullback.condition, reassoc_of% hF, htoκ])
    let eD : pullback (pullback.snd (c) D.toBase) s ⟶ Dk :=
      pullback.lift (fF ≫ pullback.snd _ _) (pullback.snd _ s) (by rw [Category.assoc, reassoc_of% hF, htoκ])
    let eXD : pullback (pullback.snd (c) D.toBase) s ⟶ pullback x σ :=
      pullback.lift eX eD (by simp only [eX, eD, x, σ, pullback.lift_snd])
    have heD : pullback.snd _ s ≫ sk = eD := by
      apply pullback.hom_ext
      · simp only [eD, sk, Category.assoc, pullback.lift_fst, hF]
      · simp only [eD, sk, Category.assoc, pullback.lift_snd, Category.comp_id]
    let e : pullback (pullback.snd (c) D.toBase) s ⟶ pullback (pullback.snd x σ) sk :=
      pullback.lift eXD (pullback.snd _ s) (by rw [heD]; simp only [eXD, pullback.lift_snd])
    have he : e ≫ fibreAt x σ sk = fibreAt (c) D.toBase s := by
      simp only [e, fibreAt, pullback.lift_snd]
    have hefF : e ≫ pullback.fst (pullback.snd x σ) sk ≫ φ = fF := by
      have a2 : e ≫ pullback.fst _ sk = eXD := pullback.lift_fst _ _ _
      have b1 : φ ≫ pullback.fst (c) D.toBase = pullback.fst x σ ≫ pullback.fst _ _ := pullback.lift_fst _ _ _
      have b3 : eXD ≫ pullback.fst x σ = eX := pullback.lift_fst _ _ _
      have b4 : eX ≫ pullback.fst _ _ = fF ≫ pullback.fst _ _ := pullback.lift_fst _ _ _
      have a1 : φ ≫ pullback.snd (c) D.toBase = pullback.snd x σ ≫ pullback.fst _ _ := pullback.lift_snd _ _ _
      have a3 : eXD ≫ pullback.snd x σ = eD := pullback.lift_snd _ _ _
      have a4 : eD ≫ pullback.fst _ _ = fF ≫ pullback.snd _ _ := pullback.lift_fst _ _ _
      apply pullback.hom_ext
      · rw [Category.assoc, Category.assoc, b1, reassoc_of% a2, reassoc_of% b3, b4]
      · rw [Category.assoc, Category.assoc, a1, reassoc_of% a2, reassoc_of% a3, a4]

    have h1 := hAEZ.pullback e he
    have eM : (Scheme.Modules.pullback e).obj ((Scheme.Modules.pullback (pullback.fst (pullback.snd x σ) sk)).obj L) ≅
        (Scheme.Modules.pullback fF).obj M :=
      (Scheme.Modules.pullback e).mapIso ((Scheme.Modules.pullbackComp (pullback.fst (pullback.snd x σ) sk) φ).app M) ≪≫
        (Scheme.Modules.pullbackComp e (pullback.fst (pullback.snd x σ) sk ≫ φ)).app M ≪≫
        (Scheme.Modules.pullbackCongr hefF).app M
    obtain ⟨e2⟩ := nonempty_pullback_fst_ofInvertible_iso (ε := ε) M hM s
    exact (h1.of_iso eM).of_iso e2.symm

end S_AlgebraicGeometry_RelPicard_RepresentsRelSubPic_fibrewiseAlgEquivZero_ofInvertible_norm_pullback_poincare_of_twoGluedCurves_of_mem_of_ringKrullDim_le_one
end P2MW
export P2MW.S_AlgebraicGeometry_RelPicard_RepresentsRelSubPic_fibrewiseAlgEquivZero_ofInvertible_norm_pullback_poincare_of_twoGluedCurves_of_mem_of_ringKrullDim_le_one (solution)
