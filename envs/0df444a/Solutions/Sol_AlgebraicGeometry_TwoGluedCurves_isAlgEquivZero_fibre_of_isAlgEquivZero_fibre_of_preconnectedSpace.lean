-- Prove2me | solution 1 for AlgebraicGeometry.TwoGluedCurves.isAlgEquivZero_fibre_of_isAlgEquivZero_fibre_of_preconnectedSpace
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.122355+00:00
-- url     : https://prove2.me/submissions/cb55c530-ed49-5587-9de5-ebb6504e411b

import Mathlib
import Theorems.Thm_AlgebraicGeometry_RelPicard_exists_fibre_eulerChar_eq_and_isClopen_setOf_fibre_eulerChar_eq
import Theorems.Thm_AlgebraicGeometry_RelPicard_isAlgEquivZero_iff_eulerChar_sectionsOf_eq
import Theorems.Thm_AlgebraicGeometry_RelPicard_isAlgEquivZero_of_isAlgEquivZero_pullback_curveChange_of_twoGluedSmoothCurves
import Theorems.Thm_AlgebraicGeometry_RelPicard_exists_twoAffineOpenCover_fibre_linearEquiv_sectionsOf_of_isPullback
import Definitions.Def_AlgebraicGeometry_RelPicardThetaBundle
import Definitions.Def_AlgebraicGeometry_TwoChartCechSectionsOf
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import Definitions.Def_AlgebraicGeometry_RepresentsRelSubPic
import Definitions.Def_AlgebraicGeometry_RelPicardAlgEquivZeroCut
import Definitions.Def_AlgebraicGeometry_RelPicardPullback
import Definitions.Def_AlgebraicGeometry_TwoAffineOpenCover
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_TwoGluedCurves_isAlgEquivZero_fibre_of_isAlgEquivZero_fibre_of_preconnectedSpace
p2m_attr_erase "instance" "AlgebraicGeometry.OModulePresheaf.isScalarTower AlgebraicGeometry.Scheme.OrderedAffineCover.instLinearOrder AlgebraicGeometry.OModulePresheaf.module AlgebraicGeometry.Scheme.OrderedAffineCover.instFintype AlgebraicGeometry.Scheme.OrderedAffineCover.instFintypeIdx AlgebraicGeometry.OModulePresheaf.addCommGroup AlgebraicGeometry.Scheme.OrderedAffineCover.instDecidableEqIdx AlgebraicGeometry.OModulePresheaf.moduleSections AlgebraicGeometry.OModulePresheaf.instSubsingletonObjZero AlgebraicGeometry.OModulePresheaf.Leray.relAltC_scalarTower AlgebraicGeometry.OModulePresheaf.Leray.ker_relAltd_modΓ AlgebraicGeometry.OModulePresheaf.Leray.relAltC_modΓ AlgebraicGeometry.OModulePresheaf.Leray.biC_abGrp AlgebraicGeometry.OModulePresheaf.Leray.relAltH_modΓ AlgebraicGeometry.OModulePresheaf.Leray.ker_relAltd_smul AlgebraicGeometry.OModulePresheaf.Leray.relAltH_scalarTower AlgebraicGeometry.OModulePresheaf.Leray.relAltH_smul AlgebraicGeometry.OModulePresheaf.Leray.biC_module AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instDecidableEqIdx AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instFintype AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instLinearOrder AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instFintypeIdx DoubleComplex.instModuleE₂I DoubleComplex.Bounded.modR DoubleComplex.instModuleE₂II DoubleComplex.instAddCommGroupE₂II DoubleComplex.Bounded.abGrp DoubleComplex.instAddCommGroupE₂I AlgebraicGeometry.ChowDatum.hι_closed AlgebraicGeometry.ChowDatumProj.hιN_closed AlgebraicGeometry.ChowDatumProj.hp_proper AlgebraicGeometry.ChowDatum.hp_isoU AlgebraicGeometry.ChowDatum.hp_proper AlgebraicGeometry.ProjSpace.algebraAway AlgebraicGeometry.ProjSpace.instIsProperProdOverπ AlgebraicGeometry.ChowDatumProj.hp_isoU AlgebraicGeometry.ProjSpace.isProper_π AlgebraicGeometry.ProjSpace.finiteType_mvPolynomial ProjSpaceCech.GradedModule.H.module ProjSpaceCech.GradedModule.H.addCommGroup"
p2m_attr_erase "instance" "ProjSpaceCech.GradedModule.sec.instAdd ProjSpaceCech.GradedModule.sec.instNeg ProjSpaceCech.GradedModule.acg ProjSpaceCech.GradedModule.Frac.setoid ProjSpaceCech.GradedModule.modR ProjSpaceCech.GradedModule.sec.instModule ProjSpaceCech.GradedModule.sec.instAddCommGroup ProjSpaceCech.GradedModule.sec.instZero ProjSpaceCech.GradedModule.Presentation.fJ ProjSpaceCech.GradedModule.sec.instSMul ProjSpaceCech.Twist.H.module ProjSpaceCech.Idx.instFintype ProjSpaceCech.Twist.H.addCommGroup ProjSpaceCech.Idx.instDecidableEq ProjSpaceCech.Twist.Mon.instDecidableEq ProjSpaceCech.Twist.cochain.instAddCommGroup ProjSpaceCech.Twist.cochain.instModule AlgebraicGeometry.RelEffCartierDiv.isIso_subschemeIota_snd_of_degree_one AlgebraicGeometry.isIso_ker_graphOver_subschemeIota_snd AlgebraicGeometry.isClosedImmersion_graphOver AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instNeg AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instSMulInt AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instAddCommGroup AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instAdd AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instSub AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instModuleCarrierObjOppositeOpensCarrierCarrierCommRingCatPresheafOpOpensTop AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instSMulCarrierObjOppositeOpensCarrierCarrierCommRingCatPresheafOpOpensTop AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instSMulNat AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instZero AlgebraicGeometry.Scheme.Modules.preservesBinaryProducts_opensMap AlgebraicGeometry.Scheme.Modules.pullback_monoidal AlgebraicGeometry.Scheme.Modules.sheafify_isLocalization' AlgebraicGeometry.Scheme.Modules.preservesTerminal_opensMap AlgebraicGeometry.Scheme.Modules.pullback₀_monoidal AlgebraicGeometry.Scheme.Modules.preservesFiniteProducts_opensMap AlgebraicGeometry.Scheme.Modules.instLiftingPresheafOfModulesSheafifyPresheafWOpensCarrierCarrierCommRingCatGrothendieckTopologyObjFunctorOppositeIsSheafSheafCompPullback₀Pullback PresheafOfModules.PullbackMonoidal.pullback_monoidal PresheafOfModules.PullbackMonoidal.isIso_δ PresheafOfModules.pushforward_laxMonoidal PresheafOfModules.PullbackMonoidal.isIso_η"
p2m_attr_erase "instance" "PresheafOfModules.free_monoidal PresheafOfModules.restrictScalars_laxMonoidal PresheafOfModules.PullbackMonoidal.isIso_δ_gS PresheafOfModules.pullback_oplaxMonoidal PresheafOfModules.PullbackMonoidal.instPreservesColimitsOfSizeCompOppositeCommRingCatRingCatForget₂RingHomCarrierCarrierPb PresheafOfModules.pullback_monoidal' AlgebraicGeometry.RelEffCartierDiv.subsingleton_of_degree_zero AlgebraicCurve.Place.instIsScalarTowerSubtypeMemValuationSubringToValuationSubring AlgebraicCurve.Divisor.instDistribMulActionAlgEquiv AlgebraicCurve.Place.instSMulAlgEquiv AlgebraicCurve.Place.instIsPrincipalIdealRingSubtypeMemValuationSubringToValuationSubring AlgebraicCurve.Place.instIsDiscreteValuationRingSubtypeMemValuationSubringToValuationSubring AlgebraicCurve.Pic0.instDistribMulActionAlgEquiv AlgebraicCurve.Place.instAlgebraSubtypeMemValuationSubringToValuationSubring AlgebraicCurve.Place.instMulActionAlgEquiv AlgebraicCurve.Pic0.instSMulAlgEquiv AlgebraicCurve.IsCurveOver.instNontrivialKaehler AlgebraicCurve.IsCurveOver.instFreeKaehler AlgebraicCurve.IsCurveOver.toHasPrincipalDivisors AlgebraicCurve.IsCurveOver.instFiniteResidue AlgebraicCurve.CurveModel.isProper AlgebraicCurve.CurveModel.isIntegral AlgebraicCurve.CurveModel.smooth AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.instFundamentalIdentityOfSumRamificationInertia AlgebraicCurve.Place.instIsScalarTowerResidueFieldRestrictPushforward AlgebraicCurve.Place.instAlgebraResidueFieldRestrictPushforward AlgebraicCurve.Place.instIsLocalHomRestrictInclusion AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.SemilinearAut.instDistribMulActionSubtypeProdRingAutMemSubgroupPic0 AlgebraicCurve.SemilinearAut.instDistribMulActionSubtypeProdRingAutMemSubgroupDivisor AlgebraicCurve.Pic0.instModuleZModTorsion AlgebraicCurve.SemilinearAut.instSMulSubtypeProdRingAutMemSubgroupPlace AlgebraicCurve.SemilinearAut.instDistribMulActionTorsion AlgebraicCurve.SemilinearAut.instSMulSubtypeProdRingAutMemSubgroupPic0"
p2m_attr_erase "instance" "AlgebraicCurve.SemilinearAut.instSMulTorsion AlgebraicCurve.SemilinearAut.instMulActionSubtypeProdRingAutMemSubgroupPlace AlgebraicCurve.SemilinearAut.instSMulCommClassZModTorsion AlgebraicCurve.SemilinearAut.instMulSemiringActionSubtypeProdRingAutMemSubgroup instDecEqAlgebraicClosureRat WeierstrassCurve.Affine.Point.instDistribMulActionAlgEquiv WeierstrassCurve.Affine.Point.instModuleZModTorsionBy WeierstrassCurve.Affine.Point.instSMulTorsionBy WeierstrassCurve.Affine.Point.instDistribMulActionTorsionBy WeierstrassCurve.Affine.Point.instSMulAlgEquiv WeierstrassCurve.Affine.Point.instSMulCommClassAlgEquivZModTorsionBy AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions AlgebraicCurve.instHasLocalResidue_of_hasCanonicalLocalResidueK AlgebraicCurve.instHasCanonicalLocalResidueK_of_hasCanonicalLocalResidueKStar AlgebraicCurve.Place.kw_ffgc_finiteDimensional_adicCompletion instAlgebraSubtypeMemValuationSubring_definitions AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersIntegersCompletion ModularCurve.KwF4gRRTate.instAlgebraKAdicCompletionIntegers AlgebraicCurve.Place.kw_ffgc_continuousSMul_adicCompletionComap AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersCompletionCompletion IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions AlgebraicCurve.instHasCanonicalLocalResidueK AlgebraicCurve.Place.instAlgebra_restrictResidueField AlgebraicCurve.Place.instIsScalarTower_restrictResidueField AlgebraicCurve.instHasLocalResidue AlgebraicCurve.HasSeparableResidue.of_perfectField_of_isCurveOver AlgebraicCurve.HasSeparableResidue.of_perfectField AlgebraicCurve.Place.instIsLocalHom_restrictSubringHom AlgebraicCurve.instHasCanonicalLocalResidueKStar ModularCurve.KwNo6Pin.isLocalRing_completion SheafOfModules.isIso_ihomModelToIhom"
p2m_attr_erase "simp" "AlgebraicGeometry.Scheme.OrderedAffineCover.mk.injEq AlgebraicGeometry.OModulePresheaf.mk.sizeOf_spec AlgebraicGeometry.Scheme.OrderedAffineCover.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.mk.injEq TwoChartCech.Mumford.dK_apply TwoChartCech.Mumford.ι0_apply TwoChartCech.Mumford.ι1_apply TwoChartCech.KerCoprod.dK_apply TwoChartCech.KerCoprod.ι1_apply TwoChartCech.KerCoprod.ι0_apply AlgebraicGeometry.OModulePresheaf.prod_obj AlgebraicGeometry.OModulePresheaf.restrOpen_obj AlgebraicGeometry.OModulePresheaf.DevissageStep.mk.injEq AlgebraicGeometry.OModulePresheaf.pushforward_obj AlgebraicGeometry.OModulePresheaf.im_obj AlgebraicGeometry.OModulePresheaf.pow_obj AlgebraicGeometry.OModulePresheaf.fstHom_app AlgebraicGeometry.OModulePresheaf.ker_obj AlgebraicGeometry.OModulePresheaf.coker_obj AlgebraicGeometry.OModulePresheaf.DevissageStep.mk.sizeOf_spec AlgebraicGeometry.Scheme.OrderedAffineCover.preimage_U AlgebraicGeometry.OModulePresheaf.sndHom_app AlgebraicGeometry.OModulePresheaf.Hom.mk.injEq AlgebraicGeometry.OModulePresheaf.Hom.id_app AlgebraicGeometry.OModulePresheaf.AffHom.appSections_apply AlgebraicGeometry.OModulePresheaf.AffHom.comp_app AlgebraicGeometry.OModulePresheaf.AffSES.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.AffHom.kerMap_coe AlgebraicGeometry.OModulePresheaf.AffHom.id_app AlgebraicGeometry.OModulePresheaf.Hom.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.Hom.toAffHom_app AlgebraicGeometry.OModulePresheaf.SES.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.AffHom.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.Hom.comp_app AlgebraicGeometry.OModulePresheaf.SES.mk.injEq AlgebraicGeometry.OModulePresheaf.AffHom.mk.injEq AlgebraicGeometry.OModulePresheaf.Hom.appSections_apply AlgebraicGeometry.OModulePresheaf.AffSES.mk.injEq AlgebraicGeometry.OModulePresheaf.Leray.restrictToPreimage_U AlgebraicGeometry.Scheme.OrderedAffineCover.toCoverOf_U"
p2m_attr_erase "simp" "AlgebraicGeometry.Scheme.OrderedAffineCoverOf.mk.sizeOf_spec AlgebraicGeometry.Scheme.OrderedAffineCoverOf.mk.injEq AlgebraicGeometry.Scheme.OrderedAffineCover.restrict_U DoubleComplex.Bounded.mk.injEq DoubleComplex.Bounded.mk.sizeOf_spec DoubleComplex.Convergence.mk.injEq DoubleComplex.Convergence.mk.sizeOf_spec DoubleComplex.SubQuot.mk.sizeOf_spec DoubleComplex.SubQuot.mk.injEq AlgebraicGeometry.ChowDatumProj.mk.sizeOf_spec AlgebraicGeometry.ChowDatum.mk.sizeOf_spec AlgebraicGeometry.ChowDatumProj.mk.injEq AlgebraicGeometry.ChowDatum.mk.injEq ProjSpaceCech.GradedModule.mk.injEq ProjSpaceCech.GradedModule.mk.sizeOf_spec ProjSpaceCech.GradedModule.Frac.mk.sizeOf_spec ProjSpaceCech.GradedModule.Presentation.mk.injEq ProjSpaceCech.GradedModule.Frac.mk.injEq ProjSpaceCech.GradedModule.Presentation.mk.sizeOf_spec ProjSpaceCech.GradedModule.Hom.shift_toLinearMap ProjSpaceCech.GradedModule.Hom.mk.sizeOf_spec ProjSpaceCech.GradedModule.Hom.mk.injEq AlgebraicGeometry.tilde.functorCompPullbackSpecIso_app AlgebraicGeometry.Scheme.Modules.tensorSections_zero_right AlgebraicGeometry.Scheme.Modules.map_unitSection AlgebraicGeometry.Scheme.Modules.tensorSectionsBilin_apply AlgebraicGeometry.Scheme.Modules.tensorPowSection_zero AlgebraicGeometry.Scheme.Modules.tensorSections_zero_left AlgebraicGeometry.Scheme.Modules.tensorPow_zero AlgebraicGeometry.Scheme.Modules.tensorPow_succ AlgebraicGeometry.RelPicard.fst_toProdSpec AlgebraicGeometry.RelPicard.toProdSpec_fst_assoc AlgebraicGeometry.RelPicard.pointsSubBasepointModule_cons AlgebraicGeometry.RelPicard.pointsSubBasepointModule_nil AlgebraicGeometry.RelPicard.fst_toProdSpec_assoc AlgebraicGeometry.RelPicard.toProdSpec_fst AlgebraicGeometry.graphOver_fst_assoc AlgebraicGeometry.RelEffCartierDiv.toPoint_comp AlgebraicGeometry.RelEffCartierDiv.toPoint_comp_assoc AlgebraicGeometry.graphOver_fst"
p2m_attr_erase "simp" "AlgebraicGeometry.RelEffCartierDiv.ofPoint_I AlgebraicGeometry.graphOver_snd AlgebraicGeometry.graphOver_snd_assoc AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.sub_app AlgebraicGeometry.Scheme.IdealSheafData.sres_sresTop AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.add_app AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.mk.sizeOf_spec AlgebraicGeometry.Scheme.IdealSheafData.coe_resLE AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.smul_app AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.coe_ofLE_app AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.ideal_range AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.zero_app AlgebraicGeometry.Scheme.IdealSheafData.sres_sres AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.comp_app AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.neg_app AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.id_app AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.coe_mulRight_app AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.nsmul_app AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.mk.injEq AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.zsmul_app PresheafOfModules.freeεIso_hom_app PresheafOfModules.freeμIso_hom_app AlgebraicGeometry.prodKerGraph_one AlgebraicGeometry.fibrePowOver.proj_comp AlgebraicGeometry.prodKerGraph_zero AlgebraicGeometry.RelEffCartierDiv.empty_I AlgebraicGeometry.fibrePowOver.proj_comp_assoc AlgebraicCurve.SymmetricPowerPackage.mk.sizeOf_spec AlgebraicCurve.SymmetricPowerPackage.mk.injEq AlgebraicCurve.Place.mk.injEq AlgebraicCurve.Divisor.degree_single AlgebraicCurve.Divisor.smul_single AlgebraicCurve.Place.smul_toValuationSubring AlgebraicCurve.Place.heightOneSpectrum_asIdeal AlgebraicCurve.Place.coe_algebraMap AlgebraicCurve.Place.ord_one AlgebraicCurve.Place.coe_smulRingEquiv_apply AlgebraicCurve.Pic0.coe_degZeroSMulHom AlgebraicCurve.Place.deg_smul AlgebraicCurve.Pic0.mk_zero"
p2m_attr_erase "simp" "AlgebraicCurve.Place.mk.sizeOf_spec AlgebraicCurve.Divisor.degree_smul AlgebraicCurve.Pic0.mk_add AlgebraicCurve.Place.ord_zero AlgebraicCurve.Place.ofHeightOneSpectrum_toValuationSubring AlgebraicCurve.mulAdele_apply AlgebraicCurve.residuePairing_apply_coe AlgebraicCurve.mem_adeleBdd AlgebraicCurve.weilSmul_one AlgebraicCurve.diagonalHom_apply AlgebraicCurve.weilSmul_apply AlgebraicCurve.adeleSpaceMul_coe AlgebraicCurve.mulAdele_one AlgebraicCurve.CurveModel.mk.injEq AlgebraicCurve.CurveModel.mk.sizeOf_spec AlgebraicCurve.coe_cechH0Equiv_apply AlgebraicCurve.cechH1ToH1_mk AlgebraicCurve.lSpaceOn_univ AlgebraicCurve.lSpaceOn_empty AlgebraicCurve.Place.congrEquiv_symm_apply AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply AlgebraicCurve.RationalFunctionField.deg_placeOfPoint AlgebraicCurve.Divisor.mapRestrict_single AlgebraicCurve.Divisor.pushforward_single AlgebraicCurve.Place.coe_restrictInclusion AlgebraicCurve.Place.mem_fiber AlgebraicCurve.Place.restrict_toValuationSubring AlgebraicCurve.Divisor.degree_pushforward AlgebraicCurve.Place.restrictResidueMap_residue AlgebraicCurve.Pic0.coe_pushforwardDegZeroHom AlgebraicCurve.Pic0.coe_pullbackDegZeroHom AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal AlgebraicCurve.IsFrobeniusEndo.frobNormRingHom_apply"
p2m_attr_erase "simp" "ModularCurve.frobeniusPushforwardGeomLevelPic0_mk ModularCurve.coe_frobeniusGeomLevelEquiv_apply ModularCurve.coe_frobeniusPushforwardGeomLevelDegZero ModularCurve.heckeFibreGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusGeomLevel_apply_coe ModularCurve.frobeniusPullbackGeomLevelPic0OfIsCurveOver_mk ModularCurve.coe_heckeFibreGeomLevelDegZero ModularCurve.coe_frobeniusPullbackGeomLevelDegZero ModularCurve.frobeniusPullbackGeomLevelPic0_mk ModularCurve.frobeniusPullbackGeomLevel_single ModularCurve.heckeFibreGeomLevelPic0_mk ModularCurve.frobeniusPushforwardGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusPushforwardGeomLevel_single ModularCurve.qExpandAlgC_apply AlgebraicCurve.Divisor.degree_pushforwardAlong AlgebraicCurve.Pic0.coe_degZeroCorrespondence AlgebraicCurve.Place.mem_fiberAlong AlgebraicCurve.SemilinearAut.toRingAut_inv AlgebraicCurve.SemilinearAut.smul_def AlgebraicCurve.SemilinearAut.smul_single AlgebraicCurve.SemilinearAut.smul_toValuationSubring AlgebraicCurve.SemilinearAut.baseAut_inv AlgebraicCurve.SemilinearAut.baseAut_ofAlgAut AlgebraicCurve.SemilinearAut.toRingAut_ofAlgAut AlgebraicCurve.SemilinearAut.torsionRep_apply AlgebraicCurve.SemilinearAut.toRingAut_one AlgebraicCurve.SemilinearAut.deg_smul AlgebraicCurve.SemilinearAut.degree_smul AlgebraicCurve.SemilinearAut.coe_degZeroSMulHom AlgebraicCurve.SemilinearAut.baseAut_mul AlgebraicCurve.SemilinearAut.coe_smulValuationSubringEquiv_apply AlgebraicCurve.SemilinearAut.baseAut_one AlgebraicCurve.SemilinearAut.ofAlgAut_smul AlgebraicCurve.SemilinearAut.coe_torsion_smul AlgebraicCurve.SemilinearAut.toRingAut_mul AlgebraicCurve.coe_frobeniusPushforwardDegZero AlgebraicCurve.IsFrobeniusEndo.coe_frobeniusPullbackDegZero ModularCurve.jqNModC_one ModularCurve.qExpand_coeff_mul ModularCurve.qExpandₐ_apply"
p2m_attr_erase "simp" "ModularCurve.jqN_one ModularCurve.qExpand_single ModularCurve.dedekindPsi_one ModularCurve.ModularPolynomialData.mk.sizeOf_spec ModularCurve.evalAtJ_X ModularCurve.ModularPolynomialData.mk.injEq ModularCurve.constantCoeff_jNum ModularCurve.constantCoeff_eisenstein4 ModularCurve.qExpand_C ModularCurve.coeff_jq_neg_one ModularCurve.constantCoeff_jNumQ ModularCurve.reduceModBivar_C_X ModularCurve.laurentMap_coeff ModularCurve.reduceModBivar_X ModularCurve.laurentMap_single ModularCurve.evalAtJInt_X ModularCurve.evalAtJMod_X ModularCurve.jqNMod_one ModularCurve.aeval_heckeGen ModularCurve.coe_mTorsionGaloisRep_apply ModularCurve.eisensteinSystem_of_dvd ModularCurve.eisensteinSystem_of_not_dvd FreyPackage.mk.sizeOf_spec FreyPackage.mk.injEq WeierstrassCurve.Affine.Point.galoisRepModuleEnd_apply AlgebraicCurve.RationalFunctionField.placeInfty_toValuationSubring AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none AlgebraicCurve.Divisor.evalFun_zero AlgebraicCurve.Place.evalAt_one AlgebraicCurve.Place.differentialCoeff_zero AlgebraicCurve.Place.differentialCoeff_dCoord AlgebraicCurve.TranscendenceTower.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.injEq AlgebraicCurve.TranscendenceTower.mk.injEq AlgebraicCurve.PoleDivisorPackage.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.sizeOf_spec AlgebraicCurve.PoleDivisorPackage.mk.injEq"
p2m_attr_erase "simp" "AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.sizeOf_spec AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.injEq AlgebraicCurve.adeleSingle_coe AlgebraicCurve.kaehlerResidueTermKFam_apply AlgebraicCurve.Place.LocalResidueData.mk.injEq AlgebraicCurve.Place.LocalResidueData.mk.sizeOf_spec AlgebraicCurve.Place.kw_ffgc_adicCompletionComapIntegers_coe AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.sizeOf_spec AlgebraicCurve.Place.mem_simplePoleSubmodule AlgebraicCurve.Place.coe_uniformizerSubring ModularCurve.Lg37.Lg37CompletionSection.mk.injEq AlgebraicCurve.Place.CoefficientFieldSection.mk.injEq AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.injEq ModularCurve.Lg37.Lg37CompletionSection.mk.sizeOf_spec AlgebraicCurve.Place.CoefficientFieldSection.mk.sizeOf_spec AlgebraicCurve.Place.poleSubmodule_one AlgebraicCurve.Place.mem_poleSubmodule AlgebraicGeometry.Scheme.Modules.toUnitSection_ofUnitSection AlgebraicGeometry.Scheme.Modules.pullbackSection_def AlgebraicGeometry.Scheme.Modules.ofUnitSection_toUnitSection PresheafOfModules.InternalHom.IsSheafAux.appAt_toPresheafHom SheafOfModules.ihomSectionsEquivFamily_unit AlgebraicGeometry.Scheme.Modules.restrictHomEquivFamily_apply SheafOfModules.ihomEval_unit_app AlgebraicGeometry.Scheme.Modules.ihomEval_zero_right AlgebraicGeometry.Scheme.Modules.ihomEval_zero_left AlgebraicGeometry.Scheme.Modules.homOfFamily_app_apply SheafOfModules.unit_ihomSectionsEquivFamily AlgebraicGeometry.Scheme.Modules.familyOfHom_app AlgebraicGeometry.Scheme.Modules.restrictUnitIso_hom_app_apply AlgebraicGeometry.Scheme.Modules.restrictUnitIso_inv_app_apply AlgebraicGeometry.Scheme.Modules.restrictHomOfFamily_app_apply AlgebraicGeometry.Scheme.Modules.restrictHomEquivFamily_symm_apply AlgebraicGeometry.Scheme.Modules.pullbackLocalSection_neg AlgebraicGeometry.Scheme.Modules.pullbackLocalSection_zero AlgebraicGeometry.Scheme.Modules.pullbackLocalSection_sub AlgebraicGeometry.Scheme.Modules.pullbackLocalSection_add AlgebraicGeometry.RelPicard.algEquivZeroGroupCut_toSubPicCondition AlgebraicGeometry.RelPicard.SubPicGroupCondition.mk.injEq AlgebraicGeometry.RelPicard.SubPicGroupCondition.mk.sizeOf_spec"
p2m_attr_erase "simp" "AlgebraicGeometry.RelPicard.SubPicCondition.onClasses_mk AlgebraicGeometry.RelPicard.relSubPicPresheaf_map_coe GoodReductionJacobian.relativeGroupLawOfGrpObj_inv GoodReductionJacobian.relativeGroupLawOfGrpObj_mul GoodReductionJacobian.overHomEquivSchemeHomOver_apply_coe GoodReductionJacobian.relativeGroupLawOfGrpObj_one GoodReductionJacobian.overHomEquivSchemeHomOver_symm_apply_left"

set_option autoImplicit false

universe u

p2m_open "CategoryTheory CategoryTheory.Limits AlgebraicGeometry P2MW.S_AlgebraicGeometry_TwoGluedCurves_isAlgEquivZero_fibre_of_isAlgEquivZero_fibre_of_preconnectedSpace.AlgebraicGeometry NeronModelInfra GoodReductionJacobian AlgebraicGeometry.RelPicard"

namespace AlgebraicGeometry
p2m_export "AlgebraicGeometry" "SmoothOfRelativeDimension IsProper Scheme.Modules.pullback GeometricallyIntegral.geometrically_isIntegral GeometricallyIntegral LocallyOfFiniteType Spec IsIntegral Scheme Spec.map_surjective IsClosedImmersion IsReduced smoothOfRelativeDimension_isStableUnderBaseChange Scheme.Modules.pullbackCongr Scheme.Modules Scheme.Modules.pullbackComp Scheme.Modules.IsInvertible Scheme.Modules.pullbackUnitIso Scheme.Modules.isInvertible_unit Scheme.TwoAffineOpenCover Scheme.TwoAffineOpenCover.specMap"
namespace ConstFam
p2m_open "AlgebraicGeometry"

p2m_open "CategoryTheory.MonoidalCategory"

variable {k : Type u} [Field k] {C : Scheme.{u}} (c : C ⟶ Spec (CommRingCat.of k)) {T : Scheme.{u}}
  (t : T ⟶ Spec (CommRingCat.of k))

noncomputable def pbComp {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) (N : Z.Modules) :
    (Scheme.Modules.pullback f).obj ((Scheme.Modules.pullback g).obj N) ≅ (Scheme.Modules.pullback (f ≫ g)).obj N :=
  (Scheme.Modules.pullbackComp f g).app N

noncomputable def pbCongr {X Y : Scheme.{u}} {f g : X ⟶ Y} (h : f = g) (N : Y.Modules) :
    (Scheme.Modules.pullback f).obj N ≅ (Scheme.Modules.pullback g).obj N :=
  (Scheme.Modules.pullbackCongr h).app N

theorem isPullback_baseChangeSnd {K : Type u} [Field K] (s : Spec (CommRingCat.of K) ⟶ T)
    (x : Spec (CommRingCat.of K) ⟶ Spec (CommRingCat.of k)) (hx : s ≫ t = x) :
    IsPullback (baseChangeSnd c (⟨s, hx⟩ : SchemeHomOver x t)) (pullback.snd c x) (pullback.snd c t) s := by
  have outer : IsPullback (baseChangeSnd c (⟨s, hx⟩ : SchemeHomOver x t) ≫ pullback.fst c t) (pullback.snd c x) c
      (s ≫ t) := by
    rw [show baseChangeSnd c (⟨s, hx⟩ : SchemeHomOver x t) ≫ pullback.fst c t = pullback.fst c x by
      rw [baseChangeSnd, pullback.lift_fst, Category.comp_id], hx]
    exact IsPullback.of_hasPullback c x
  exact IsPullback.of_right outer (by rw [baseChangeSnd, pullback.lift_snd]) (IsPullback.of_hasPullback c t)

theorem isAlgEquivZero_fibre_iff {K : Type u} [Field K] (s : Spec (CommRingCat.of K) ⟶ T)
    (x : Spec (CommRingCat.of K) ⟶ Spec (CommRingCat.of k)) (hx : s ≫ t = x) (M : (pullback c t).Modules) :
    IsAlgEquivZero (fibreAt c t s) (fibreModule c t s M) ↔
      IsAlgEquivZero (pullback.snd c x) ((Scheme.Modules.pullback (baseChangeSnd c (⟨s, hx⟩ : SchemeHomOver x t))).obj M) := by
  let φ := (isPullback_baseChangeSnd c t s x hx).isoPullback
  have hφ : φ.hom ≫ fibreAt c t s = pullback.snd c x := IsPullback.isoPullback_hom_snd _
  have hφ' : φ.inv ≫ pullback.snd c x = fibreAt c t s := by rw [← hφ, Iso.inv_hom_id_assoc]
  have hfst : φ.hom ≫ pullback.fst (pullback.snd c t) s = baseChangeSnd c ⟨s, hx⟩ := IsPullback.isoPullback_hom_fst _
  constructor
  · intro h
    exact (h.pullback φ.hom hφ).of_iso (pbComp _ _ _ ≪≫ pbCongr hfst _)
  · intro h
    refine (h.pullback φ.inv hφ').of_iso (pbComp _ _ _ ≪≫ pbCongr ?_ _)
    rw [← hfst, Iso.inv_hom_id_assoc]

theorem eulerChar_eq_of_forall (K : Type u) [Field K] [Algebra k K] (s : Spec (CommRingCat.of K) ⟶ T)
    (hx : s ≫ t = Scheme.TwoAffineOpenCover.specMap k K) (M : (pullback c t).Modules) (e : ℤ)
    (he : ∀ 𝒲 : (pullback (pullback.snd c t) s).TwoAffineOpenCover, ((Module.finrank K (𝒲.sectionsOf (fibreAt c t s) (fibreModule c t s M)).H0 : ℤ) - Module.finrank K (𝒲.sectionsOf (fibreAt c t s) (fibreModule c t s M)).H1) = e)
    (𝒱 : C.TwoAffineOpenCover) (F : (pullback c (Scheme.TwoAffineOpenCover.specMap k K)).Modules)
    (eF : F ≅ (Scheme.Modules.pullback (baseChangeSnd c (⟨s, hx⟩ : SchemeHomOver _ t))).obj M) :
    ((Module.finrank K ((𝒱.pullback c K).sectionsOf (pullback.snd c (Scheme.TwoAffineOpenCover.specMap k K)) F).H0 : ℤ) - Module.finrank K ((𝒱.pullback c K).sectionsOf (pullback.snd c (Scheme.TwoAffineOpenCover.specMap k K)) F).H1) = e := by
  obtain ⟨𝒲, ⟨e0⟩, ⟨e1⟩⟩ := exists_twoAffineOpenCover_fibre_linearEquiv_sectionsOf_of_isPullback c t M s
    (pullback.snd c (Scheme.TwoAffineOpenCover.specMap k K)) (baseChangeSnd c ⟨s, hx⟩)
    (isPullback_baseChangeSnd c t s _ hx) F eF (𝒱.pullback c K)
  rw [← he 𝒲, e0.finrank_eq, e1.finrank_eq]

end AlgebraicGeometry.ConstFam

namespace AlgebraicGeometry
p2m_export "AlgebraicGeometry" "SmoothOfRelativeDimension IsProper Scheme.Modules.pullback GeometricallyIntegral.geometrically_isIntegral GeometricallyIntegral LocallyOfFiniteType Spec IsIntegral Scheme Spec.map_surjective IsClosedImmersion IsReduced smoothOfRelativeDimension_isStableUnderBaseChange Scheme.Modules.pullbackCongr Scheme.Modules Scheme.Modules.pullbackComp Scheme.Modules.IsInvertible Scheme.Modules.pullbackUnitIso Scheme.Modules.isInvertible_unit Scheme.TwoAffineOpenCover Scheme.TwoAffineOpenCover.specMap"
namespace ConstFam
p2m_open "AlgebraicGeometry"

p2m_open "CategoryTheory.MonoidalCategory"

open _root_.AlgebraicGeometry.Scheme.TwoAffineOpenCover in

theorem component
    (k : Type u) [Field k] [IsAlgClosed k]
    {X C' : Scheme.{u}} (x : X ⟶ Spec (CommRingCat.of k))
    (c' : C' ⟶ Spec (CommRingCat.of k)) [IsProper c'] [SmoothOfRelativeDimension 1 c'] [GeometricallyIntegral c']
    (i : SchemeHomOver c' x) (𝒱 : C'.TwoAffineOpenCover)
    {S : Scheme.{u}} (σ : S ⟶ Spec (CommRingCat.of k)) [LocallyOfFiniteType σ] [PreconnectedSpace ↥S]
    (L : (pullback x σ).Modules) (hL : Scheme.Modules.IsInvertible L)
    {k₀ : Type u} [Field k₀] [IsAlgClosed k₀] (s₀ : Spec (CommRingCat.of k₀) ⟶ S)
    (h₀ : IsAlgEquivZero (fibreAt x σ s₀) (fibreModule x σ s₀ L))
    (K : Type u) [Field K] [IsAlgClosed K] [Algebra k K] (s : Spec (CommRingCat.of K) ⟶ S)
    (hx : s ≫ σ = specMap k K) :
    IsAlgEquivZero (pullback.snd c' (specMap k K))
      ((Scheme.Modules.pullback (baseChangeSnd c' (⟨s, hx⟩ : SchemeHomOver _ σ))).obj
        ((Scheme.Modules.pullback (curveChange i.1 i.2 σ)).obj L)) := by
  haveI := smoothOfRelativeDimension_isStableUnderBaseChange 1

  set L' := (Scheme.Modules.pullback (curveChange i.1 i.2 σ)).obj L with hL'def
  have hL' : Scheme.Modules.IsInvertible L' := hL.pullback _
  obtain ⟨hwd, hcl⟩ := exists_fibre_eulerChar_eq_and_isClopen_setOf_fibre_eulerChar_eq k c' 𝒱 σ L' hL'
  obtain ⟨hwd1, hcl1⟩ := exists_fibre_eulerChar_eq_and_isClopen_setOf_fibre_eulerChar_eq k c' 𝒱 σ
    (𝟙_ (pullback c' σ).Modules) (Scheme.Modules.isInvertible_unit _)

  have hint : ∀ (K' : Type u) [Field K'] [Algebra k K'], IsIntegral (pullback c' (specMap k K')) :=
    fun K' _ _ => GeometricallyIntegral.geometrically_isIntegral (f := c') (specMap k K') (pullback.fst c' _)
      (pullback.snd c' _) (IsPullback.of_hasPullback _ _)
  have hsm : ∀ (K' : Type u) [Field K'] [Algebra k K'], SmoothOfRelativeDimension 1 (pullback.snd c' (specMap k K')) :=
    fun K' _ _ => MorphismProperty.pullback_snd (P := @SmoothOfRelativeDimension 1) _ _ inferInstance

  have key : ∀ (K' : Type u) [Field K'] [IsAlgClosed K'] [Algebra k K'] (s' : Spec (CommRingCat.of K') ⟶ S)
      (hx' : s' ≫ σ = specMap k K'),
      (IsAlgEquivZero (pullback.snd c' (specMap k K'))
        ((Scheme.Modules.pullback (baseChangeSnd c' (⟨s', hx'⟩ : SchemeHomOver _ σ))).obj L') ↔
      ((Module.finrank K' ((𝒱.pullback c' K').sectionsOf (pullback.snd c' (specMap k K')) ((Scheme.Modules.pullback (baseChangeSnd c' (⟨s', hx'⟩ : SchemeHomOver _ σ))).obj L')).H0 : ℤ) - Module.finrank K' ((𝒱.pullback c' K').sectionsOf (pullback.snd c' (specMap k K')) ((Scheme.Modules.pullback (baseChangeSnd c' (⟨s', hx'⟩ : SchemeHomOver _ σ))).obj L')).H1) =
        ((Module.finrank K' ((𝒱.pullback c' K').sectionsOf (pullback.snd c' (specMap k K')) (SheafOfModules.unit (pullback c' (specMap k K')).ringCatSheaf : (pullback c' (specMap k K')).Modules)).H0 : ℤ) - Module.finrank K' ((𝒱.pullback c' K').sectionsOf (pullback.snd c' (specMap k K')) (SheafOfModules.unit (pullback c' (specMap k K')).ringCatSheaf : (pullback c' (specMap k K')).Modules)).H1)) := by
    intro K' _ _ _ s' hx'
    haveI := hint K'
    haveI := hsm K'
    exact isAlgEquivZero_iff_eulerChar_sectionsOf_eq K' (pullback.snd c' (specMap k K')) _ (hL'.pullback _) (𝒱.pullback c' K')

  obtain ⟨φ₀, hφ₀⟩ := Spec.map_surjective (s₀ ≫ σ)
  letI alg₀ : Algebra k k₀ := φ₀.hom.toAlgebra
  have hx₀ : s₀ ≫ σ = specMap k k₀ := hφ₀.symm

  have hA₀ : IsAlgEquivZero (pullback.snd c' (specMap k k₀))
      ((Scheme.Modules.pullback (baseChangeSnd c' (⟨s₀, hx₀⟩ : SchemeHomOver _ σ))).obj L') := by
    have h1 := (isAlgEquivZero_fibre_iff x σ s₀ _ hx₀ L).mp h₀
    have h2 := h1.pullback (curveChange i.1 i.2 (specMap k k₀)) (curveChange_snd i.1 i.2 _)
    refine h2.of_iso (pbComp _ _ _ ≪≫ pbCongr (curveChange_baseChangeSnd i.1 i.2 ⟨s₀, hx₀⟩) _ ≪≫ (pbComp _ _ _).symm)

  obtain ⟨e₀, he₀⟩ := hwd (s₀.base (IsLocalRing.closedPoint k₀))
  obtain ⟨e₀', he₀'⟩ := hwd1 (s₀.base (IsLocalRing.closedPoint k₀))
  have hχ₀ := eulerChar_eq_of_forall c' σ k₀ s₀ hx₀ L' e₀ (he₀ k₀ s₀ rfl) 𝒱 _ (Iso.refl _)
  have hχ₀' := eulerChar_eq_of_forall c' σ k₀ s₀ hx₀ (𝟙_ _) e₀' (he₀' k₀ s₀ rfl) 𝒱
    (SheafOfModules.unit (pullback c' (specMap k k₀)).ringCatSheaf) (Scheme.Modules.pullbackUnitIso _).symm
  have hee : e₀ = e₀' := by rw [← hχ₀, ← hχ₀', ← key k₀ s₀ hx₀]; exact hA₀

  have hZ : {y : S | ∀ (K' : Type u) [Field K'] (s' : Spec (CommRingCat.of K') ⟶ S),
      s'.base (IsLocalRing.closedPoint K') = y →
        ∀ 𝒲 : (pullback (pullback.snd c' σ) s').TwoAffineOpenCover,
          ((Module.finrank K' (𝒲.sectionsOf (fibreAt c' σ s') (fibreModule c' σ s' L')).H0 : ℤ) - Module.finrank K' (𝒲.sectionsOf (fibreAt c' σ s') (fibreModule c' σ s' L')).H1) = e₀} ∩
      {y : S | ∀ (K' : Type u) [Field K'] (s' : Spec (CommRingCat.of K') ⟶ S),
      s'.base (IsLocalRing.closedPoint K') = y →
        ∀ 𝒲 : (pullback (pullback.snd c' σ) s').TwoAffineOpenCover,
          ((Module.finrank K' (𝒲.sectionsOf (fibreAt c' σ s') (fibreModule c' σ s' (𝟙_ (pullback c' σ).Modules))).H0 : ℤ) - Module.finrank K' (𝒲.sectionsOf (fibreAt c' σ s') (fibreModule c' σ s' (𝟙_ (pullback c' σ).Modules))).H1) = e₀} = Set.univ := by
    rcases isClopen_iff.mp ((hcl e₀).inter (hcl1 e₀)) with h | h
    · exfalso
      have : s₀.base (IsLocalRing.closedPoint k₀) ∈ (∅ : Set S) := by
        rw [← h]
        exact ⟨he₀, hee ▸ he₀'⟩
      exact this
    · exact h

  have hmem : s.base (IsLocalRing.closedPoint K) ∈ (Set.univ : Set S) := trivial
  rw [← hZ] at hmem
  obtain ⟨hs1, hs2⟩ := hmem
  have hχ := eulerChar_eq_of_forall c' σ K s hx L' e₀ (hs1 K s rfl) 𝒱 _ (Iso.refl _)
  have hχ' := eulerChar_eq_of_forall c' σ K s hx (𝟙_ _) e₀ (hs2 K s rfl) 𝒱
    (SheafOfModules.unit (pullback c' (specMap k K)).ringCatSheaf) (Scheme.Modules.pullbackUnitIso _).symm
  exact (key K s hx).mpr (hχ.trans hχ'.symm)

end AlgebraicGeometry.ConstFam

open AlgebraicGeometry.ConstFam _root_.AlgebraicGeometry.Scheme.TwoAffineOpenCover in
theorem solution
    (k : Type u) [Field k] [IsAlgClosed k]
    {X C₁ C₂ : Scheme.{u}} (x : X ⟶ Spec (CommRingCat.of k)) [IsProper x] (hXred : IsReduced X)
    (c₁ : C₁ ⟶ Spec (CommRingCat.of k)) (c₂ : C₂ ⟶ Spec (CommRingCat.of k))
    [IsProper c₁] [SmoothOfRelativeDimension 1 c₁] [GeometricallyIntegral c₁]
    [IsProper c₂] [SmoothOfRelativeDimension 1 c₂] [GeometricallyIntegral c₂]
    (i₁ : SchemeHomOver c₁ x) (i₂ : SchemeHomOver c₂ x) [IsClosedImmersion i₁.1] [IsClosedImmersion i₂.1]
    (hjs : ∀ z : X, z ∈ Set.range i₁.1.base ∨ z ∈ Set.range i₂.1.base)
    (hcr : IsReduced (pullback i₁.1 i₂.1)) (s : ℕ) (hs : Nat.card ↥(pullback i₁.1 i₂.1) = s) (hs0 : 0 < s)
    (𝒱₁ : C₁.TwoAffineOpenCover) (𝒱₂ : C₂.TwoAffineOpenCover)

    {S : Scheme.{u}} (σ : S ⟶ Spec (CommRingCat.of k)) [LocallyOfFiniteType σ] [PreconnectedSpace ↥S]
    (L : (pullback x σ).Modules) (hL : Scheme.Modules.IsInvertible L)

    {k₀ : Type u} [Field k₀] [IsAlgClosed k₀] (s₀ : Spec (CommRingCat.of k₀) ⟶ S)
    (h₀ : IsAlgEquivZero (fibreAt x σ s₀) ((Scheme.Modules.pullback (pullback.fst (pullback.snd x σ) s₀)).obj L)) :

    ∀ (k₁ : Type u) [Field k₁] [IsAlgClosed k₁] (s₁ : Spec (CommRingCat.of k₁) ⟶ S),
      IsAlgEquivZero (fibreAt x σ s₁) ((Scheme.Modules.pullback (pullback.fst (pullback.snd x σ) s₁)).obj L) := by
  intro k₁ _ _ s₁
  obtain ⟨φ₁, hφ₁⟩ := Spec.map_surjective (s₁ ≫ σ)
  letI alg₁ : Algebra k k₁ := φ₁.hom.toAlgebra
  have hx₁ : s₁ ≫ σ = specMap k k₁ := hφ₁.symm
  have h₁ := component k x c₁ i₁ 𝒱₁ σ L hL s₀ h₀ k₁ s₁ hx₁
  have h₂ := component k x c₂ i₂ 𝒱₂ σ L hL s₀ h₀ k₁ s₁ hx₁

  have hL₁ : Scheme.Modules.IsInvertible
      ((Scheme.Modules.pullback (baseChangeSnd x (⟨s₁, hx₁⟩ : SchemeHomOver _ σ))).obj L) := hL.pullback _
  have e : ∀ {C'' : Scheme.{u}} {c'' : C'' ⟶ Spec (CommRingCat.of k)} (i : SchemeHomOver c'' x),
      Nonempty ((Scheme.Modules.pullback (baseChangeSnd c'' (⟨s₁, hx₁⟩ : SchemeHomOver _ σ))).obj
        ((Scheme.Modules.pullback (curveChange i.1 i.2 σ)).obj L) ≅
        (Scheme.Modules.pullback (curveChange i.1 i.2 (specMap k k₁))).obj
          ((Scheme.Modules.pullback (baseChangeSnd x (⟨s₁, hx₁⟩ : SchemeHomOver _ σ))).obj L)) :=
    fun i => ⟨pbComp _ _ _ ≪≫ pbCongr (curveChange_baseChangeSnd i.1 i.2 ⟨s₁, hx₁⟩).symm _ ≪≫ (pbComp _ _ _).symm⟩
  have h := isAlgEquivZero_of_isAlgEquivZero_pullback_curveChange_of_twoGluedSmoothCurves x hXred c₁ c₂ i₁ i₂ hjs hcr s hs hs0
    k₁ (specMap k k₁) _ hL₁ (h₁.of_iso (e i₁).some) (h₂.of_iso (e i₂).some)
  exact (isAlgEquivZero_fibre_iff x σ s₁ _ hx₁ L).mpr h

end S_AlgebraicGeometry_TwoGluedCurves_isAlgEquivZero_fibre_of_isAlgEquivZero_fibre_of_preconnectedSpace
end P2MW
export P2MW.S_AlgebraicGeometry_TwoGluedCurves_isAlgEquivZero_fibre_of_isAlgEquivZero_fibre_of_preconnectedSpace (solution)
