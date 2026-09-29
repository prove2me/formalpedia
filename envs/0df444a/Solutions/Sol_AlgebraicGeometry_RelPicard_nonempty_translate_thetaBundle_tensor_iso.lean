-- Prove2me | solution 1 for AlgebraicGeometry.RelPicard.nonempty_translate_thetaBundle_tensor_iso
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:03.589526+00:00
-- url     : https://prove2.me/submissions/17cfe1e9-143a-5978-8948-a88dc0f6e5fe

import Mathlib
import Definitions.Def_AlgebraicGeometry_NeronModelPropertyBundleCarrier
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import Definitions.Def_AlgebraicGeometry_RepresentsRelSubPic
import Definitions.Def_AlgebraicGeometry_RelSubPicPresheaf
import Definitions.Def_AlgebraicGeometry_RelPicardAlgEquivZeroCut
import Definitions.Def_AlgebraicGeometry_RelPicardAlgEquivZeroGroupCut
import Definitions.Def_AlgebraicGeometry_RelSubPicGroup
import Definitions.Def_JacJ1Iface
import Definitions.Def_AlgebraicGeometry_TwoAffineOpenCover
import Definitions.Def_AlgebraicGeometry_TwoChartCechSectionsOf
import Definitions.Def_AlgebraicGeometry_SmoothProperCurveFiniteMapData
import Definitions.Def_AlgebraicGeometry_SmoothProperCurveBase
import Definitions.Def_AlgebraicGeometry_RelSubPicBaseChange
import Definitions.Def_AlgebraicCurve_CurveModel
import Definitions.Def_AlgebraicCurve_AdelicIndex
import Definitions.Def_SheafOfModules_Monoidal
import Definitions.Def_AlgebraicGeometry_ModulesPullbackMonoidal
import Definitions.Def_AlgebraicGeometry_RelPicardThetaBundle
import Theorems.Thm_AlgebraicGeometry_RelPicard_nonempty_pullback_thetaBundle_iso
import Theorems.Thm_AlgebraicGeometry_RelPicard_RepresentsRelSubPic_nonempty_poincare_pullbackAlong_mul_iso
import Theorems.Thm_AlgebraicGeometry_RelPicard_subsingleton_H1_and_finrank_H0_fibre_tensor_sectionTwist_of_fibrewiseAlgEquivZero
import Theorems.Thm_AlgebraicGeometry_SmoothProperCurve_forall_geometricFibre_riemannRoch_imp_eq_of_isAlgClosed
import Theorems.Thm_AlgebraicGeometry_RelPicard_nonempty_thetaBundle_tensor_pullbackAlong_tensor_iso_of_fibrewiseAlgEquivZero
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_RelPicard_nonempty_translate_thetaBundle_tensor_iso
p2m_attr_erase "instance" "AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instNeg AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instSMulInt AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instAddCommGroup AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instAdd AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instSub AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instModuleCarrierObjOppositeOpensCarrierCarrierCommRingCatPresheafOpOpensTop AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instSMulCarrierObjOppositeOpensCarrierCarrierCommRingCatPresheafOpOpensTop AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instSMulNat AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instZero AlgebraicGeometry.RelEffCartierDiv.isIso_subschemeIota_snd_of_degree_one AlgebraicGeometry.isIso_ker_graphOver_subschemeIota_snd AlgebraicGeometry.isClosedImmersion_graphOver AlgebraicGeometry.OModulePresheaf.isScalarTower AlgebraicGeometry.Scheme.OrderedAffineCover.instLinearOrder AlgebraicGeometry.OModulePresheaf.module AlgebraicGeometry.Scheme.OrderedAffineCover.instFintype AlgebraicGeometry.Scheme.OrderedAffineCover.instFintypeIdx AlgebraicGeometry.OModulePresheaf.addCommGroup AlgebraicGeometry.Scheme.OrderedAffineCover.instDecidableEqIdx AlgebraicGeometry.OModulePresheaf.moduleSections AlgebraicGeometry.OModulePresheaf.instSubsingletonObjZero AlgebraicGeometry.OModulePresheaf.Leray.relAltC_scalarTower AlgebraicGeometry.OModulePresheaf.Leray.ker_relAltd_modΓ AlgebraicGeometry.OModulePresheaf.Leray.relAltC_modΓ AlgebraicGeometry.OModulePresheaf.Leray.biC_abGrp AlgebraicGeometry.OModulePresheaf.Leray.relAltH_modΓ AlgebraicGeometry.OModulePresheaf.Leray.ker_relAltd_smul AlgebraicGeometry.OModulePresheaf.Leray.relAltH_scalarTower AlgebraicGeometry.OModulePresheaf.Leray.relAltH_smul AlgebraicGeometry.OModulePresheaf.Leray.biC_module AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instDecidableEqIdx AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instFintype AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instLinearOrder AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instFintypeIdx DoubleComplex.instModuleE₂I DoubleComplex.Bounded.modR DoubleComplex.instModuleE₂II DoubleComplex.instAddCommGroupE₂II DoubleComplex.Bounded.abGrp DoubleComplex.instAddCommGroupE₂I"
p2m_attr_erase "instance" "AlgebraicGeometry.ChowDatum.hι_closed AlgebraicGeometry.ChowDatumProj.hιN_closed AlgebraicGeometry.ChowDatumProj.hp_proper AlgebraicGeometry.ChowDatum.hp_isoU AlgebraicGeometry.ChowDatum.hp_proper AlgebraicGeometry.ProjSpace.algebraAway AlgebraicGeometry.ProjSpace.instIsProperProdOverπ AlgebraicGeometry.ChowDatumProj.hp_isoU AlgebraicGeometry.ProjSpace.isProper_π AlgebraicGeometry.ProjSpace.finiteType_mvPolynomial ProjSpaceCech.GradedModule.H.module ProjSpaceCech.GradedModule.H.addCommGroup ProjSpaceCech.GradedModule.sec.instAdd ProjSpaceCech.GradedModule.sec.instNeg ProjSpaceCech.GradedModule.acg ProjSpaceCech.GradedModule.Frac.setoid ProjSpaceCech.GradedModule.modR ProjSpaceCech.GradedModule.sec.instModule ProjSpaceCech.GradedModule.sec.instAddCommGroup ProjSpaceCech.GradedModule.sec.instZero ProjSpaceCech.GradedModule.Presentation.fJ ProjSpaceCech.GradedModule.sec.instSMul ProjSpaceCech.Twist.H.module ProjSpaceCech.Idx.instFintype ProjSpaceCech.Twist.H.addCommGroup ProjSpaceCech.Idx.instDecidableEq ProjSpaceCech.Twist.Mon.instDecidableEq ProjSpaceCech.Twist.cochain.instAddCommGroup ProjSpaceCech.Twist.cochain.instModule SheafOfModules.isIso_ihomModelToIhom AlgebraicGeometry.RelEffCartierDiv.subsingleton_of_degree_zero AlgebraicCurve.IsCurveOver.instNontrivialKaehler AlgebraicCurve.IsCurveOver.instFreeKaehler AlgebraicCurve.IsCurveOver.toHasPrincipalDivisors AlgebraicCurve.IsCurveOver.instFiniteResidue AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.instFundamentalIdentityOfSumRamificationInertia AlgebraicCurve.Place.instIsScalarTowerResidueFieldRestrictPushforward AlgebraicCurve.Place.instAlgebraResidueFieldRestrictPushforward"
p2m_attr_erase "instance" "AlgebraicCurve.Place.instIsLocalHomRestrictInclusion AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.SemilinearAut.instDistribMulActionSubtypeProdRingAutMemSubgroupPic0 AlgebraicCurve.SemilinearAut.instDistribMulActionSubtypeProdRingAutMemSubgroupDivisor AlgebraicCurve.Pic0.instModuleZModTorsion AlgebraicCurve.SemilinearAut.instSMulSubtypeProdRingAutMemSubgroupPlace AlgebraicCurve.SemilinearAut.instDistribMulActionTorsion AlgebraicCurve.SemilinearAut.instSMulSubtypeProdRingAutMemSubgroupPic0 AlgebraicCurve.SemilinearAut.instSMulTorsion AlgebraicCurve.SemilinearAut.instMulActionSubtypeProdRingAutMemSubgroupPlace AlgebraicCurve.SemilinearAut.instSMulCommClassZModTorsion AlgebraicCurve.SemilinearAut.instMulSemiringActionSubtypeProdRingAutMemSubgroup instDecEqAlgebraicClosureRat WeierstrassCurve.Affine.Point.instDistribMulActionAlgEquiv WeierstrassCurve.Affine.Point.instModuleZModTorsionBy WeierstrassCurve.Affine.Point.instSMulTorsionBy WeierstrassCurve.Affine.Point.instDistribMulActionTorsionBy WeierstrassCurve.Affine.Point.instSMulAlgEquiv WeierstrassCurve.Affine.Point.instSMulCommClassAlgEquivZModTorsionBy AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions AlgebraicCurve.instHasLocalResidue_of_hasCanonicalLocalResidueK AlgebraicCurve.instHasCanonicalLocalResidueK_of_hasCanonicalLocalResidueKStar AlgebraicCurve.Place.kw_ffgc_finiteDimensional_adicCompletion instAlgebraSubtypeMemValuationSubring_definitions AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersIntegersCompletion ModularCurve.KwF4gRRTate.instAlgebraKAdicCompletionIntegers AlgebraicCurve.Place.kw_ffgc_continuousSMul_adicCompletionComap AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersCompletionCompletion IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions AlgebraicCurve.instHasCanonicalLocalResidueK AlgebraicCurve.Place.instAlgebra_restrictResidueField"
p2m_attr_erase "instance" "AlgebraicCurve.Place.instIsScalarTower_restrictResidueField AlgebraicCurve.instHasLocalResidue AlgebraicCurve.HasSeparableResidue.of_perfectField_of_isCurveOver AlgebraicCurve.HasSeparableResidue.of_perfectField AlgebraicCurve.Place.instIsLocalHom_restrictSubringHom AlgebraicCurve.instHasCanonicalLocalResidueKStar ModularCurve.KwNo6Pin.isLocalRing_completion"
p2m_attr_erase "simp" "AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.sub_app AlgebraicGeometry.Scheme.IdealSheafData.sres_sresTop AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.add_app AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.mk.sizeOf_spec AlgebraicGeometry.Scheme.IdealSheafData.coe_resLE AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.smul_app AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.coe_ofLE_app AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.ideal_range AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.zero_app AlgebraicGeometry.Scheme.IdealSheafData.sres_sres AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.comp_app AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.neg_app AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.id_app AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.coe_mulRight_app AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.nsmul_app AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.mk.injEq AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.zsmul_app AlgebraicGeometry.tilde.functorCompPullbackSpecIso_app TwoChartCech.Mumford.dK_apply TwoChartCech.Mumford.ι0_apply TwoChartCech.Mumford.ι1_apply TwoChartCech.KerCoprod.dK_apply TwoChartCech.KerCoprod.ι1_apply TwoChartCech.KerCoprod.ι0_apply PresheafOfModules.pushforwardCongr_inv_app_app_apply PresheafOfModules.pushforwardNatTrans_app_app_apply PresheafOfModules.pushforwardCongr_hom_app_app_apply AlgebraicGeometry.graphOver_fst_assoc AlgebraicGeometry.RelEffCartierDiv.toPoint_comp AlgebraicGeometry.RelEffCartierDiv.toPoint_comp_assoc AlgebraicGeometry.graphOver_fst AlgebraicGeometry.RelEffCartierDiv.ofPoint_I AlgebraicGeometry.graphOver_snd AlgebraicGeometry.graphOver_snd_assoc AlgebraicGeometry.Scheme.OrderedAffineCover.mk.injEq AlgebraicGeometry.OModulePresheaf.mk.sizeOf_spec AlgebraicGeometry.Scheme.OrderedAffineCover.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.mk.injEq AlgebraicGeometry.OModulePresheaf.prod_obj AlgebraicGeometry.OModulePresheaf.restrOpen_obj"
p2m_attr_erase "simp" "AlgebraicGeometry.OModulePresheaf.DevissageStep.mk.injEq AlgebraicGeometry.OModulePresheaf.pushforward_obj AlgebraicGeometry.OModulePresheaf.im_obj AlgebraicGeometry.OModulePresheaf.pow_obj AlgebraicGeometry.OModulePresheaf.fstHom_app AlgebraicGeometry.OModulePresheaf.ker_obj AlgebraicGeometry.OModulePresheaf.coker_obj AlgebraicGeometry.OModulePresheaf.DevissageStep.mk.sizeOf_spec AlgebraicGeometry.Scheme.OrderedAffineCover.preimage_U AlgebraicGeometry.OModulePresheaf.sndHom_app AlgebraicGeometry.OModulePresheaf.Hom.mk.injEq AlgebraicGeometry.OModulePresheaf.Hom.id_app AlgebraicGeometry.OModulePresheaf.AffHom.appSections_apply AlgebraicGeometry.OModulePresheaf.AffHom.comp_app AlgebraicGeometry.OModulePresheaf.AffSES.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.AffHom.kerMap_coe AlgebraicGeometry.OModulePresheaf.AffHom.id_app AlgebraicGeometry.OModulePresheaf.Hom.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.Hom.toAffHom_app AlgebraicGeometry.OModulePresheaf.SES.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.AffHom.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.Hom.comp_app AlgebraicGeometry.OModulePresheaf.SES.mk.injEq AlgebraicGeometry.OModulePresheaf.AffHom.mk.injEq AlgebraicGeometry.OModulePresheaf.Hom.appSections_apply AlgebraicGeometry.OModulePresheaf.AffSES.mk.injEq AlgebraicGeometry.OModulePresheaf.Leray.restrictToPreimage_U AlgebraicGeometry.Scheme.OrderedAffineCover.toCoverOf_U AlgebraicGeometry.Scheme.OrderedAffineCoverOf.mk.sizeOf_spec AlgebraicGeometry.Scheme.OrderedAffineCoverOf.mk.injEq AlgebraicGeometry.Scheme.OrderedAffineCover.restrict_U DoubleComplex.Bounded.mk.injEq DoubleComplex.Bounded.mk.sizeOf_spec DoubleComplex.Convergence.mk.injEq DoubleComplex.Convergence.mk.sizeOf_spec DoubleComplex.SubQuot.mk.sizeOf_spec DoubleComplex.SubQuot.mk.injEq AlgebraicGeometry.ChowDatumProj.mk.sizeOf_spec AlgebraicGeometry.ChowDatum.mk.sizeOf_spec AlgebraicGeometry.ChowDatumProj.mk.injEq"
p2m_attr_erase "simp" "AlgebraicGeometry.ChowDatum.mk.injEq ProjSpaceCech.GradedModule.mk.injEq ProjSpaceCech.GradedModule.mk.sizeOf_spec ProjSpaceCech.GradedModule.Frac.mk.sizeOf_spec ProjSpaceCech.GradedModule.Presentation.mk.injEq ProjSpaceCech.GradedModule.Frac.mk.injEq ProjSpaceCech.GradedModule.Presentation.mk.sizeOf_spec ProjSpaceCech.GradedModule.Hom.shift_toLinearMap ProjSpaceCech.GradedModule.Hom.mk.sizeOf_spec ProjSpaceCech.GradedModule.Hom.mk.injEq AlgebraicGeometry.Scheme.Modules.tensorPow_zero AlgebraicGeometry.Scheme.Modules.tensorPow_succ AlgebraicGeometry.Scheme.Modules.tensorSections_zero_right AlgebraicGeometry.Scheme.Modules.map_unitSection AlgebraicGeometry.Scheme.Modules.tensorSectionsBilin_apply AlgebraicGeometry.Scheme.Modules.tensorPowSection_zero AlgebraicGeometry.Scheme.Modules.tensorSections_zero_left AlgebraicGeometry.Scheme.Modules.pullbackLocalSection_neg AlgebraicGeometry.Scheme.Modules.pullbackLocalSection_zero AlgebraicGeometry.Scheme.Modules.pullbackLocalSection_sub AlgebraicGeometry.Scheme.Modules.pullbackLocalSection_add PresheafOfModules.InternalHom.IsSheafAux.appAt_toPresheafHom SheafOfModules.ihomSectionsEquivFamily_unit AlgebraicGeometry.Scheme.Modules.restrictHomEquivFamily_apply SheafOfModules.ihomEval_unit_app AlgebraicGeometry.Scheme.Modules.ihomEval_zero_right AlgebraicGeometry.Scheme.Modules.ihomEval_zero_left AlgebraicGeometry.Scheme.Modules.homOfFamily_app_apply SheafOfModules.unit_ihomSectionsEquivFamily AlgebraicGeometry.Scheme.Modules.familyOfHom_app AlgebraicGeometry.Scheme.Modules.restrictUnitIso_hom_app_apply AlgebraicGeometry.Scheme.Modules.restrictUnitIso_inv_app_apply AlgebraicGeometry.Scheme.Modules.restrictHomOfFamily_app_apply AlgebraicGeometry.Scheme.Modules.restrictHomEquivFamily_symm_apply AlgebraicGeometry.prodKerGraph_one AlgebraicGeometry.fibrePowOver.proj_comp AlgebraicGeometry.prodKerGraph_zero AlgebraicGeometry.RelEffCartierDiv.empty_I AlgebraicGeometry.fibrePowOver.proj_comp_assoc AlgebraicCurve.SymmetricPowerPackage.mk.sizeOf_spec"
p2m_attr_erase "simp" "AlgebraicCurve.SymmetricPowerPackage.mk.injEq AlgebraicCurve.coe_cechH0Equiv_apply AlgebraicCurve.cechH1ToH1_mk AlgebraicCurve.lSpaceOn_univ AlgebraicCurve.lSpaceOn_empty AlgebraicCurve.Place.congrEquiv_symm_apply AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply AlgebraicCurve.RationalFunctionField.deg_placeOfPoint AlgebraicCurve.Divisor.mapRestrict_single AlgebraicCurve.Divisor.pushforward_single AlgebraicCurve.Place.coe_restrictInclusion AlgebraicCurve.Place.mem_fiber AlgebraicCurve.Place.restrict_toValuationSubring AlgebraicCurve.Divisor.degree_pushforward AlgebraicCurve.Place.restrictResidueMap_residue AlgebraicCurve.Pic0.coe_pushforwardDegZeroHom AlgebraicCurve.Pic0.coe_pullbackDegZeroHom AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal AlgebraicCurve.IsFrobeniusEndo.frobNormRingHom_apply ModularCurve.frobeniusPushforwardGeomLevelPic0_mk ModularCurve.coe_frobeniusGeomLevelEquiv_apply ModularCurve.coe_frobeniusPushforwardGeomLevelDegZero ModularCurve.heckeFibreGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusGeomLevel_apply_coe ModularCurve.frobeniusPullbackGeomLevelPic0OfIsCurveOver_mk ModularCurve.coe_heckeFibreGeomLevelDegZero ModularCurve.coe_frobeniusPullbackGeomLevelDegZero ModularCurve.frobeniusPullbackGeomLevelPic0_mk ModularCurve.frobeniusPullbackGeomLevel_single ModularCurve.heckeFibreGeomLevelPic0_mk ModularCurve.frobeniusPushforwardGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusPushforwardGeomLevel_single ModularCurve.qExpandAlgC_apply"
p2m_attr_erase "simp" "AlgebraicCurve.Divisor.degree_pushforwardAlong AlgebraicCurve.Pic0.coe_degZeroCorrespondence AlgebraicCurve.Place.mem_fiberAlong AlgebraicCurve.SemilinearAut.toRingAut_inv AlgebraicCurve.SemilinearAut.smul_def AlgebraicCurve.SemilinearAut.smul_single AlgebraicCurve.SemilinearAut.smul_toValuationSubring AlgebraicCurve.SemilinearAut.baseAut_inv AlgebraicCurve.SemilinearAut.baseAut_ofAlgAut AlgebraicCurve.SemilinearAut.toRingAut_ofAlgAut AlgebraicCurve.SemilinearAut.torsionRep_apply AlgebraicCurve.SemilinearAut.toRingAut_one AlgebraicCurve.SemilinearAut.deg_smul AlgebraicCurve.SemilinearAut.degree_smul AlgebraicCurve.SemilinearAut.coe_degZeroSMulHom AlgebraicCurve.SemilinearAut.baseAut_mul AlgebraicCurve.SemilinearAut.coe_smulValuationSubringEquiv_apply AlgebraicCurve.SemilinearAut.baseAut_one AlgebraicCurve.SemilinearAut.ofAlgAut_smul AlgebraicCurve.SemilinearAut.coe_torsion_smul AlgebraicCurve.SemilinearAut.toRingAut_mul AlgebraicCurve.coe_frobeniusPushforwardDegZero AlgebraicCurve.IsFrobeniusEndo.coe_frobeniusPullbackDegZero ModularCurve.jqNModC_one ModularCurve.qExpand_coeff_mul ModularCurve.qExpandₐ_apply ModularCurve.jqN_one ModularCurve.qExpand_single ModularCurve.dedekindPsi_one ModularCurve.ModularPolynomialData.mk.sizeOf_spec ModularCurve.evalAtJ_X ModularCurve.ModularPolynomialData.mk.injEq ModularCurve.constantCoeff_jNum ModularCurve.constantCoeff_eisenstein4 ModularCurve.qExpand_C ModularCurve.coeff_jq_neg_one ModularCurve.constantCoeff_jNumQ ModularCurve.reduceModBivar_C_X ModularCurve.laurentMap_coeff ModularCurve.reduceModBivar_X"
p2m_attr_erase "simp" "ModularCurve.laurentMap_single ModularCurve.evalAtJInt_X ModularCurve.evalAtJMod_X ModularCurve.jqNMod_one ModularCurve.aeval_heckeGen ModularCurve.coe_mTorsionGaloisRep_apply ModularCurve.eisensteinSystem_of_dvd ModularCurve.eisensteinSystem_of_not_dvd FreyPackage.mk.sizeOf_spec FreyPackage.mk.injEq WeierstrassCurve.Affine.Point.galoisRepModuleEnd_apply AlgebraicCurve.RationalFunctionField.placeInfty_toValuationSubring AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none AlgebraicCurve.Divisor.evalFun_zero AlgebraicCurve.Place.evalAt_one AlgebraicCurve.Place.differentialCoeff_zero AlgebraicCurve.Place.differentialCoeff_dCoord AlgebraicCurve.TranscendenceTower.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.injEq AlgebraicCurve.TranscendenceTower.mk.injEq AlgebraicCurve.PoleDivisorPackage.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.sizeOf_spec AlgebraicCurve.PoleDivisorPackage.mk.injEq AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.sizeOf_spec AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.injEq AlgebraicCurve.adeleSingle_coe AlgebraicCurve.kaehlerResidueTermKFam_apply AlgebraicCurve.Place.LocalResidueData.mk.injEq AlgebraicCurve.Place.LocalResidueData.mk.sizeOf_spec AlgebraicCurve.Place.kw_ffgc_adicCompletionComapIntegers_coe AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.sizeOf_spec AlgebraicCurve.Place.mem_simplePoleSubmodule AlgebraicCurve.Place.coe_uniformizerSubring ModularCurve.Lg37.Lg37CompletionSection.mk.injEq AlgebraicCurve.Place.CoefficientFieldSection.mk.injEq AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.injEq ModularCurve.Lg37.Lg37CompletionSection.mk.sizeOf_spec"
p2m_attr_erase "simp" "AlgebraicCurve.Place.CoefficientFieldSection.mk.sizeOf_spec AlgebraicCurve.Place.poleSubmodule_one AlgebraicCurve.Place.mem_poleSubmodule AlgebraicGeometry.RelPicard.fst_toProdSpec AlgebraicGeometry.RelPicard.toProdSpec_fst_assoc AlgebraicGeometry.RelPicard.pointsSubBasepointModule_cons AlgebraicGeometry.RelPicard.pointsSubBasepointModule_nil AlgebraicGeometry.RelPicard.fst_toProdSpec_assoc AlgebraicGeometry.RelPicard.toProdSpec_fst AlgebraicGeometry.Scheme.Modules.toUnitSection_ofUnitSection AlgebraicGeometry.Scheme.Modules.pullbackSection_def AlgebraicGeometry.Scheme.Modules.ofUnitSection_toUnitSection exteriorPower.mulₗ_apply_coe AlgebraicGeometry.RelPicard.rigSection_snd AlgebraicGeometry.RelPicard.RigidifiedLineBundle.ofInvertible_L AlgebraicGeometry.RelPicard.rigSection_snd_assoc"

set_option autoImplicit false

universe u

p2m_open "CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory AlgebraicGeometry P2MW.S_AlgebraicGeometry_RelPicard_nonempty_translate_thetaBundle_tensor_iso.AlgebraicGeometry AlgebraicGeometry.RelPicard P2MW.S_AlgebraicGeometry_RelPicard_nonempty_translate_thetaBundle_tensor_iso.AlgebraicGeometry.RelPicard NeronModelInfra AlgebraicGeometry.SmoothProperCurve GoodReductionJacobian AlgebraicCurve~genus"

open scoped CategoryTheory.MonObj

namespace AlgebraicGeometry
p2m_export "AlgebraicGeometry" "SmoothOfRelativeDimension IsProper Scheme.Modules.pullback GeometricallyIntegral LocallyOfFiniteType Spec Scheme Smooth Scheme.Modules.pullbackCongr Scheme.Modules.pullbackId Scheme.Modules GeometricallyConnected Scheme.Modules.pullbackComp RelPicard.RigidifiedLineBundle Scheme.Modules.pullbackTensorObjIso SmoothProperCurve.FiniteMapData RelPicard.nonempty_pullback_thetaBundle_iso RelPicard.subsingleton_H1_and_finrank_H0_fibre_tensor_sectionTwist_of_fibrewiseAlgEquivZero SmoothProperCurve.forall_geometricFibre_riemannRoch_imp_eq_of_isAlgClosed RelPicard.nonempty_thetaBundle_tensor_pullbackAlong_tensor_iso_of_fibrewiseAlgEquivZero"
namespace RelPicard
p2m_export "AlgebraicGeometry.RelPicard" "baseChangeSnd postComp baseChangeSnd_id baseChangeSnd_comp RigidifiedLineBundle RepresentsRelSubPic fibreAt FibrewiseAlgEquivZero algEquivZeroCut algEquivZeroGroupCut sectionTwist thetaBundle fibreModule nonempty_pullback_thetaBundle_iso RepresentsRelSubPic.nonempty_poincare_pullbackAlong_mul_iso subsingleton_H1_and_finrank_H0_fibre_tensor_sectionTwist_of_fibrewiseAlgEquivZero nonempty_thetaBundle_tensor_pullbackAlong_tensor_iso_of_fibrewiseAlgEquivZero"
namespace RigidifiedLineBundle
p2m_export "AlgebraicGeometry.RelPicard.RigidifiedLineBundle" "pullbackAlong L mk tensor"
p2m_open "AlgebraicGeometry.RelPicard.RigidifiedLineBundle AlgebraicGeometry.RelPicard AlgebraicGeometry"

variable {R : Type u} [CommRing R] {C : Scheme.{u}} {c : C ⟶ Spec (CommRingCat.of R)}
  {ε : SchemeHomOver (𝟙 (Spec (CommRingCat.of R))) c}

private noncomputable def _root_.AlgebraicGeometry.RelPicard.RigidifiedLineBundle.sqCongrL {T T' : Scheme.{u}} {t : T ⟶ Spec (CommRingCat.of R)} {t' : T' ⟶ Spec (CommRingCat.of R)}
    (M : RigidifiedLineBundle c ε t) (ψ ψ' : SchemeHomOver t' t) (h : ψ.1 = ψ'.1) :
    (M.pullbackAlong ψ).L ≅ (M.pullbackAlong ψ').L :=
  (Scheme.Modules.pullbackCongr (show baseChangeSnd c ψ = baseChangeSnd c ψ' by rw [Subtype.ext h])).app M.L

p2m_export "AlgebraicGeometry.RelPicard.RigidifiedLineBundle" "sqCongrL"

private noncomputable def _root_.AlgebraicGeometry.RelPicard.RigidifiedLineBundle.sqCompL {X X' T' : Scheme.{u}} {x : X ⟶ Spec (CommRingCat.of R)} {x' : X' ⟶ Spec (CommRingCat.of R)}
    {t' : T' ⟶ Spec (CommRingCat.of R)} (M : RigidifiedLineBundle c ε x') (φ : SchemeHomOver x x')
    (ψ : SchemeHomOver t' x) :
    ((M.pullbackAlong φ).pullbackAlong ψ).L ≅ (M.pullbackAlong (postComp φ ψ)).L :=
  (Scheme.Modules.pullbackComp (baseChangeSnd c ψ) (baseChangeSnd c φ)).app M.L ≪≫
    (Scheme.Modules.pullbackCongr (baseChangeSnd_comp c φ ψ)).app M.L

p2m_export "AlgebraicGeometry.RelPicard.RigidifiedLineBundle" "sqCompL"

private noncomputable def _root_.AlgebraicGeometry.RelPicard.RigidifiedLineBundle.sqIdL {T : Scheme.{u}} {t : T ⟶ Spec (CommRingCat.of R)} (M : RigidifiedLineBundle c ε t)
    (ψ : SchemeHomOver t t) (h : ψ.1 = 𝟙 T) : (M.pullbackAlong ψ).L ≅ M.L :=
  M.sqCongrL ψ ⟨𝟙 T, Category.id_comp t⟩ h ≪≫
    (Scheme.Modules.pullbackCongr (baseChangeSnd_id c t)).app M.L ≪≫ (Scheme.Modules.pullbackId _).app M.L

p2m_export "AlgebraicGeometry.RelPicard.RigidifiedLineBundle" "sqIdL"

noncomputable def sqTensorL {T T' : Scheme.{u}} {t : T ⟶ Spec (CommRingCat.of R)} {t' : T' ⟶ Spec (CommRingCat.of R)}
    (ψ : SchemeHomOver t' t) (L M : RigidifiedLineBundle c ε t) :
    ((L.tensor M).pullbackAlong ψ).L ≅ ((L.pullbackAlong ψ).tensor (M.pullbackAlong ψ)).L :=
  Scheme.Modules.pullbackTensorObjIso _ _ _

end AlgebraicGeometry.RelPicard.RigidifiedLineBundle

theorem solution
    (k : Type u) [Field k] [IsAlgClosed k] {C : Scheme.{u}} (c : C ⟶ Spec (CommRingCat.of k))
    [IsProper c] [SmoothOfRelativeDimension 1 c] [GeometricallyIntegral c]
    (ε : SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) c)
    (h𝔉 : ∀ m₀ : ℕ, ∃ 𝔉 : SmoothProperCurve.FiniteMapData c ε, m₀ ≤ 𝔉.m)
    (J : RelativePic0Designation k c) (h : RepresentsRelSubPic c ε (algEquivZeroCut c ε) J)
    (hsm : Smooth J.toBase) (hpr : IsProper J.toBase) (hgc : GeometricallyConnected J.toBase)
    (g : ℕ)
    (hg : ∀ (L : Type u) [Field L] [Algebra k L] (M : CurveModel k L) (e : M.C ≅ C)
      (_ : e.hom ≫ c = M.toBase) (Kc : Divisor k L) (g' : ℕ),
      (∀ D : Divisor k L, (ell D : ℤ) - ell (Kc - D) = Divisor.degree D + 1 - g') → g' = g)
    (r : ℕ) (hr : 2 * g ≤ r)
    (x y : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ Over.mk J.toBase) :
    letI := (show RepresentsRelSubPic c ε (algEquivZeroGroupCut c ε).toSubPicCondition J from h).grpObj
    Nonempty (
      (Scheme.Modules.pullback
          (𝟙 (Over.mk J.toBase) * (CartesianMonoidalCategory.toUnit (Over.mk J.toBase) ≫ x)).left).obj
        (thetaBundle c ε J.toBase h.poincare r (r + 1 - g)) ⊗
      (Scheme.Modules.pullback
          (𝟙 (Over.mk J.toBase) * (CartesianMonoidalCategory.toUnit (Over.mk J.toBase) ≫ y)).left).obj
        (thetaBundle c ε J.toBase h.poincare r (r + 1 - g)) ≅
      (Scheme.Modules.pullback
          (𝟙 (Over.mk J.toBase) * (CartesianMonoidalCategory.toUnit (Over.mk J.toBase) ≫ (x * y))).left).obj
        (thetaBundle c ε J.toBase h.poincare r (r + 1 - g)) ⊗
      thetaBundle c ε J.toBase h.poincare r (r + 1 - g)) := by

  let h' : RepresentsRelSubPic c ε (algEquivZeroGroupCut c ε).toSubPicCondition J := h
  letI := h'.grpObj
  haveI : IsProper J.toBase := hpr
  haveI : LocallyOfFiniteType J.toBase := inferInstance

  let S := Spec (CommRingCat.of k)
  let JB : Over S := Over.mk J.toBase
  let P : RigidifiedLineBundle c ε J.toBase := h.poincare
  let tJ : SchemeHomOver J.toBase (𝟙 S) := ⟨J.toBase, Category.comp_id _⟩

  let T : (Over.mk (𝟙 S) ⟶ JB) → (JB ⟶ JB) := fun a => 𝟙 JB * (CartesianMonoidalCategory.toUnit JB ≫ a)
  let ov : (JB ⟶ JB) → SchemeHomOver J.toBase J.toBase := fun f => ⟨f.left, Over.w f⟩
  let N : (Over.mk (𝟙 S) ⟶ JB) → RigidifiedLineBundle c ε (𝟙 S) := fun a => P.pullbackAlong ⟨a.left, Over.w a⟩
  have htu : (CartesianMonoidalCategory.toUnit JB).left = J.toBase := by
    first
      | simp [JB]
      | simpa [JB] using Over.w (CartesianMonoidalCategory.toUnit JB)
      | (have w := Over.w (CartesianMonoidalCategory.toUnit JB)
         simp only [JB, Over.mk_left, Over.mk_hom] at w ⊢
         simpa using w)

  obtain ⟨𝔉, -⟩ := h𝔉 0
  have hgeo := SmoothProperCurve.forall_geometricFibre_riemannRoch_imp_eq_of_isAlgClosed k c ε 𝔉 g hg
  have hfib : ∀ (M : RigidifiedLineBundle c ε J.toBase), FibrewiseAlgEquivZero M →
      ∀ (k' : Type u) [Field k'] (s : Spec (CommRingCat.of k') ⟶ J.P)
        (𝒲 : (pullback (pullback.snd c J.toBase) s).TwoAffineOpenCover),
        Subsingleton (𝒲.sectionsOf (fibreAt c J.toBase s) (fibreModule c J.toBase s (M.L ⊗ sectionTwist c ε J.toBase r))).H1 ∧
          Module.finrank k' (𝒲.sectionsOf (fibreAt c J.toBase s)
            (fibreModule c J.toBase s (M.L ⊗ sectionTwist c ε J.toBase r))).H0 = r + 1 - g :=
    fun M hM => RelPicard.subsingleton_H1_and_finrank_H0_fibre_tensor_sectionTwist_of_fibrewiseAlgEquivZero
      k c ε g hgeo M hM r (by omega)
  have hP : FibrewiseAlgEquivZero P := h.poincare_mem

  have jj : ∀ a : Over.mk (𝟙 S) ⟶ JB, ((N a).pullbackAlong tJ).L ≅
      (h'.poincare.pullbackAlong (ov (CartesianMonoidalCategory.toUnit JB ≫ a))).L := fun a =>
    P.sqCompL ⟨a.left, Over.w a⟩ tJ ≪≫ P.sqCongrL _ _
      (show J.toBase ≫ a.left = (CartesianMonoidalCategory.toUnit JB ≫ a).left from (congrArg (· ≫ a.left) htu).symm)

  have e : ∀ a : Over.mk (𝟙 S) ⟶ JB, (P.tensor ((N a).pullbackAlong tJ)).L ≅ (P.pullbackAlong (ov (T a))).L :=
    fun a => ((P.sqIdL (ov (𝟙 JB)) rfl).symm ⊗ᵢ jj a) ≪≫
      (RepresentsRelSubPic.nonempty_poincare_pullbackAlong_mul_iso h' (𝟙 JB)
        (CartesianMonoidalCategory.toUnit JB ≫ a)).some.symm

  have Φ : ∀ a : Over.mk (𝟙 S) ⟶ JB,
      (Scheme.Modules.pullback (T a).left).obj (thetaBundle c ε J.toBase P r (r + 1 - g)) ≅
        thetaBundle c ε J.toBase (P.tensor ((N a).pullbackAlong tJ)) r (r + 1 - g) := fun a =>
    (RelPicard.nonempty_pullback_thetaBundle_iso k c ε h𝔉 P r (r + 1 - g) (hfib P hP) (ov (T a))
      (P.tensor ((N a).pullbackAlong tJ)) (e a)).some

  have hmul : CartesianMonoidalCategory.toUnit JB ≫ (x * y) =
      (CartesianMonoidalCategory.toUnit JB ≫ x) * (CartesianMonoidalCategory.toUnit JB ≫ y) :=
    MonObj.comp_mul _ _ _
  have exy : (P.tensor (((N x).tensor (N y)).pullbackAlong tJ)).L ≅ (P.pullbackAlong (ov (T (x * y)))).L :=
    ((P.sqIdL (ov (𝟙 JB)) rfl).symm ⊗ᵢ
      (RigidifiedLineBundle.sqTensorL tJ (N x) (N y) ≪≫ (jj x ⊗ᵢ jj y) ≪≫
        (RepresentsRelSubPic.nonempty_poincare_pullbackAlong_mul_iso h'
          (CartesianMonoidalCategory.toUnit JB ≫ x) (CartesianMonoidalCategory.toUnit JB ≫ y)).some.symm ≪≫
        h'.poincare.sqCongrL _ _ (congrArg (fun f : JB ⟶ JB => f.left) hmul).symm)) ≪≫
      (RepresentsRelSubPic.nonempty_poincare_pullbackAlong_mul_iso h' (𝟙 JB)
        (CartesianMonoidalCategory.toUnit JB ≫ (x * y))).some.symm
  have Φxy : (Scheme.Modules.pullback (T (x * y)).left).obj (thetaBundle c ε J.toBase P r (r + 1 - g)) ≅
      thetaBundle c ε J.toBase (P.tensor (((N x).tensor (N y)).pullbackAlong tJ)) r (r + 1 - g) :=
    (RelPicard.nonempty_pullback_thetaBundle_iso k c ε h𝔉 P r (r + 1 - g) (hfib P hP) (ov (T (x * y)))
      (P.tensor (((N x).tensor (N y)).pullbackAlong tJ)) exy).some

  obtain ⟨lin⟩ := RelPicard.nonempty_thetaBundle_tensor_pullbackAlong_tensor_iso_of_fibrewiseAlgEquivZero k c ε h𝔉 g
    hgeo P hP (N x) (N y) (hP.pullback _) (hP.pullback _) r (by omega)
  exact ⟨(Φ x ⊗ᵢ Φ y) ≪≫ lin ≪≫ (Φxy.symm ⊗ᵢ Iso.refl _)⟩

end S_AlgebraicGeometry_RelPicard_nonempty_translate_thetaBundle_tensor_iso
end P2MW
export P2MW.S_AlgebraicGeometry_RelPicard_nonempty_translate_thetaBundle_tensor_iso (solution)
