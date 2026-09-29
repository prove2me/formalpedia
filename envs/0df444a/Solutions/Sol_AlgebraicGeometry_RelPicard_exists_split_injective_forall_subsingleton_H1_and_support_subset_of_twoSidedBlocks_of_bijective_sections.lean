-- Prove2me | solution 1 for AlgebraicGeometry.RelPicard.exists_split_injective_forall_subsingleton_H1_and_support_subset_of_twoSidedBlocks_of_bijective_sections
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:03.589526+00:00
-- url     : https://prove2.me/submissions/c4b15e68-3196-597d-9b5f-f6245d6b7e90

import Mathlib
import Theorems.Thm_AlgebraicGeometry_RelPicard_exists_split_injective_forall_subsingleton_H1_and_support_subset_of_twoSidedBlocks_of_twoGluedSmoothCurveDegeneration
import Theorems.Thm_AlgebraicGeometry_RelPicard_exists_injective_forall_finrank_H0_add_eq_and_subsingleton_H1_of_blocks_of_isAlgEquivZero_of_lt_card
import Theorems.Thm_AlgebraicGeometry_RelPicard_exists_fibreIso_hom_comp_eq
import Theorems.Thm_AlgebraicGeometry_Scheme_TwoAffineOpenCover_exists_linearEquiv_sectionsOf_of_iso
import Theorems.Thm_AlgebraicGeometry_Scheme_TwoAffineOpenCover_finrank_H0_unit_fibre_eq_one_of_bijective_sections
import Theorems.Thm_AlgebraicGeometry_isIntegral_of_smooth_of_preconnectedSpace
import Theorems.Thm_AlgebraicGeometry_geometricallyConnected_of_bijective_algebraMap_sections
import Theorems.Thm_AlgHom_nonempty_equiv_fin_of_tensorProduct_algEquiv_pi
import Definitions.Def_AlgebraicGeometry_ModulesPullbackMonoidal
import Definitions.Def_AlgebraicCurve_CurveModel
import Definitions.Def_AlgebraicCurve_AdelicIndex
import Definitions.Def_AlgebraicGeometry_NeronModelPropertyBundleCarrier
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import Definitions.Def_AlgebraicGeometry_RepresentsRelSubPic
import Definitions.Def_AlgebraicGeometry_RelPicardAlgEquivZeroCut
import Definitions.Def_AlgebraicGeometry_RelSubPicPresheaf
import Definitions.Def_CategoryTheory_OverTotalPresheaf
import Definitions.Def_AlgebraicGeometry_LocalRepresentabilityULift
import Definitions.Def_AlgebraicGeometry_AffineLimit
import Definitions.Def_AlgebraicGeometry_RelPicardThetaBundle
import Definitions.Def_AlgebraicGeometry_TwoAffineOpenCover
import Definitions.Def_AlgebraicGeometry_TwoChartCechSectionsOf
import Definitions.Def_AlgebraicGeometry_RelEffCartierDiv
import Definitions.Def_AlgebraicGeometry_RelEffCartierDivSupportedIn
import Definitions.Def_AlgebraicGeometry_RelEffCartierDivFunctor
import Definitions.Def_AlgebraicGeometry_RelEffCartierDivRestrict
import Definitions.Def_AlgebraicGeometry_IdealSheafModule
import Definitions.Def_SheafOfModules_Monoidal
import Definitions.Def_AlgebraicGeometry_RelEffCartierDivTwist2
import Definitions.Def_AlgebraicGeometry_ModulesSectionZeroScheme

import Definitions.Def_AlgebraicGeometry_SmoothProperCurveBase
import Definitions.Def_AlgebraicGeometry_RelEffCartierDivSum
import Definitions.Def_AlgebraicGeometry_RelPicardChartSections
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_RelPicard_exists_split_injective_forall_subsingleton_H1_and_support_subset_of_twoSidedBlocks_of_bijective_sections
p2m_attr_erase "instance" "AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instNeg AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instSMulInt AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instAddCommGroup AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instAdd AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instSub AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instModuleCarrierObjOppositeOpensCarrierCarrierCommRingCatPresheafOpOpensTop AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instSMulCarrierObjOppositeOpensCarrierCarrierCommRingCatPresheafOpOpensTop AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instSMulNat AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instZero AlgebraicGeometry.OModulePresheaf.isScalarTower AlgebraicGeometry.Scheme.OrderedAffineCover.instLinearOrder AlgebraicGeometry.OModulePresheaf.module AlgebraicGeometry.Scheme.OrderedAffineCover.instFintype AlgebraicGeometry.Scheme.OrderedAffineCover.instFintypeIdx AlgebraicGeometry.OModulePresheaf.addCommGroup AlgebraicGeometry.Scheme.OrderedAffineCover.instDecidableEqIdx AlgebraicGeometry.OModulePresheaf.moduleSections AlgebraicGeometry.OModulePresheaf.instSubsingletonObjZero AlgebraicGeometry.OModulePresheaf.Leray.relAltC_scalarTower AlgebraicGeometry.OModulePresheaf.Leray.ker_relAltd_modΓ AlgebraicGeometry.OModulePresheaf.Leray.relAltC_modΓ AlgebraicGeometry.OModulePresheaf.Leray.biC_abGrp AlgebraicGeometry.OModulePresheaf.Leray.relAltH_modΓ AlgebraicGeometry.OModulePresheaf.Leray.ker_relAltd_smul AlgebraicGeometry.OModulePresheaf.Leray.relAltH_scalarTower AlgebraicGeometry.OModulePresheaf.Leray.relAltH_smul AlgebraicGeometry.OModulePresheaf.Leray.biC_module AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instDecidableEqIdx AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instFintype AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instLinearOrder AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instFintypeIdx DoubleComplex.instModuleE₂I DoubleComplex.Bounded.modR DoubleComplex.instModuleE₂II DoubleComplex.instAddCommGroupE₂II DoubleComplex.Bounded.abGrp DoubleComplex.instAddCommGroupE₂I AlgebraicGeometry.ChowDatum.hι_closed AlgebraicGeometry.ChowDatumProj.hιN_closed AlgebraicGeometry.ChowDatumProj.hp_proper"
p2m_attr_erase "instance" "AlgebraicGeometry.ChowDatum.hp_isoU AlgebraicGeometry.ChowDatum.hp_proper AlgebraicGeometry.ProjSpace.algebraAway AlgebraicGeometry.ProjSpace.instIsProperProdOverπ AlgebraicGeometry.ChowDatumProj.hp_isoU AlgebraicGeometry.ProjSpace.isProper_π AlgebraicGeometry.ProjSpace.finiteType_mvPolynomial ProjSpaceCech.GradedModule.H.module ProjSpaceCech.GradedModule.H.addCommGroup ProjSpaceCech.GradedModule.sec.instAdd ProjSpaceCech.GradedModule.sec.instNeg ProjSpaceCech.GradedModule.acg ProjSpaceCech.GradedModule.Frac.setoid ProjSpaceCech.GradedModule.modR ProjSpaceCech.GradedModule.sec.instModule ProjSpaceCech.GradedModule.sec.instAddCommGroup ProjSpaceCech.GradedModule.sec.instZero ProjSpaceCech.GradedModule.Presentation.fJ ProjSpaceCech.GradedModule.sec.instSMul ProjSpaceCech.Twist.H.module ProjSpaceCech.Idx.instFintype ProjSpaceCech.Twist.H.addCommGroup ProjSpaceCech.Idx.instDecidableEq ProjSpaceCech.Twist.Mon.instDecidableEq ProjSpaceCech.Twist.cochain.instAddCommGroup ProjSpaceCech.Twist.cochain.instModule SheafOfModules.isIso_ihomModelToIhom AlgebraicCurve.IsCurveOver.instNontrivialKaehler AlgebraicCurve.IsCurveOver.instFreeKaehler AlgebraicCurve.IsCurveOver.toHasPrincipalDivisors AlgebraicCurve.IsCurveOver.instFiniteResidue AlgebraicCurve.instFundamentalIdentityOfSumRamificationInertia AlgebraicCurve.Place.instIsScalarTowerResidueFieldRestrictPushforward AlgebraicCurve.Place.instAlgebraResidueFieldRestrictPushforward AlgebraicCurve.Place.instIsLocalHomRestrictInclusion AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt"
p2m_attr_erase "instance" "AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.SemilinearAut.instDistribMulActionSubtypeProdRingAutMemSubgroupPic0 AlgebraicCurve.SemilinearAut.instDistribMulActionSubtypeProdRingAutMemSubgroupDivisor AlgebraicCurve.Pic0.instModuleZModTorsion AlgebraicCurve.SemilinearAut.instSMulSubtypeProdRingAutMemSubgroupPlace AlgebraicCurve.SemilinearAut.instDistribMulActionTorsion AlgebraicCurve.SemilinearAut.instSMulSubtypeProdRingAutMemSubgroupPic0 AlgebraicCurve.SemilinearAut.instSMulTorsion AlgebraicCurve.SemilinearAut.instMulActionSubtypeProdRingAutMemSubgroupPlace AlgebraicCurve.SemilinearAut.instSMulCommClassZModTorsion AlgebraicCurve.SemilinearAut.instMulSemiringActionSubtypeProdRingAutMemSubgroup instDecEqAlgebraicClosureRat WeierstrassCurve.Affine.Point.instDistribMulActionAlgEquiv WeierstrassCurve.Affine.Point.instModuleZModTorsionBy WeierstrassCurve.Affine.Point.instSMulTorsionBy WeierstrassCurve.Affine.Point.instDistribMulActionTorsionBy WeierstrassCurve.Affine.Point.instSMulAlgEquiv WeierstrassCurve.Affine.Point.instSMulCommClassAlgEquivZModTorsionBy AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions AlgebraicCurve.instHasLocalResidue_of_hasCanonicalLocalResidueK AlgebraicCurve.instHasCanonicalLocalResidueK_of_hasCanonicalLocalResidueKStar AlgebraicCurve.Place.kw_ffgc_finiteDimensional_adicCompletion instAlgebraSubtypeMemValuationSubring_definitions AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersIntegersCompletion ModularCurve.KwF4gRRTate.instAlgebraKAdicCompletionIntegers AlgebraicCurve.Place.kw_ffgc_continuousSMul_adicCompletionComap AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersCompletionCompletion IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions AlgebraicCurve.instHasCanonicalLocalResidueK AlgebraicCurve.Place.instAlgebra_restrictResidueField AlgebraicCurve.Place.instIsScalarTower_restrictResidueField AlgebraicCurve.instHasLocalResidue AlgebraicCurve.HasSeparableResidue.of_perfectField_of_isCurveOver AlgebraicCurve.HasSeparableResidue.of_perfectField"
p2m_attr_erase "instance" "AlgebraicCurve.Place.instIsLocalHom_restrictSubringHom AlgebraicCurve.instHasCanonicalLocalResidueKStar ModularCurve.KwNo6Pin.isLocalRing_completion"
p2m_attr_erase "simp" "AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.sub_app AlgebraicGeometry.Scheme.IdealSheafData.sres_sresTop AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.add_app AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.mk.sizeOf_spec AlgebraicGeometry.Scheme.IdealSheafData.coe_resLE AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.smul_app AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.coe_ofLE_app AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.ideal_range AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.zero_app AlgebraicGeometry.Scheme.IdealSheafData.sres_sres AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.comp_app AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.neg_app AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.id_app AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.coe_mulRight_app AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.nsmul_app AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.mk.injEq AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.zsmul_app AlgebraicGeometry.Scheme.OrderedAffineCover.mk.injEq AlgebraicGeometry.OModulePresheaf.mk.sizeOf_spec AlgebraicGeometry.Scheme.OrderedAffineCover.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.mk.injEq AlgebraicGeometry.Scheme.Modules.pullbackLocalSection_neg AlgebraicGeometry.Scheme.Modules.pullbackLocalSection_zero AlgebraicGeometry.Scheme.Modules.pullbackLocalSection_sub AlgebraicGeometry.Scheme.Modules.pullbackLocalSection_add AlgebraicGeometry.OModulePresheaf.prod_obj AlgebraicGeometry.OModulePresheaf.restrOpen_obj AlgebraicGeometry.OModulePresheaf.DevissageStep.mk.injEq AlgebraicGeometry.OModulePresheaf.pushforward_obj AlgebraicGeometry.OModulePresheaf.im_obj AlgebraicGeometry.OModulePresheaf.pow_obj AlgebraicGeometry.OModulePresheaf.fstHom_app AlgebraicGeometry.OModulePresheaf.ker_obj AlgebraicGeometry.OModulePresheaf.coker_obj AlgebraicGeometry.OModulePresheaf.DevissageStep.mk.sizeOf_spec AlgebraicGeometry.Scheme.OrderedAffineCover.preimage_U AlgebraicGeometry.OModulePresheaf.sndHom_app AlgebraicGeometry.OModulePresheaf.Hom.mk.injEq AlgebraicGeometry.OModulePresheaf.Hom.id_app AlgebraicGeometry.OModulePresheaf.AffHom.appSections_apply"
p2m_attr_erase "simp" "AlgebraicGeometry.OModulePresheaf.AffHom.comp_app AlgebraicGeometry.OModulePresheaf.AffSES.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.AffHom.kerMap_coe AlgebraicGeometry.OModulePresheaf.AffHom.id_app AlgebraicGeometry.OModulePresheaf.Hom.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.Hom.toAffHom_app AlgebraicGeometry.OModulePresheaf.SES.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.AffHom.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.Hom.comp_app AlgebraicGeometry.OModulePresheaf.SES.mk.injEq AlgebraicGeometry.OModulePresheaf.AffHom.mk.injEq AlgebraicGeometry.OModulePresheaf.Hom.appSections_apply AlgebraicGeometry.OModulePresheaf.AffSES.mk.injEq AlgebraicGeometry.OModulePresheaf.Leray.restrictToPreimage_U AlgebraicGeometry.Scheme.OrderedAffineCover.toCoverOf_U AlgebraicGeometry.Scheme.OrderedAffineCoverOf.mk.sizeOf_spec AlgebraicGeometry.Scheme.OrderedAffineCoverOf.mk.injEq AlgebraicGeometry.Scheme.OrderedAffineCover.restrict_U DoubleComplex.Bounded.mk.injEq DoubleComplex.Bounded.mk.sizeOf_spec DoubleComplex.Convergence.mk.injEq DoubleComplex.Convergence.mk.sizeOf_spec DoubleComplex.SubQuot.mk.sizeOf_spec DoubleComplex.SubQuot.mk.injEq AlgebraicGeometry.ChowDatumProj.mk.sizeOf_spec AlgebraicGeometry.ChowDatum.mk.sizeOf_spec AlgebraicGeometry.ChowDatumProj.mk.injEq AlgebraicGeometry.ChowDatum.mk.injEq ProjSpaceCech.GradedModule.mk.injEq ProjSpaceCech.GradedModule.mk.sizeOf_spec ProjSpaceCech.GradedModule.Frac.mk.sizeOf_spec ProjSpaceCech.GradedModule.Presentation.mk.injEq ProjSpaceCech.GradedModule.Frac.mk.injEq ProjSpaceCech.GradedModule.Presentation.mk.sizeOf_spec ProjSpaceCech.GradedModule.Hom.shift_toLinearMap ProjSpaceCech.GradedModule.Hom.mk.sizeOf_spec ProjSpaceCech.GradedModule.Hom.mk.injEq AlgebraicGeometry.Scheme.Modules.tensorPow_zero AlgebraicGeometry.Scheme.Modules.tensorPow_succ AlgebraicGeometry.Scheme.Modules.tensorSections_zero_right"
p2m_attr_erase "simp" "AlgebraicGeometry.Scheme.Modules.map_unitSection AlgebraicGeometry.Scheme.Modules.tensorSectionsBilin_apply AlgebraicGeometry.Scheme.Modules.tensorPowSection_zero AlgebraicGeometry.Scheme.Modules.tensorSections_zero_left PresheafOfModules.InternalHom.IsSheafAux.appAt_toPresheafHom SheafOfModules.ihomSectionsEquivFamily_unit AlgebraicGeometry.Scheme.Modules.restrictHomEquivFamily_apply SheafOfModules.ihomEval_unit_app AlgebraicGeometry.Scheme.Modules.ihomEval_zero_right AlgebraicGeometry.Scheme.Modules.ihomEval_zero_left AlgebraicGeometry.Scheme.Modules.homOfFamily_app_apply SheafOfModules.unit_ihomSectionsEquivFamily AlgebraicGeometry.Scheme.Modules.familyOfHom_app AlgebraicGeometry.Scheme.Modules.restrictUnitIso_hom_app_apply AlgebraicGeometry.Scheme.Modules.restrictUnitIso_inv_app_apply AlgebraicGeometry.Scheme.Modules.restrictHomOfFamily_app_apply AlgebraicGeometry.Scheme.Modules.restrictHomEquivFamily_symm_apply TwoChartCech.Mumford.dK_apply TwoChartCech.Mumford.ι0_apply TwoChartCech.Mumford.ι1_apply TwoChartCech.KerCoprod.dK_apply TwoChartCech.KerCoprod.ι1_apply TwoChartCech.KerCoprod.ι0_apply AlgebraicGeometry.tilde.functorCompPullbackSpecIso_app AlgebraicCurve.Divisor.mapRestrict_single AlgebraicCurve.Divisor.pushforward_single AlgebraicCurve.Place.coe_restrictInclusion AlgebraicCurve.Place.mem_fiber AlgebraicCurve.Place.restrict_toValuationSubring AlgebraicCurve.Divisor.degree_pushforward AlgebraicCurve.Place.restrictResidueMap_residue AlgebraicCurve.Pic0.coe_pushforwardDegZeroHom AlgebraicCurve.Pic0.coe_pullbackDegZeroHom AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal AlgebraicCurve.IsFrobeniusEndo.frobNormRingHom_apply ModularCurve.frobeniusPushforwardGeomLevelPic0_mk"
p2m_attr_erase "simp" "ModularCurve.coe_frobeniusGeomLevelEquiv_apply ModularCurve.coe_frobeniusPushforwardGeomLevelDegZero ModularCurve.heckeFibreGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusGeomLevel_apply_coe ModularCurve.frobeniusPullbackGeomLevelPic0OfIsCurveOver_mk ModularCurve.coe_heckeFibreGeomLevelDegZero ModularCurve.coe_frobeniusPullbackGeomLevelDegZero ModularCurve.frobeniusPullbackGeomLevelPic0_mk ModularCurve.frobeniusPullbackGeomLevel_single ModularCurve.heckeFibreGeomLevelPic0_mk ModularCurve.frobeniusPushforwardGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusPushforwardGeomLevel_single ModularCurve.qExpandAlgC_apply AlgebraicCurve.Place.congrEquiv_symm_apply AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply AlgebraicCurve.RationalFunctionField.deg_placeOfPoint AlgebraicCurve.Divisor.degree_pushforwardAlong AlgebraicCurve.Pic0.coe_degZeroCorrespondence AlgebraicCurve.Place.mem_fiberAlong AlgebraicCurve.SemilinearAut.toRingAut_inv AlgebraicCurve.SemilinearAut.smul_def AlgebraicCurve.SemilinearAut.smul_single AlgebraicCurve.SemilinearAut.smul_toValuationSubring AlgebraicCurve.SemilinearAut.baseAut_inv AlgebraicCurve.SemilinearAut.baseAut_ofAlgAut AlgebraicCurve.SemilinearAut.toRingAut_ofAlgAut AlgebraicCurve.SemilinearAut.torsionRep_apply AlgebraicCurve.SemilinearAut.toRingAut_one AlgebraicCurve.SemilinearAut.deg_smul AlgebraicCurve.SemilinearAut.degree_smul AlgebraicCurve.SemilinearAut.coe_degZeroSMulHom AlgebraicCurve.SemilinearAut.baseAut_mul AlgebraicCurve.SemilinearAut.coe_smulValuationSubringEquiv_apply AlgebraicCurve.SemilinearAut.baseAut_one AlgebraicCurve.SemilinearAut.ofAlgAut_smul AlgebraicCurve.SemilinearAut.coe_torsion_smul AlgebraicCurve.SemilinearAut.toRingAut_mul"
p2m_attr_erase "simp" "AlgebraicCurve.coe_frobeniusPushforwardDegZero AlgebraicCurve.IsFrobeniusEndo.coe_frobeniusPullbackDegZero ModularCurve.jqNModC_one ModularCurve.qExpand_coeff_mul ModularCurve.qExpandₐ_apply ModularCurve.jqN_one ModularCurve.qExpand_single ModularCurve.dedekindPsi_one ModularCurve.ModularPolynomialData.mk.sizeOf_spec ModularCurve.evalAtJ_X ModularCurve.ModularPolynomialData.mk.injEq ModularCurve.constantCoeff_jNum ModularCurve.constantCoeff_eisenstein4 ModularCurve.qExpand_C ModularCurve.coeff_jq_neg_one ModularCurve.constantCoeff_jNumQ ModularCurve.reduceModBivar_C_X ModularCurve.laurentMap_coeff ModularCurve.reduceModBivar_X ModularCurve.laurentMap_single ModularCurve.evalAtJInt_X ModularCurve.evalAtJMod_X ModularCurve.jqNMod_one ModularCurve.aeval_heckeGen ModularCurve.coe_mTorsionGaloisRep_apply ModularCurve.eisensteinSystem_of_dvd ModularCurve.eisensteinSystem_of_not_dvd FreyPackage.mk.sizeOf_spec FreyPackage.mk.injEq WeierstrassCurve.Affine.Point.galoisRepModuleEnd_apply AlgebraicCurve.RationalFunctionField.placeInfty_toValuationSubring AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none AlgebraicCurve.Divisor.evalFun_zero AlgebraicCurve.Place.evalAt_one AlgebraicCurve.Place.differentialCoeff_zero AlgebraicCurve.Place.differentialCoeff_dCoord AlgebraicCurve.TranscendenceTower.mk.sizeOf_spec"
p2m_attr_erase "simp" "AlgebraicCurve.IntegralBasisInLSpace.mk.injEq AlgebraicCurve.TranscendenceTower.mk.injEq AlgebraicCurve.PoleDivisorPackage.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.sizeOf_spec AlgebraicCurve.PoleDivisorPackage.mk.injEq AlgebraicCurve.coe_cechH0Equiv_apply AlgebraicCurve.cechH1ToH1_mk AlgebraicCurve.lSpaceOn_univ AlgebraicCurve.lSpaceOn_empty AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.sizeOf_spec AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.injEq AlgebraicCurve.adeleSingle_coe AlgebraicCurve.kaehlerResidueTermKFam_apply AlgebraicCurve.Place.LocalResidueData.mk.injEq AlgebraicCurve.Place.LocalResidueData.mk.sizeOf_spec AlgebraicCurve.Place.kw_ffgc_adicCompletionComapIntegers_coe AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.sizeOf_spec AlgebraicCurve.Place.mem_simplePoleSubmodule AlgebraicCurve.Place.coe_uniformizerSubring ModularCurve.Lg37.Lg37CompletionSection.mk.injEq AlgebraicCurve.Place.CoefficientFieldSection.mk.injEq AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.injEq ModularCurve.Lg37.Lg37CompletionSection.mk.sizeOf_spec AlgebraicCurve.Place.CoefficientFieldSection.mk.sizeOf_spec AlgebraicCurve.Place.poleSubmodule_one AlgebraicCurve.Place.mem_poleSubmodule RegularLocalRingQuotientAscent.dualNumberFst_apply"

set_option autoImplicit false

universe u

p2m_open "CategoryTheory CategoryTheory.Limits Opposite CategoryTheory.MonoidalCategory AlgebraicGeometry P2MW.S_AlgebraicGeometry_RelPicard_exists_split_injective_forall_subsingleton_H1_and_support_subset_of_twoSidedBlocks_of_bijective_sections.AlgebraicGeometry AlgebraicGeometry.RelPicard NeronModelInfra"

p2m_open "AlgebraicGeometry.SmoothProperCurve AlgebraicCurve~genus"

noncomputable section

namespace AlgebraicGeometry
p2m_export "AlgebraicGeometry" "Spec.map_comp SmoothOfRelativeDimension IsProper Scheme.Modules.pullback Scheme.Opens.range_ι Scheme.Hom GeometricallyIntegral Scheme.Hom.preimage_inf Scheme.Pullback.range_map Spec IsIntegral Spec.map Scheme Smooth IsOpenImmersion Flat isIso_of_isOpenImmersion_of_opensRange_eq_top IsClosedImmersion IsReduced smoothOfRelativeDimension_isStableUnderBaseChange Etale Scheme.Hom.preimage_sup Scheme.Modules GeometricallyConnected Scheme.Opens IsAffineHom GeometricallyConnected.connectedSpace_of_subsingleton geometrically Scheme.Hom.coe_opensRange RelPicard.exists_split_injective_forall_subsingleton_H1_and_support_subset_of_twoSidedBlocks_of_twoGluedSmoothCurveDegeneration Scheme.Modules.IsInvertible Scheme.TwoAffineOpenCover Scheme.TwoAffineOpenCover.specMap Scheme.TwoAffineOpenCover.algebraOfHom SmoothProperCurve.specMap Scheme.Modules.zeroSchemeIdeal RelPicard.exists_injective_forall_finrank_H0_add_eq_and_subsingleton_H1_of_blocks_of_isAlgEquivZero_of_lt_card Scheme.TwoAffineOpenCover.exists_linearEquiv_sectionsOf_of_iso Scheme.TwoAffineOpenCover.finrank_H0_unit_fibre_eq_one_of_bijective_sections isIntegral_of_smooth_of_preconnectedSpace geometricallyConnected_of_bijective_algebraMap_sections Scheme.Modules.pullbackTensorUnitObjIso"
namespace HGPprimeImpl
p2m_open "AlgebraicGeometry"

open scoped TensorProduct

theorem nonempty_algHom_of_faithfullyFlat (R A Ω : Type u) [CommRing R] [CommRing A] [Algebra R A]
    [Module.Finite R A] [Module.FaithfullyFlat R A] [Field Ω] [IsAlgClosed Ω] [Algebra R Ω] :
    Nonempty (A →ₐ[R] Ω) := by
  classical

  haveI : Nontrivial (Ω ⊗[R] A) := Module.FaithfullyFlat.rTensor_nontrivial R A Ω
  haveI : Module.Finite Ω (Ω ⊗[R] A) := inferInstance
  obtain ⟨m, hm⟩ := Ideal.exists_maximal (Ω ⊗[R] A)
  haveI := hm

  haveI : Module.Finite Ω ((Ω ⊗[R] A) ⧸ m) := inferInstance
  haveI : Algebra.IsIntegral Ω ((Ω ⊗[R] A) ⧸ m) := Algebra.IsIntegral.of_finite Ω _
  have hbij : Function.Bijective (algebraMap Ω ((Ω ⊗[R] A) ⧸ m)) :=
    IsAlgClosed.algebraMap_bijective_of_isIntegral
  let e : ((Ω ⊗[R] A) ⧸ m) ≃ₐ[Ω] Ω := (AlgEquiv.ofBijective (Algebra.ofId Ω ((Ω ⊗[R] A) ⧸ m)) hbij).symm
  exact ⟨(e.restrictScalars R).toAlgHom.comp
    ((Ideal.Quotient.mkₐ R m).comp (Algebra.TensorProduct.includeRight (R := R) (A := Ω) (B := A)))⟩

theorem finrank_sectionsOf_unit_fibre
    {R : Type u} [CommRing R] {C : Scheme.{u}} (c : C ⟶ Spec (CommRingCat.of R))
    (hH0 : ∀ (A' : Type u) [CommRing A'] [Algebra R A'],
      letI := Scheme.TwoAffineOpenCover.algebraOfHom
        (Limits.pullback.snd c (Scheme.TwoAffineOpenCover.specMap R A')) ⊤
      Function.Bijective (algebraMap A' Γ(Limits.pullback c (Scheme.TwoAffineOpenCover.specMap R A'), ⊤)))
    (g : ℕ) {k : Type u} [Field k] (x : Spec (CommRingCat.of k) ⟶ Spec (CommRingCat.of R))
    (hg : ∀ 𝒲 : (pullback (pullback.snd c (𝟙 (Spec (CommRingCat.of R)))) x).TwoAffineOpenCover,
      Module.finrank k (𝒲.sectionsOf (fibreAt c (𝟙 _) x)
        (SheafOfModules.unit (pullback (pullback.snd c (𝟙 (Spec (CommRingCat.of R)))) x).ringCatSheaf)).H1 = g)
    (𝒱 : (pullback c x).TwoAffineOpenCover) :
    Module.finrank k (𝒱.sectionsOf (pullback.snd c x) (SheafOfModules.unit (pullback c x).ringCatSheaf)).H0 = 1 ∧
    Module.finrank k (𝒱.sectionsOf (pullback.snd c x) (SheafOfModules.unit (pullback c x).ringCatSheaf)).H1 = g := by

  obtain ⟨φ, hφsnd, -, -⟩ := exists_fibreIso_hom_comp_eq c (𝟙 (Spec (CommRingCat.of R))) x x (Category.comp_id x)

  let e : SheafOfModules.unit (pullback (pullback.snd c (𝟙 (Spec (CommRingCat.of R)))) x).ringCatSheaf ≅
      (Scheme.Modules.pullback φ.hom).obj (SheafOfModules.unit (pullback c x).ringCatSheaf) :=
    (Scheme.Modules.pullbackTensorUnitObjIso φ.hom).symm
  obtain ⟨𝒲, -, -, ⟨e0⟩, ⟨e1⟩⟩ := Scheme.TwoAffineOpenCover.exists_linearEquiv_sectionsOf_of_iso
    (fibreAt c (𝟙 _) x) (pullback.snd c x) φ hφsnd 𝒱 (SheafOfModules.unit (pullback c x).ringCatSheaf)
    (SheafOfModules.unit (pullback (pullback.snd c (𝟙 (Spec (CommRingCat.of R)))) x).ringCatSheaf) e
  refine ⟨?_, ?_⟩
  · rw [← e0.finrank_eq]
    exact Scheme.TwoAffineOpenCover.finrank_H0_unit_fibre_eq_one_of_bijective_sections c hH0 (𝟙 _) k x 𝒲
  · rw [← e1.finrank_eq]
    exact hg 𝒲

theorem smoothOfRelativeDimension_one_snd_of_range_subset
    {R : Type u} [CommRing R] {C : Scheme.{u}} (c : C ⟶ Spec (CommRingCat.of R))
    (U : C.Opens) [SmoothOfRelativeDimension 1 (U.ι ≫ c)]
    {k : Type u} [Field k] (x : Spec (CommRingCat.of k) ⟶ Spec (CommRingCat.of R))
    (hU : Set.range (pullback.fst c x).base ⊆ (U : Set C)) :
    SmoothOfRelativeDimension 1 (pullback.snd c x) := by
  haveI := smoothOfRelativeDimension_isStableUnderBaseChange (n := 1)
  set j := pullback.map (U.ι ≫ c) x c x U.ι (𝟙 _) (𝟙 _) (by simp) (by simp) with hj
  have hrange : Set.range ⇑j = (pullback.fst c x) ⁻¹' (U : Set C) := by
    rw [hj, Scheme.Pullback.range_map]
    simp [Scheme.Opens.range_ι]
  haveI : IsIso j := by
    refine isIso_of_isOpenImmersion_of_opensRange_eq_top _ ?_
    ext z
    simp only [Scheme.Hom.coe_opensRange, TopologicalSpace.Opens.coe_top, Set.mem_univ, iff_true]
    rw [hrange]
    exact hU ⟨z, rfl⟩
  have hjsnd : j ≫ pullback.snd c x = pullback.snd (U.ι ≫ c) x := by
    rw [hj, pullback.lift_snd, Category.comp_id]
  haveI : SmoothOfRelativeDimension 1 (pullback.snd (U.ι ≫ c) x) :=
    MorphismProperty.pullback_snd (P := @SmoothOfRelativeDimension 1) _ _ inferInstance
  have : pullback.snd c x = inv j ≫ pullback.snd (U.ι ≫ c) x := by
    rw [← hjsnd, IsIso.inv_hom_id_assoc]
  rw [this]
  exact inferInstanceAs (SmoothOfRelativeDimension (0 + 1) _)

theorem isIntegral_pullback_of_smooth
    {R : Type u} [CommRing R] {C : Scheme.{u}} (c : C ⟶ Spec (CommRingCat.of R)) [GeometricallyConnected c]
    {k : Type u} [Field k] (x : Spec (CommRingCat.of k) ⟶ Spec (CommRingCat.of R))
    (hsm : Smooth (pullback.snd c x)) : IsIntegral (pullback c x) := by
  haveI := hsm
  haveI : ConnectedSpace ↥(pullback c x) :=
    GeometricallyConnected.connectedSpace_of_subsingleton (f := pullback.snd c x)
  haveI : Nonempty ↥(pullback c x) := ConnectedSpace.toNonempty
  exact isIntegral_of_smooth_of_preconnectedSpace (pullback.snd c x)

section Blocks

variable {A : Type u} [CommRing A] {C' : Scheme.{u}} (c' : C' ⟶ Spec (CommRingCat.of A))
  {M : ℕ} {B : Fin M → Type u} [∀ i, CommRing (B i)] [∀ i, Algebra A (B i)]
  {deg : Fin M → ℕ}
  (z : ∀ i, Spec (CommRingCat.of (B i)) ⟶ C') (hz : ∀ i, z i ≫ c' = specMap A (B i))
  {Ω : Type u} [Field Ω] [Algebra A Ω]

def ptOf (i : Fin M) (ψ : B i →ₐ[A] Ω) :
    {q : Spec (CommRingCat.of Ω) ⟶ pullback c' (specMap A Ω) // q ≫ pullback.snd c' (specMap A Ω) = 𝟙 _} :=
  ⟨pullback.lift (Spec.map (CommRingCat.ofHom ψ.toRingHom) ≫ z i) (𝟙 _) (by
      rw [Category.assoc, hz i, Category.id_comp]
      show Spec.map _ ≫ Spec.map _ = Spec.map _
      rw [← Spec.map_comp, ← CommRingCat.ofHom_comp, AlgHom.toRingHom_eq_coe, AlgHom.comp_algebraMap]),
    pullback.lift_snd _ _ _⟩

@[scoped simp] theorem ptOf_fst (i : Fin M) (ψ : B i →ₐ[A] Ω) :
    (ptOf c' z hz i ψ).1 ≫ pullback.fst c' (specMap A Ω) = Spec.map (CommRingCat.ofHom ψ.toRingHom) ≫ z i :=
  pullback.lift_fst _ _ _

variable [∀ i, Fintype (B i →ₐ[A] Ω)]

def blockAll (i : Fin M) :
    Finset {q : Spec (CommRingCat.of Ω) ⟶ pullback c' (specMap A Ω) // q ≫ pullback.snd c' (specMap A Ω) = 𝟙 _} := by
  classical
  exact Finset.univ.image (ptOf c' z hz i)

theorem ptOf_mem_blockAll (i : Fin M) (ψ : B i →ₐ[A] Ω) : ptOf c' z hz i ψ ∈ blockAll c' z hz i := by
  classical
  unfold blockAll
  exact Finset.mem_image_of_mem _ (Finset.mem_univ ψ)

theorem card_blockAll_le (hcnt : ∀ i, Fintype.card (B i →ₐ[A] Ω) ≤ deg i) (i : Fin M) :
    (blockAll c' z hz (Ω := Ω) i).card ≤ deg i := by
  classical
  unfold blockAll
  exact Finset.card_image_le.trans (by rw [Finset.card_univ]; exact hcnt i)

theorem blockAll_nonempty (i : Fin M) (h : Nonempty (B i →ₐ[A] Ω)) : (blockAll c' z hz (Ω := Ω) i).Nonempty :=
  ⟨_, ptOf_mem_blockAll c' z hz i h.some⟩

theorem mem_blockAll_iff (i : Fin M)
    (q : {q : Spec (CommRingCat.of Ω) ⟶ pullback c' (specMap A Ω) // q ≫ pullback.snd c' (specMap A Ω) = 𝟙 _}) :
    q ∈ blockAll c' z hz i ↔ ∃ ψ, ptOf c' z hz i ψ = q := by
  classical
  unfold blockAll
  simp

theorem range_subset_of_mem_blockAll (i : Fin M)
    (q : {q : Spec (CommRingCat.of Ω) ⟶ pullback c' (specMap A Ω) // q ≫ pullback.snd c' (specMap A Ω) = 𝟙 _})
    (hq : q ∈ blockAll c' z hz i) :
    Set.range (q.1 ≫ pullback.fst c' (specMap A Ω)).base ⊆ Set.range (z i).base := by
  obtain ⟨ψ, rfl⟩ := (mem_blockAll_iff c' z hz i q).mp hq
  rw [ptOf_fst]
  rintro _ ⟨y, rfl⟩
  exact ⟨(Spec.map (CommRingCat.ofHom ψ.toRingHom)).base y, rfl⟩

theorem disjoint_blockAll (hdisj : Pairwise fun i j => Disjoint (Set.range (z i).base) (Set.range (z j).base))
    {i j : Fin M} (hij : i ≠ j) : Disjoint (blockAll c' z hz (Ω := Ω) i) (blockAll c' z hz j) := by
  classical
  rw [Finset.disjoint_left]
  intro q hqi hqj
  have hi := range_subset_of_mem_blockAll c' z hz i q hqi
  have hj := range_subset_of_mem_blockAll c' z hz j q hqj
  have hpt : (q.1 ≫ pullback.fst c' (specMap A Ω)).base (IsLocalRing.closedPoint Ω) ∈
      Set.range (z i).base ∩ Set.range (z j).base := ⟨hi ⟨_, rfl⟩, hj ⟨_, rfl⟩⟩
  exact Set.disjoint_iff.mp (hdisj hij) hpt

end Blocks

def comapCover {X Y : Scheme.{u}} (i : Y ⟶ X) [IsAffineHom i] (𝒲 : X.TwoAffineOpenCover) :
    Y.TwoAffineOpenCover where
  U0 := i ⁻¹ᵁ 𝒲.U0
  U1 := i ⁻¹ᵁ 𝒲.U1
  isAffineOpen_U0 := 𝒲.isAffineOpen_U0.preimage _
  isAffineOpen_U1 := 𝒲.isAffineOpen_U1.preimage _
  sup_eq_top := by rw [← Scheme.Hom.preimage_sup, 𝒲.sup_eq_top]; rfl
  isAffineOpen_inf := by rw [← Scheme.Hom.preimage_inf]; exact 𝒲.isAffineOpen_inf.preimage _

end AlgebraicGeometry.HGPprimeImpl
p2m_reactivate "P2MW.S_AlgebraicGeometry_RelPicard_exists_split_injective_forall_subsingleton_H1_and_support_subset_of_twoSidedBlocks_of_bijective_sections.AlgebraicGeometry P2MW.S_AlgebraicGeometry_RelPicard_exists_split_injective_forall_subsingleton_H1_and_support_subset_of_twoSidedBlocks_of_bijective_sections.AlgebraicGeometry.HGPprimeImpl"
p2m_reactivate "P2MW.S_AlgebraicGeometry_RelPicard_exists_split_injective_forall_subsingleton_H1_and_support_subset_of_twoSidedBlocks_of_bijective_sections.AlgebraicGeometry"

end
p2m_reactivate "P2MW.S_AlgebraicGeometry_RelPicard_exists_split_injective_forall_subsingleton_H1_and_support_subset_of_twoSidedBlocks_of_bijective_sections.AlgebraicGeometry P2MW.S_AlgebraicGeometry_RelPicard_exists_split_injective_forall_subsingleton_H1_and_support_subset_of_twoSidedBlocks_of_bijective_sections.AlgebraicGeometry.HGPprimeImpl"

open AlgebraicGeometry.HGPprimeImpl in
theorem solution
    {R : Type u} [CommRing R] {C : Scheme.{u}} (c : C ⟶ Spec (CommRingCat.of R)) [IsProper c] [Flat c]

    (𝒱 : C.TwoAffineOpenCover)
    (hH0 : ∀ (A : Type u) [CommRing A] [Algebra R A],
      letI := Scheme.TwoAffineOpenCover.algebraOfHom
        (Limits.pullback.snd c (Scheme.TwoAffineOpenCover.specMap R A)) ⊤
      Function.Bijective (algebraMap A Γ(Limits.pullback c (Scheme.TwoAffineOpenCover.specMap R A), ⊤)))
    (ε : SchemeHomOver (𝟙 (Spec (CommRingCat.of R))) c) (U : C.Opens) [SmoothOfRelativeDimension 1 (U.ι ≫ c)]
    (hεA : Set.range ε.1 ⊆ (U : Set C))
    (hgoodU : ∀ (k : Type u) [Field k] [IsAlgClosed k] (x : Spec (CommRingCat.of k) ⟶ Spec (CommRingCat.of R)),
      Smooth (pullback.snd c x) → Set.range (pullback.fst c x).base ⊆ (U : Set C))
    (hgred : ∀ (k : Type u) [Field k] [IsAlgClosed k]
      (x : Spec (CommRingCat.of k) ⟶ Spec (CommRingCat.of R)), IsReduced (pullback c x))
    (g : ℕ)
    (hg : ∀ (k : Type u) [Field k] [IsAlgClosed k]
      (x : Spec (CommRingCat.of k) ⟶ Spec (CommRingCat.of R))
      (𝒲 : (pullback (pullback.snd c (𝟙 (Spec (CommRingCat.of R)))) x).TwoAffineOpenCover),
      Module.finrank k (𝒲.sectionsOf (fibreAt c (𝟙 _) x)
        (SheafOfModules.unit (pullback (pullback.snd c (𝟙 (Spec (CommRingCat.of R)))) x).ringCatSheaf)).H1 = g)

    (hbad : ∀ (k : Type u) [Field k] [IsAlgClosed k]
      (s : Spec (CommRingCat.of k) ⟶ Spec (CommRingCat.of R)), ¬ Smooth (pullback.snd c s) →
      ∃ (C₁ C₂ : Scheme.{u}) (c₁ : C₁ ⟶ Spec (CommRingCat.of k)) (c₂ : C₂ ⟶ Spec (CommRingCat.of k))
        (_ : IsProper c₁) (_ : SmoothOfRelativeDimension 1 c₁) (_ : GeometricallyIntegral c₁)
        (_ : IsProper c₂) (_ : SmoothOfRelativeDimension 1 c₂) (_ : GeometricallyIntegral c₂)
        (i₁ : SchemeHomOver c₁ (pullback.snd c s)) (i₂ : SchemeHomOver c₂ (pullback.snd c s))
        (_ : IsClosedImmersion i₁.1) (_ : IsClosedImmersion i₂.1) (n : ℕ),
        (∀ z : ↥(pullback c s), z ∈ Set.range i₁.1.base ∨ z ∈ Set.range i₂.1.base) ∧
        IsReduced (pullback i₁.1 i₂.1) ∧ Nat.card ↥(pullback i₁.1 i₂.1) = n ∧ 0 < n ∧
        ((sectionFibrePoint ε s).1).base (IsLocalRing.closedPoint k) ∈ Set.range i₁.1.base \ Set.range i₂.1.base ∧
        ((pullback.fst c s ⁻¹ᵁ U : (pullback c s).Opens) : Set ↥(pullback c s)) =
          (Set.range (pullback.fst i₁.1 i₂.1 ≫ i₁.1).base)ᶜ ∧
        Set.range i₁.1.base ∩ ((pullback.fst c s ⁻¹ᵁ U : (pullback c s).Opens) : Set ↥(pullback c s)) =
          connectedComponentIn ((pullback.fst c s ⁻¹ᵁ U : (pullback c s).Opens) : Set ↥(pullback c s))
            (((sectionFibrePoint ε s).1).base (IsLocalRing.closedPoint k)) ∧
        Set.range i₂.1.base ∩ ((pullback.fst c s ⁻¹ᵁ U : (pullback c s).Opens) : Set ↥(pullback c s)) =
          ((pullback.fst c s ⁻¹ᵁ U : (pullback c s).Opens) : Set ↥(pullback c s)) \
            connectedComponentIn ((pullback.fst c s ⁻¹ᵁ U : (pullback c s).Opens) : Set ↥(pullback c s))
              (((sectionFibrePoint ε s).1).base (IsLocalRing.closedPoint k)) ∧
        (∃ W₁ : (pullback c s).Opens, (W₁ : Set ↥(pullback c s)) = (Set.range i₂.1.base)ᶜ ∧
          IsOpenImmersion ((i₁.1 ⁻¹ᵁ W₁).ι ≫ i₁.1)) ∧
        (∃ W₂ : (pullback c s).Opens, (W₂ : Set ↥(pullback c s)) = (Set.range i₁.1.base)ᶜ ∧
          IsOpenImmersion ((i₂.1 ⁻¹ᵁ W₂).ι ≫ i₂.1)))
    (A : Type u) [CommRing A] [Algebra R A] [Module.Finite R A] [Module.FaithfullyFlat R A]

    {M M' : ℕ} (B : Fin M → Type u) [∀ i, CommRing (B i)] [∀ i, Algebra R (B i)]
    [∀ i, Module.Finite R (B i)] [∀ i, Algebra.Etale R (B i)]
    (deg : Fin M → ℕ) (hdeg : ∀ i, 1 ≤ deg i) (φ : ∀ i, TensorProduct R A (B i) ≃ₐ[A] (Fin (deg i) → A))
    (z : ∀ i, Spec (CommRingCat.of (B i)) ⟶ C) [∀ i, IsClosedImmersion (z i)]
    (hz : ∀ i, z i ≫ c = Spec.map (CommRingCat.ofHom (algebraMap R (B i))))
    (hzU : ∀ i, Set.range (z i).base ⊆ (U : Set C))
    (hzdisj : Pairwise fun i j => Disjoint (Set.range (z i).base) (Set.range (z j).base))
    (hzε : ∀ (k : Type u) [Field k] [IsAlgClosed k] (s : Spec (CommRingCat.of k) ⟶ Spec (CommRingCat.of R)) (i : Fin M),
      (pullback.fst c s).base ⁻¹' Set.range (z i).base ⊆
        connectedComponentIn ((pullback.fst c s ⁻¹ᵁ U : (pullback c s).Opens) : Set ↥(pullback c s))
          (((sectionFibrePoint ε s).1).base (IsLocalRing.closedPoint k)))

    (B' : Fin M' → Type u) [∀ i, CommRing (B' i)] [∀ i, Algebra R (B' i)]
    [∀ i, Module.Finite R (B' i)] [∀ i, Algebra.Etale R (B' i)]
    (deg' : Fin M' → ℕ) (hdeg' : ∀ i, 1 ≤ deg' i) (φ' : ∀ i, TensorProduct R A (B' i) ≃ₐ[A] (Fin (deg' i) → A))
    (z' : ∀ i, Spec (CommRingCat.of (B' i)) ⟶ C) [∀ i, IsClosedImmersion (z' i)]
    (hz' : ∀ i, z' i ≫ c = Spec.map (CommRingCat.ofHom (algebraMap R (B' i))))
    (hz'U : ∀ i, Set.range (z' i).base ⊆ (U : Set C))
    (hz'disj : Pairwise fun i j => Disjoint (Set.range (z' i).base) (Set.range (z' j).base))
    (hzz' : ∀ i j, Disjoint (Set.range (z i).base) (Set.range (z' j).base))
    (hz'ε : ∀ (k : Type u) [Field k] [IsAlgClosed k] (s : Spec (CommRingCat.of k) ⟶ Spec (CommRingCat.of R)) (i : Fin M'),
      ¬ Smooth (pullback.snd c s) →
      (pullback.fst c s).base ⁻¹' Set.range (z' i).base ⊆
        ((pullback.fst c s ⁻¹ᵁ U : (pullback c s).Opens) : Set ↥(pullback c s)) \
          connectedComponentIn ((pullback.fst c s ⁻¹ᵁ U : (pullback c s).Opens) : Set ↥(pullback c s))
            (((sectionFibrePoint ε s).1).base (IsLocalRing.closedPoint k)))

    (r r' : ℕ) (i₀ : Fin M') (e : ℕ) (he : g + e = r + r' * deg' i₀) (hr : 2 * g + 1 ≤ r) (hr' : 2 * g + 1 ≤ r')
    (b : ℕ) (hdegb : ∀ i, deg i ≤ b) (hdeg'b : ∀ i, deg' i ≤ b)
    (hMlt : (g + 2) * (r + r' * b) * b ^ e + e < M) (hM'lt : (g + 2) * (r + r' * b) * b ^ e + e + 1 < M') :
    ∀ (Ω : Type u) [Field Ω] [IsAlgClosed Ω] [Algebra R Ω]
      (L₀ : (pullback c (SmoothProperCurve.specMap R Ω)).Modules), Scheme.Modules.IsInvertible L₀ →
      IsAlgEquivZero (pullback.snd c (SmoothProperCurve.specMap R Ω)) L₀ →

      ∀ (q : Fin (deg' i₀) → {q : Spec (CommRingCat.of Ω) ⟶ pullback c (SmoothProperCurve.specMap R Ω) //
            q ≫ pullback.snd c (SmoothProperCurve.specMap R Ω) = 𝟙 _}),
        Function.Injective (fun m => (q m).1) →
        (∀ m, ∃ ψ : B' i₀ →ₐ[R] Ω,
          (q m).1 ≫ pullback.fst c (SmoothProperCurve.specMap R Ω) = Spec.map (CommRingCat.ofHom ψ.toRingHom) ≫ z' i₀) →
      ∃ (e₁ e₂ : ℕ) (_ : e₁ + e₂ = e) (a : Fin e₁ → Fin M) (a' : Fin e₂ → Fin M'),
        Function.Injective a ∧ Function.Injective a' ∧ (∀ j, a' j ≠ i₀) ∧
        ∀ (v : Fin e₁ → {q : Spec (CommRingCat.of Ω) ⟶ pullback c (SmoothProperCurve.specMap R Ω) //
            q ≫ pullback.snd c (SmoothProperCurve.specMap R Ω) = 𝟙 _})
          (v' : Fin e₂ → {q : Spec (CommRingCat.of Ω) ⟶ pullback c (SmoothProperCurve.specMap R Ω) //
            q ≫ pullback.snd c (SmoothProperCurve.specMap R Ω) = 𝟙 _}),
          (∀ j, ∃ ψ : B (a j) →ₐ[R] Ω,
            (v j).1 ≫ pullback.fst c (SmoothProperCurve.specMap R Ω) = Spec.map (CommRingCat.ofHom ψ.toRingHom) ≫ z (a j)) →
          (∀ j, ∃ ψ : B' (a' j) →ₐ[R] Ω,
            (v' j).1 ≫ pullback.fst c (SmoothProperCurve.specMap R Ω) = Spec.map (CommRingCat.ofHom ψ.toRingHom) ≫ z' (a' j)) →
          (∀ 𝒲 : (pullback c (SmoothProperCurve.specMap R Ω)).TwoAffineOpenCover,
            Subsingleton (𝒲.sectionsOf (pullback.snd c (SmoothProperCurve.specMap R Ω))
              (L₀ ⊗ ((((sectionFibrePoint ε (SmoothProperCurve.specMap R Ω)).1.ker) ^ r * (∏ m, (q m).1.ker) ^ r').invModule ⊗
                ((∏ j, (v j).1.ker) * (∏ j, (v' j).1.ker)).module))).H1) ∧
          (∀ τ : 𝟙_ (pullback c (SmoothProperCurve.specMap R Ω)).Modules ⟶
              (L₀ ⊗ ((((sectionFibrePoint ε (SmoothProperCurve.specMap R Ω)).1.ker) ^ r * (∏ m, (q m).1.ker) ^ r').invModule ⊗
                ((∏ j, (v j).1.ker) * (∏ j, (v' j).1.ker)).module)),
            τ ≠ 0 → ((Scheme.Modules.zeroSchemeIdeal τ).support : Set ↥(pullback c (SmoothProperCurve.specMap R Ω))) ⊆
              ((pullback.fst c (SmoothProperCurve.specMap R Ω)) ⁻¹ᵁ U : Set ↥(pullback c (SmoothProperCurve.specMap R Ω)))) := by
  intro Ω _ _ _ L₀ hL₀ h0 q hqinj hq
  classical

  obtain ⟨t₀⟩ := nonempty_algHom_of_faithfullyFlat R A Ω
  have eB : ∀ i, (B i →ₐ[R] Ω) ≃ Fin (deg i) := fun i =>
    (AlgHom.nonempty_equiv_fin_of_tensorProduct_algEquiv_pi (φ i) t₀).some
  have eB'0 : ∀ i, (B' i →ₐ[R] Ω) ≃ Fin (deg' i) := fun i =>
    (AlgHom.nonempty_equiv_fin_of_tensorProduct_algEquiv_pi (φ' i) t₀).some

  have h01 := finrank_sectionsOf_unit_fibre c hH0 g (SmoothProperCurve.specMap R Ω) (hg Ω (SmoothProperCurve.specMap R Ω))
  haveI : IsReduced (pullback c (SmoothProperCurve.specMap R Ω)) := hgred Ω (SmoothProperCurve.specMap R Ω)
  haveI : IsAffineHom (pullback.fst c (SmoothProperCurve.specMap R Ω)) := MorphismProperty.pullback_fst (P := @IsAffineHom) _ _ inferInstance
  let 𝒲₀ : (pullback c (SmoothProperCurve.specMap R Ω)).TwoAffineOpenCover := comapCover (pullback.fst c (SmoothProperCurve.specMap R Ω)) 𝒱
  by_cases hsm : Smooth (pullback.snd c (SmoothProperCurve.specMap R Ω))
  ·
    haveI := hsm
    haveI : GeometricallyConnected c := geometricallyConnected_of_bijective_algebraMap_sections c hH0
    haveI : IsIntegral (pullback c (SmoothProperCurve.specMap R Ω)) := isIntegral_pullback_of_smooth c (SmoothProperCurve.specMap R Ω) hsm
    haveI : SmoothOfRelativeDimension 1 (pullback.snd c (SmoothProperCurve.specMap R Ω)) :=
      smoothOfRelativeDimension_one_snd_of_range_subset c U (SmoothProperCurve.specMap R Ω) (hgoodU Ω (SmoothProperCurve.specMap R Ω) hsm)
    haveI : ∀ i, Fintype (B i →ₐ[R] Ω) := fun i => Fintype.ofEquiv _ (eB i).symm

    let pε : {q : Spec (CommRingCat.of Ω) ⟶ pullback c (SmoothProperCurve.specMap R Ω) //
            q ≫ pullback.snd c (SmoothProperCurve.specMap R Ω) = 𝟙 _} := sectionFibrePoint ε (SmoothProperCurve.specMap R Ω)
    let w : Fin (r + deg' i₀ * r') → {q : Spec (CommRingCat.of Ω) ⟶ pullback c (SmoothProperCurve.specMap R Ω) //
            q ≫ pullback.snd c (SmoothProperCurve.specMap R Ω) = 𝟙 _} :=
      Fin.append (fun _ : Fin r => pε) (fun l => q (finProdFinEquiv.symm l).1)
    have hw : (∏ l, (w l).1.ker) = (pε.1.ker) ^ r * (∏ m, (q m).1.ker) ^ r' := by
      rw [Fin.prod_univ_add]
      simp only [w, Fin.append_left, Fin.append_right]
      rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
      congr 1
      rw [← Finset.prod_pow]
      rw [Fintype.prod_equiv finProdFinEquiv.symm (fun l => (q (finProdFinEquiv.symm l).1).1.ker)
        (fun ml : Fin (deg' i₀) × Fin r' => (q ml.1).1.ker) (fun l => rfl)]
      rw [Fintype.prod_prod_type]
      simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin]

    obtain ⟨a, ha, hgen⟩ :=
      AlgebraicGeometry.RelPicard.exists_injective_forall_finrank_H0_add_eq_and_subsingleton_H1_of_blocks_of_isAlgEquivZero_of_lt_card
        Ω (pullback.snd c (SmoothProperCurve.specMap R Ω)) g 𝒲₀ (h01 𝒲₀).2 L₀ hL₀ h0 w (fun _ : Fin 1 => (∅ : Finset _)) e
        (fun _ => by simp only [Finset.card_empty]; rw [Nat.mul_comm (deg' i₀) r']; omega)
        (fun _ => by simp only [Finset.card_empty]; rw [Nat.mul_comm (deg' i₀) r']; omega)
        (fun i => blockAll c z hz i) (fun i i' hne => disjoint_blockAll c z hz hzdisj hne) (b := b)
        (le_trans (hdeg ⟨0, by omega⟩) (hdegb _))
        (fun i => (card_blockAll_le c z hz (fun i => le_of_eq (by rw [Fintype.card_congr (eB i), Fintype.card_fin])) i).trans
          (hdegb i))
        (show 1 * (r + deg' i₀ * r') * b ^ e + e < Fintype.card (Fin M) by
          rw [Fintype.card_fin]
          have h1 : r + deg' i₀ * r' ≤ r + r' * b := by
            have := Nat.mul_le_mul_left r' (hdeg'b i₀); rw [Nat.mul_comm]; omega
          have h2 : 1 * (r + deg' i₀ * r') * b ^ e ≤ (g + 2) * (r + r' * b) * b ^ e :=
            Nat.mul_le_mul_right _ (Nat.mul_le_mul (by omega) h1)
          omega)
    refine ⟨e, 0, by simp, a, Fin.elim0, ha, Function.injective_of_subsingleton _, fun j => Fin.elim0 j, ?_⟩
    intro v v' hv hv'
    have hvblk : ∀ j, v j ∈ blockAll c z hz (a j) := fun j => by
      obtain ⟨ψ, hψ⟩ := hv j
      rw [mem_blockAll_iff]
      refine ⟨ψ, Subtype.ext (pullback.hom_ext ?_ ?_)⟩
      · rw [ptOf_fst, hψ]
      · rw [(ptOf c z hz (a j) ψ).2, (v j).2]
    have hD : (∏ j, (v j).1.ker) * ∏ p ∈ (∅ : Finset {q : Spec (CommRingCat.of Ω) ⟶ pullback c (SmoothProperCurve.specMap R Ω) //
            q ≫ pullback.snd c (SmoothProperCurve.specMap R Ω) = 𝟙 _}), p.1.ker =
        (∏ j, (v j).1.ker) * ∏ j, (v' j).1.ker := by
      rw [Finset.prod_empty]
      congr 1
    refine ⟨fun 𝒲 => ?_, fun τ _ y _ => hgoodU Ω (SmoothProperCurve.specMap R Ω) hsm ⟨y, rfl⟩⟩
    have hsp := (hgen v hvblk 0 𝒲).2
    rw [hw, hD] at hsp
    exact hsp
  ·

    let f : Fin (deg' i₀) → (B' i₀ →ₐ[R] Ω) := fun m => (hq m).choose
    have hf : ∀ m, (q m).1 ≫ pullback.fst c (SmoothProperCurve.specMap R Ω) =
        Spec.map (CommRingCat.ofHom (f m).toRingHom) ≫ z' i₀ := fun m => (hq m).choose_spec
    haveI : Fintype (B' i₀ →ₐ[R] Ω) := Fintype.ofEquiv _ (eB'0 i₀).symm
    have hfinj : Function.Injective f := by
      intro m m' h
      apply hqinj
      show (q m).1 = (q m').1
      apply pullback.hom_ext
      · rw [hf, hf, h]
      · rw [(q m).2, (q m').2]
    have hfbij : Function.Bijective f := by
      rw [Fintype.bijective_iff_injective_and_card]
      exact ⟨hfinj, by rw [Fintype.card_fin, Fintype.card_congr (eB'0 i₀), Fintype.card_fin]⟩
    let eBi₀ : (B' i₀ →ₐ[R] Ω) ≃ Fin (deg' i₀) := (Equiv.ofBijective f hfbij).symm
    let eB' : ∀ i, (B' i →ₐ[R] Ω) ≃ Fin (deg' i) := fun i =>
      if h : i = i₀ then h ▸ eBi₀ else eB'0 i
    have heB' : eB' i₀ = eBi₀ := by simp [eB']
    have hq' : ∀ m, (q m).1 ≫ pullback.fst c (SmoothProperCurve.specMap R Ω) =
        Spec.map (CommRingCat.ofHom ((eB' i₀).symm m).toRingHom) ≫ z' i₀ := fun m => by
      rw [heB']
      exact hf m
    exact
      AlgebraicGeometry.RelPicard.exists_split_injective_forall_subsingleton_H1_and_support_subset_of_twoSidedBlocks_of_twoGluedSmoothCurveDegeneration
        R c ε U hεA B B' z z' hz hz' hzU hz'U hzdisj hz'disj hzz' deg hdeg deg' hdeg' hdegb hdeg'b g r r' e i₀ hr hr' he
        hMlt hM'lt Ω eB eB' hsm 𝒲₀ q hq' hbad (hzε Ω (SmoothProperCurve.specMap R Ω)) (fun i => hz'ε Ω (SmoothProperCurve.specMap R Ω) i hsm)
        (fun 𝒲 => (h01 𝒲).1) (fun 𝒲 => (h01 𝒲).2) L₀ hL₀ h0

end S_AlgebraicGeometry_RelPicard_exists_split_injective_forall_subsingleton_H1_and_support_subset_of_twoSidedBlocks_of_bijective_sections
end P2MW
export P2MW.S_AlgebraicGeometry_RelPicard_exists_split_injective_forall_subsingleton_H1_and_support_subset_of_twoSidedBlocks_of_bijective_sections (solution)
