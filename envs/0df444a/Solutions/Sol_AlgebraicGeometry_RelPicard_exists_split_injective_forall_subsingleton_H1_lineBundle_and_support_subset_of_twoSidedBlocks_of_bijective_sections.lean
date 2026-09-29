-- Prove2me | solution 1 for AlgebraicGeometry.RelPicard.exists_split_injective_forall_subsingleton_H1_lineBundle_and_support_subset_of_twoSidedBlocks_of_bijective_sections
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:03.589526+00:00
-- url     : https://prove2.me/submissions/1e4c1d5e-cce0-5429-affe-a69869423ba2

import Mathlib
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
import Theorems.Thm_AlgebraicGeometry_RelPicard_exists_split_injective_forall_subsingleton_H1_and_support_subset_of_twoSidedBlocks_of_bijective_sections
import Theorems.Thm_AlgebraicGeometry_RelEffCartierDiv_nonempty_lineBundle_pullbackAlong_iso_invModule_pow_ker_mul_pow_prod_ker
import Theorems.Thm_AlgHom_nonempty_equiv_fin_of_tensorProduct_algEquiv_pi
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_zeroSchemeIdeal_comp_eq_of_isIso
import Theorems.Thm_AlgebraicGeometry_Scheme_TwoAffineOpenCover_exists_linearEquiv_sectionsOf_of_iso
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_RelPicard_exists_split_injective_forall_subsingleton_H1_lineBundle_and_support_subset_of_twoSidedBlocks_of_bijective_sections
p2m_attr_erase "instance" "AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instNeg AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instSMulInt AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instAddCommGroup AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instAdd AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instSub AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instModuleCarrierObjOppositeOpensCarrierCarrierCommRingCatPresheafOpOpensTop AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instSMulCarrierObjOppositeOpensCarrierCarrierCommRingCatPresheafOpOpensTop AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instSMulNat AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instZero AlgebraicGeometry.OModulePresheaf.isScalarTower AlgebraicGeometry.Scheme.OrderedAffineCover.instLinearOrder AlgebraicGeometry.OModulePresheaf.module AlgebraicGeometry.Scheme.OrderedAffineCover.instFintype AlgebraicGeometry.Scheme.OrderedAffineCover.instFintypeIdx AlgebraicGeometry.OModulePresheaf.addCommGroup AlgebraicGeometry.Scheme.OrderedAffineCover.instDecidableEqIdx AlgebraicGeometry.OModulePresheaf.moduleSections AlgebraicGeometry.OModulePresheaf.instSubsingletonObjZero AlgebraicGeometry.OModulePresheaf.Leray.relAltC_scalarTower AlgebraicGeometry.OModulePresheaf.Leray.ker_relAltd_modΓ AlgebraicGeometry.OModulePresheaf.Leray.relAltC_modΓ AlgebraicGeometry.OModulePresheaf.Leray.biC_abGrp AlgebraicGeometry.OModulePresheaf.Leray.relAltH_modΓ AlgebraicGeometry.OModulePresheaf.Leray.ker_relAltd_smul AlgebraicGeometry.OModulePresheaf.Leray.relAltH_scalarTower AlgebraicGeometry.OModulePresheaf.Leray.relAltH_smul AlgebraicGeometry.OModulePresheaf.Leray.biC_module AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instDecidableEqIdx AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instFintype AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instLinearOrder AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instFintypeIdx DoubleComplex.instModuleE₂I DoubleComplex.Bounded.modR DoubleComplex.instModuleE₂II DoubleComplex.instAddCommGroupE₂II DoubleComplex.Bounded.abGrp DoubleComplex.instAddCommGroupE₂I AlgebraicGeometry.ChowDatum.hι_closed AlgebraicGeometry.ChowDatumProj.hιN_closed AlgebraicGeometry.ChowDatumProj.hp_proper"
p2m_attr_erase "instance" "AlgebraicGeometry.ChowDatum.hp_isoU AlgebraicGeometry.ChowDatum.hp_proper AlgebraicGeometry.ProjSpace.algebraAway AlgebraicGeometry.ProjSpace.instIsProperProdOverπ AlgebraicGeometry.ChowDatumProj.hp_isoU AlgebraicGeometry.ProjSpace.isProper_π AlgebraicGeometry.ProjSpace.finiteType_mvPolynomial ProjSpaceCech.GradedModule.H.module ProjSpaceCech.GradedModule.H.addCommGroup ProjSpaceCech.GradedModule.sec.instAdd ProjSpaceCech.GradedModule.sec.instNeg ProjSpaceCech.GradedModule.acg ProjSpaceCech.GradedModule.Frac.setoid ProjSpaceCech.GradedModule.modR ProjSpaceCech.GradedModule.sec.instModule ProjSpaceCech.GradedModule.sec.instAddCommGroup ProjSpaceCech.GradedModule.sec.instZero ProjSpaceCech.GradedModule.Presentation.fJ ProjSpaceCech.GradedModule.sec.instSMul ProjSpaceCech.Twist.H.module ProjSpaceCech.Idx.instFintype ProjSpaceCech.Twist.H.addCommGroup ProjSpaceCech.Idx.instDecidableEq ProjSpaceCech.Twist.Mon.instDecidableEq ProjSpaceCech.Twist.cochain.instAddCommGroup ProjSpaceCech.Twist.cochain.instModule PresheafOfModules.PullbackMonoidal.pullback_monoidal PresheafOfModules.PullbackMonoidal.isIso_δ PresheafOfModules.pushforward_laxMonoidal PresheafOfModules.PullbackMonoidal.isIso_η PresheafOfModules.free_monoidal PresheafOfModules.restrictScalars_laxMonoidal PresheafOfModules.PullbackMonoidal.isIso_δ_gS PresheafOfModules.pullback_oplaxMonoidal PresheafOfModules.PullbackMonoidal.instPreservesColimitsOfSizeCompOppositeCommRingCatRingCatForget₂RingHomCarrierCarrierPb PresheafOfModules.pullback_monoidal' AlgebraicGeometry.Scheme.Modules.preservesBinaryProducts_opensMap AlgebraicGeometry.Scheme.Modules.pullback_monoidal AlgebraicGeometry.Scheme.Modules.sheafify_isLocalization' AlgebraicGeometry.Scheme.Modules.preservesTerminal_opensMap"
p2m_attr_erase "instance" "AlgebraicGeometry.Scheme.Modules.pullback₀_monoidal AlgebraicGeometry.Scheme.Modules.preservesFiniteProducts_opensMap AlgebraicGeometry.Scheme.Modules.instLiftingPresheafOfModulesSheafifyPresheafWOpensCarrierCarrierCommRingCatGrothendieckTopologyObjFunctorOppositeIsSheafSheafCompPullback₀Pullback SheafOfModules.isIso_ihomModelToIhom AlgebraicCurve.IsCurveOver.instNontrivialKaehler AlgebraicCurve.IsCurveOver.instFreeKaehler AlgebraicCurve.IsCurveOver.toHasPrincipalDivisors AlgebraicCurve.IsCurveOver.instFiniteResidue AlgebraicCurve.instFundamentalIdentityOfSumRamificationInertia AlgebraicCurve.Place.instIsScalarTowerResidueFieldRestrictPushforward AlgebraicCurve.Place.instAlgebraResidueFieldRestrictPushforward AlgebraicCurve.Place.instIsLocalHomRestrictInclusion AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.SemilinearAut.instDistribMulActionSubtypeProdRingAutMemSubgroupPic0 AlgebraicCurve.SemilinearAut.instDistribMulActionSubtypeProdRingAutMemSubgroupDivisor AlgebraicCurve.Pic0.instModuleZModTorsion AlgebraicCurve.SemilinearAut.instSMulSubtypeProdRingAutMemSubgroupPlace AlgebraicCurve.SemilinearAut.instDistribMulActionTorsion AlgebraicCurve.SemilinearAut.instSMulSubtypeProdRingAutMemSubgroupPic0 AlgebraicCurve.SemilinearAut.instSMulTorsion AlgebraicCurve.SemilinearAut.instMulActionSubtypeProdRingAutMemSubgroupPlace AlgebraicCurve.SemilinearAut.instSMulCommClassZModTorsion AlgebraicCurve.SemilinearAut.instMulSemiringActionSubtypeProdRingAutMemSubgroup instDecEqAlgebraicClosureRat WeierstrassCurve.Affine.Point.instDistribMulActionAlgEquiv WeierstrassCurve.Affine.Point.instModuleZModTorsionBy WeierstrassCurve.Affine.Point.instSMulTorsionBy WeierstrassCurve.Affine.Point.instDistribMulActionTorsionBy WeierstrassCurve.Affine.Point.instSMulAlgEquiv WeierstrassCurve.Affine.Point.instSMulCommClassAlgEquivZModTorsionBy AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions AlgebraicCurve.instHasLocalResidue_of_hasCanonicalLocalResidueK AlgebraicCurve.instHasCanonicalLocalResidueK_of_hasCanonicalLocalResidueKStar AlgebraicCurve.Place.kw_ffgc_finiteDimensional_adicCompletion"
p2m_attr_erase "instance" "instAlgebraSubtypeMemValuationSubring_definitions AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersIntegersCompletion ModularCurve.KwF4gRRTate.instAlgebraKAdicCompletionIntegers AlgebraicCurve.Place.kw_ffgc_continuousSMul_adicCompletionComap AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersCompletionCompletion IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions AlgebraicCurve.instHasCanonicalLocalResidueK AlgebraicCurve.Place.instAlgebra_restrictResidueField AlgebraicCurve.Place.instIsScalarTower_restrictResidueField AlgebraicCurve.instHasLocalResidue AlgebraicCurve.HasSeparableResidue.of_perfectField_of_isCurveOver AlgebraicCurve.HasSeparableResidue.of_perfectField AlgebraicCurve.Place.instIsLocalHom_restrictSubringHom AlgebraicCurve.instHasCanonicalLocalResidueKStar ModularCurve.KwNo6Pin.isLocalRing_completion"
p2m_attr_erase "simp" "AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.sub_app AlgebraicGeometry.Scheme.IdealSheafData.sres_sresTop AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.add_app AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.mk.sizeOf_spec AlgebraicGeometry.Scheme.IdealSheafData.coe_resLE AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.smul_app AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.coe_ofLE_app AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.ideal_range AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.zero_app AlgebraicGeometry.Scheme.IdealSheafData.sres_sres AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.comp_app AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.neg_app AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.id_app AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.coe_mulRight_app AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.nsmul_app AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.mk.injEq AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.zsmul_app AlgebraicGeometry.Scheme.OrderedAffineCover.mk.injEq AlgebraicGeometry.OModulePresheaf.mk.sizeOf_spec AlgebraicGeometry.Scheme.OrderedAffineCover.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.mk.injEq AlgebraicGeometry.Scheme.Modules.pullbackLocalSection_neg AlgebraicGeometry.Scheme.Modules.pullbackLocalSection_zero AlgebraicGeometry.Scheme.Modules.pullbackLocalSection_sub AlgebraicGeometry.Scheme.Modules.pullbackLocalSection_add AlgebraicGeometry.OModulePresheaf.prod_obj AlgebraicGeometry.OModulePresheaf.restrOpen_obj AlgebraicGeometry.OModulePresheaf.DevissageStep.mk.injEq AlgebraicGeometry.OModulePresheaf.pushforward_obj AlgebraicGeometry.OModulePresheaf.im_obj AlgebraicGeometry.OModulePresheaf.pow_obj AlgebraicGeometry.OModulePresheaf.fstHom_app AlgebraicGeometry.OModulePresheaf.ker_obj AlgebraicGeometry.OModulePresheaf.coker_obj AlgebraicGeometry.OModulePresheaf.DevissageStep.mk.sizeOf_spec AlgebraicGeometry.Scheme.OrderedAffineCover.preimage_U AlgebraicGeometry.OModulePresheaf.sndHom_app AlgebraicGeometry.OModulePresheaf.Hom.mk.injEq AlgebraicGeometry.OModulePresheaf.Hom.id_app AlgebraicGeometry.OModulePresheaf.AffHom.appSections_apply"
p2m_attr_erase "simp" "AlgebraicGeometry.OModulePresheaf.AffHom.comp_app AlgebraicGeometry.OModulePresheaf.AffSES.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.AffHom.kerMap_coe AlgebraicGeometry.OModulePresheaf.AffHom.id_app AlgebraicGeometry.OModulePresheaf.Hom.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.Hom.toAffHom_app AlgebraicGeometry.OModulePresheaf.SES.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.AffHom.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.Hom.comp_app AlgebraicGeometry.OModulePresheaf.SES.mk.injEq AlgebraicGeometry.OModulePresheaf.AffHom.mk.injEq AlgebraicGeometry.OModulePresheaf.Hom.appSections_apply AlgebraicGeometry.OModulePresheaf.AffSES.mk.injEq AlgebraicGeometry.OModulePresheaf.Leray.restrictToPreimage_U AlgebraicGeometry.Scheme.OrderedAffineCover.toCoverOf_U AlgebraicGeometry.Scheme.OrderedAffineCoverOf.mk.sizeOf_spec AlgebraicGeometry.Scheme.OrderedAffineCoverOf.mk.injEq AlgebraicGeometry.Scheme.OrderedAffineCover.restrict_U DoubleComplex.Bounded.mk.injEq DoubleComplex.Bounded.mk.sizeOf_spec DoubleComplex.Convergence.mk.injEq DoubleComplex.Convergence.mk.sizeOf_spec DoubleComplex.SubQuot.mk.sizeOf_spec DoubleComplex.SubQuot.mk.injEq AlgebraicGeometry.ChowDatumProj.mk.sizeOf_spec AlgebraicGeometry.ChowDatum.mk.sizeOf_spec AlgebraicGeometry.ChowDatumProj.mk.injEq AlgebraicGeometry.ChowDatum.mk.injEq ProjSpaceCech.GradedModule.mk.injEq ProjSpaceCech.GradedModule.mk.sizeOf_spec ProjSpaceCech.GradedModule.Frac.mk.sizeOf_spec ProjSpaceCech.GradedModule.Presentation.mk.injEq ProjSpaceCech.GradedModule.Frac.mk.injEq ProjSpaceCech.GradedModule.Presentation.mk.sizeOf_spec ProjSpaceCech.GradedModule.Hom.shift_toLinearMap ProjSpaceCech.GradedModule.Hom.mk.sizeOf_spec ProjSpaceCech.GradedModule.Hom.mk.injEq PresheafOfModules.freeεIso_hom_app PresheafOfModules.freeμIso_hom_app AlgebraicGeometry.Scheme.Modules.tensorPow_zero"
p2m_attr_erase "simp" "AlgebraicGeometry.Scheme.Modules.tensorPow_succ AlgebraicGeometry.Scheme.Modules.tensorSections_zero_right AlgebraicGeometry.Scheme.Modules.map_unitSection AlgebraicGeometry.Scheme.Modules.tensorSectionsBilin_apply AlgebraicGeometry.Scheme.Modules.tensorPowSection_zero AlgebraicGeometry.Scheme.Modules.tensorSections_zero_left PresheafOfModules.InternalHom.IsSheafAux.appAt_toPresheafHom SheafOfModules.ihomSectionsEquivFamily_unit AlgebraicGeometry.Scheme.Modules.restrictHomEquivFamily_apply SheafOfModules.ihomEval_unit_app AlgebraicGeometry.Scheme.Modules.ihomEval_zero_right AlgebraicGeometry.Scheme.Modules.ihomEval_zero_left AlgebraicGeometry.Scheme.Modules.homOfFamily_app_apply SheafOfModules.unit_ihomSectionsEquivFamily AlgebraicGeometry.Scheme.Modules.familyOfHom_app AlgebraicGeometry.Scheme.Modules.restrictUnitIso_hom_app_apply AlgebraicGeometry.Scheme.Modules.restrictUnitIso_inv_app_apply AlgebraicGeometry.Scheme.Modules.restrictHomOfFamily_app_apply AlgebraicGeometry.Scheme.Modules.restrictHomEquivFamily_symm_apply TwoChartCech.Mumford.dK_apply TwoChartCech.Mumford.ι0_apply TwoChartCech.Mumford.ι1_apply TwoChartCech.KerCoprod.dK_apply TwoChartCech.KerCoprod.ι1_apply TwoChartCech.KerCoprod.ι0_apply AlgebraicGeometry.tilde.functorCompPullbackSpecIso_app AlgebraicCurve.Divisor.mapRestrict_single AlgebraicCurve.Divisor.pushforward_single AlgebraicCurve.Place.coe_restrictInclusion AlgebraicCurve.Place.mem_fiber AlgebraicCurve.Place.restrict_toValuationSubring AlgebraicCurve.Divisor.degree_pushforward AlgebraicCurve.Place.restrictResidueMap_residue AlgebraicCurve.Pic0.coe_pushforwardDegZeroHom AlgebraicCurve.Pic0.coe_pullbackDegZeroHom AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal"
p2m_attr_erase "simp" "AlgebraicCurve.IsFrobeniusEndo.frobNormRingHom_apply ModularCurve.frobeniusPushforwardGeomLevelPic0_mk ModularCurve.coe_frobeniusGeomLevelEquiv_apply ModularCurve.coe_frobeniusPushforwardGeomLevelDegZero ModularCurve.heckeFibreGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusGeomLevel_apply_coe ModularCurve.frobeniusPullbackGeomLevelPic0OfIsCurveOver_mk ModularCurve.coe_heckeFibreGeomLevelDegZero ModularCurve.coe_frobeniusPullbackGeomLevelDegZero ModularCurve.frobeniusPullbackGeomLevelPic0_mk ModularCurve.frobeniusPullbackGeomLevel_single ModularCurve.heckeFibreGeomLevelPic0_mk ModularCurve.frobeniusPushforwardGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusPushforwardGeomLevel_single ModularCurve.qExpandAlgC_apply AlgebraicCurve.Place.congrEquiv_symm_apply AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply AlgebraicCurve.RationalFunctionField.deg_placeOfPoint AlgebraicCurve.Divisor.degree_pushforwardAlong AlgebraicCurve.Pic0.coe_degZeroCorrespondence AlgebraicCurve.Place.mem_fiberAlong AlgebraicCurve.SemilinearAut.toRingAut_inv AlgebraicCurve.SemilinearAut.smul_def AlgebraicCurve.SemilinearAut.smul_single AlgebraicCurve.SemilinearAut.smul_toValuationSubring AlgebraicCurve.SemilinearAut.baseAut_inv AlgebraicCurve.SemilinearAut.baseAut_ofAlgAut AlgebraicCurve.SemilinearAut.toRingAut_ofAlgAut AlgebraicCurve.SemilinearAut.torsionRep_apply AlgebraicCurve.SemilinearAut.toRingAut_one AlgebraicCurve.SemilinearAut.deg_smul AlgebraicCurve.SemilinearAut.degree_smul AlgebraicCurve.SemilinearAut.coe_degZeroSMulHom AlgebraicCurve.SemilinearAut.baseAut_mul AlgebraicCurve.SemilinearAut.coe_smulValuationSubringEquiv_apply AlgebraicCurve.SemilinearAut.baseAut_one AlgebraicCurve.SemilinearAut.ofAlgAut_smul"
p2m_attr_erase "simp" "AlgebraicCurve.SemilinearAut.coe_torsion_smul AlgebraicCurve.SemilinearAut.toRingAut_mul AlgebraicCurve.coe_frobeniusPushforwardDegZero AlgebraicCurve.IsFrobeniusEndo.coe_frobeniusPullbackDegZero ModularCurve.jqNModC_one ModularCurve.qExpand_coeff_mul ModularCurve.qExpandₐ_apply ModularCurve.jqN_one ModularCurve.qExpand_single ModularCurve.dedekindPsi_one ModularCurve.ModularPolynomialData.mk.sizeOf_spec ModularCurve.evalAtJ_X ModularCurve.ModularPolynomialData.mk.injEq ModularCurve.constantCoeff_jNum ModularCurve.constantCoeff_eisenstein4 ModularCurve.qExpand_C ModularCurve.coeff_jq_neg_one ModularCurve.constantCoeff_jNumQ ModularCurve.reduceModBivar_C_X ModularCurve.laurentMap_coeff ModularCurve.reduceModBivar_X ModularCurve.laurentMap_single ModularCurve.evalAtJInt_X ModularCurve.evalAtJMod_X ModularCurve.jqNMod_one ModularCurve.aeval_heckeGen ModularCurve.coe_mTorsionGaloisRep_apply ModularCurve.eisensteinSystem_of_dvd ModularCurve.eisensteinSystem_of_not_dvd FreyPackage.mk.sizeOf_spec FreyPackage.mk.injEq WeierstrassCurve.Affine.Point.galoisRepModuleEnd_apply AlgebraicCurve.RationalFunctionField.placeInfty_toValuationSubring AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none AlgebraicCurve.Divisor.evalFun_zero AlgebraicCurve.Place.evalAt_one AlgebraicCurve.Place.differentialCoeff_zero"
p2m_attr_erase "simp" "AlgebraicCurve.Place.differentialCoeff_dCoord AlgebraicCurve.TranscendenceTower.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.injEq AlgebraicCurve.TranscendenceTower.mk.injEq AlgebraicCurve.PoleDivisorPackage.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.sizeOf_spec AlgebraicCurve.PoleDivisorPackage.mk.injEq AlgebraicCurve.coe_cechH0Equiv_apply AlgebraicCurve.cechH1ToH1_mk AlgebraicCurve.lSpaceOn_univ AlgebraicCurve.lSpaceOn_empty AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.sizeOf_spec AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.injEq AlgebraicCurve.adeleSingle_coe AlgebraicCurve.kaehlerResidueTermKFam_apply AlgebraicCurve.Place.LocalResidueData.mk.injEq AlgebraicCurve.Place.LocalResidueData.mk.sizeOf_spec AlgebraicCurve.Place.kw_ffgc_adicCompletionComapIntegers_coe AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.sizeOf_spec AlgebraicCurve.Place.mem_simplePoleSubmodule AlgebraicCurve.Place.coe_uniformizerSubring ModularCurve.Lg37.Lg37CompletionSection.mk.injEq AlgebraicCurve.Place.CoefficientFieldSection.mk.injEq AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.injEq ModularCurve.Lg37.Lg37CompletionSection.mk.sizeOf_spec AlgebraicCurve.Place.CoefficientFieldSection.mk.sizeOf_spec AlgebraicCurve.Place.poleSubmodule_one AlgebraicCurve.Place.mem_poleSubmodule RegularLocalRingQuotientAscent.dualNumberFst_apply"

set_option autoImplicit false

universe u

p2m_open "CategoryTheory CategoryTheory.Limits Opposite CategoryTheory.MonoidalCategory AlgebraicGeometry P2MW.S_AlgebraicGeometry_RelPicard_exists_split_injective_forall_subsingleton_H1_lineBundle_and_support_subset_of_twoSidedBlocks_of_bijective_sections.AlgebraicGeometry AlgebraicGeometry.RelPicard NeronModelInfra"

p2m_open "AlgebraicGeometry.SmoothProperCurve AlgebraicCurve~genus"

noncomputable section

namespace AlgebraicGeometry
p2m_export "AlgebraicGeometry" "Spec.map_comp Spec.map_preimage SmoothOfRelativeDimension IsProper IsClosedImmersion.of_comp GeometricallyIntegral Flat.SpecMap_iff IsFinite Spec IsIntegral Spec.map Scheme Smooth IsOpenImmersion Spec.map_injective Flat IsClosedImmersion IsReduced Spec.preimage HasRingHomProperty.Spec_iff Etale IsFinite.SpecMap_iff Scheme.Modules.pullbackId Scheme.Modules HasRingHomProperty geometrically Scheme.Modules.IsInvertible RelEffCartierDiv mapOnProdOver mapOnProdOver_fst mapOnProdOver_snd Scheme.TwoAffineOpenCover Scheme.TwoAffineOpenCover.specMap Scheme.TwoAffineOpenCover.algebraOfHom Scheme.Modules.zeroSchemeIdeal SmoothProperCurve.specMap RelPicard.exists_split_injective_forall_subsingleton_H1_and_support_subset_of_twoSidedBlocks_of_bijective_sections RelEffCartierDiv.nonempty_lineBundle_pullbackAlong_iso_invModule_pow_ker_mul_pow_prod_ker Scheme.Modules.zeroSchemeIdeal_comp_eq_of_isIso Scheme.TwoAffineOpenCover.exists_linearEquiv_sectionsOf_of_iso"
namespace N11Impl
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

theorem cover_ext {X : Scheme.{u}} {𝒱 𝒱' : X.TwoAffineOpenCover}
    (h0 : 𝒱.U0 = 𝒱'.U0) (h1 : 𝒱.U1 = 𝒱'.U1) : 𝒱 = 𝒱' := by
  cases 𝒱; cases 𝒱'; cases h0; cases h1; rfl

theorem H1_equiv_of_iso {k : Type u} [Field k] {X : Scheme.{u}} (x : X ⟶ Spec (CommRingCat.of k))
    (𝒱 : X.TwoAffineOpenCover) {M M' : X.Modules} (e : M ≅ M') :
    Nonempty ((𝒱.sectionsOf x M).H1 ≃ₗ[k] (𝒱.sectionsOf x M').H1) := by
  obtain ⟨𝒱₂, h0, h1, -, ⟨e1⟩⟩ :=
    Scheme.TwoAffineOpenCover.exists_linearEquiv_sectionsOf_of_iso x x (Iso.refl X) (Category.id_comp x)
      𝒱 M' M (e ≪≫ ((Scheme.Modules.pullbackId X).app M').symm)
  obtain rfl : 𝒱₂ = 𝒱 := cover_ext h0 h1
  exact ⟨e1⟩

end AlgebraicGeometry.N11Impl

end

open AlgebraicGeometry.N11Impl in
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
    (hMlt : (g + 2) * (r + r' * b) * b ^ e + e < M) (hM'lt : (g + 2) * (r + r' * b) * b ^ e + e + 1 < M')

    (ρ : ℕ) (hρ : ρ = r + r' * deg' i₀)
    (E : RelEffCartierDiv c ρ (𝟙 (Spec (CommRingCat.of R))))
    (hEI : E.I = (sectionIdeal c ε (𝟙 (Spec (CommRingCat.of R)))) ^ r *
      ((pullback.lift (z' i₀) (Spec.map (CommRingCat.ofHom (algebraMap R (B' i₀)))) (by rw [Category.comp_id]; exact hz' i₀)).ker) ^ r') :
    ∀ (Ω : Type u) [Field Ω] [IsAlgClosed Ω] [Algebra R Ω]
      (L₀ : (pullback c (SmoothProperCurve.specMap R Ω)).Modules), Scheme.Modules.IsInvertible L₀ →
      IsAlgEquivZero (pullback.snd c (SmoothProperCurve.specMap R Ω)) L₀ →
      ∃ (e₁ e₂ : ℕ) (_ : e₁ + e₂ = e) (a : Fin e₁ → Fin M) (a' : Fin e₂ → Fin M'),
        Function.Injective a ∧ Function.Injective a' ∧
        ∀ (v : Fin e₁ → {q : Spec (CommRingCat.of Ω) ⟶ pullback c (SmoothProperCurve.specMap R Ω) //
            q ≫ pullback.snd c (SmoothProperCurve.specMap R Ω) = 𝟙 _})
          (v' : Fin e₂ → {q : Spec (CommRingCat.of Ω) ⟶ pullback c (SmoothProperCurve.specMap R Ω) //
            q ≫ pullback.snd c (SmoothProperCurve.specMap R Ω) = 𝟙 _}),
          (∀ j, ∃ ψ : B (a j) →ₐ[R] Ω,
            (v j).1 ≫ pullback.fst c (SmoothProperCurve.specMap R Ω) =
              Spec.map (CommRingCat.ofHom ψ.toRingHom) ≫ z (a j)) →
          (∀ j, ∃ ψ : B' (a' j) →ₐ[R] Ω,
            (v' j).1 ≫ pullback.fst c (SmoothProperCurve.specMap R Ω) =
              Spec.map (CommRingCat.ofHom ψ.toRingHom) ≫ z' (a' j)) →
          (∀ 𝒲 : (pullback c (SmoothProperCurve.specMap R Ω)).TwoAffineOpenCover,
            Subsingleton (𝒲.sectionsOf (pullback.snd c (SmoothProperCurve.specMap R Ω))
              (L₀ ⊗ ((E.pullbackAlong (SmoothProperCurve.specMap R Ω) (Category.comp_id _)).lineBundle ⊗
                ((∏ j, (v j).1.ker) * (∏ j, (v' j).1.ker)).module))).H1) ∧
          (∀ τ : 𝟙_ (pullback c (SmoothProperCurve.specMap R Ω)).Modules ⟶
              (L₀ ⊗ ((E.pullbackAlong (SmoothProperCurve.specMap R Ω) (Category.comp_id _)).lineBundle ⊗
                ((∏ j, (v j).1.ker) * (∏ j, (v' j).1.ker)).module)),
            τ ≠ 0 → ((Scheme.Modules.zeroSchemeIdeal τ).support : Set ↥(pullback c (SmoothProperCurve.specMap R Ω))) ⊆
              ((pullback.fst c (SmoothProperCurve.specMap R Ω)) ⁻¹ᵁ U : Set ↥(pullback c (SmoothProperCurve.specMap R Ω)))) := by
  intro Ω _ _ _ L₀ hL₀ h0
  classical

  obtain ⟨t₀⟩ := nonempty_algHom_of_faithfullyFlat R A Ω
  obtain ⟨eB'⟩ := AlgHom.nonempty_equiv_fin_of_tensorProduct_algEquiv_pi (φ' i₀) t₀
  let ptOf : (B' i₀ →ₐ[R] Ω) → {q : Spec (CommRingCat.of Ω) ⟶ pullback c (SmoothProperCurve.specMap R Ω) //
            q ≫ pullback.snd c (SmoothProperCurve.specMap R Ω) = 𝟙 _} := fun ψ =>
    ⟨pullback.lift (Spec.map (CommRingCat.ofHom ψ.toRingHom) ≫ z' i₀) (𝟙 _) (by
        rw [Category.assoc, hz' i₀, Category.id_comp]
        show Spec.map _ ≫ Spec.map _ = Spec.map _
        rw [← Spec.map_comp, ← CommRingCat.ofHom_comp, AlgHom.toRingHom_eq_coe, AlgHom.comp_algebraMap]),
      pullback.lift_snd _ _ _⟩
  have ptOf_fst : ∀ ψ, (ptOf ψ).1 ≫ pullback.fst c (SmoothProperCurve.specMap R Ω) = Spec.map (CommRingCat.ofHom ψ.toRingHom) ≫ z' i₀ :=
    fun ψ => pullback.lift_fst _ _ _
  let q : Fin (deg' i₀) → {q : Spec (CommRingCat.of Ω) ⟶ pullback c (SmoothProperCurve.specMap R Ω) //
            q ≫ pullback.snd c (SmoothProperCurve.specMap R Ω) = 𝟙 _} := fun m => ptOf (eB'.symm m)
  have hqinj : Function.Injective (fun m => (q m).1) := by
    intro m m' h
    have h1 : Spec.map (CommRingCat.ofHom (eB'.symm m).toRingHom) ≫ z' i₀ =
        Spec.map (CommRingCat.ofHom (eB'.symm m').toRingHom) ≫ z' i₀ := by
      rw [← ptOf_fst, ← ptOf_fst]; exact congrArg (· ≫ pullback.fst c (SmoothProperCurve.specMap R Ω)) h
    have h2 := Spec.map_injective ((cancel_mono (z' i₀)).mp h1)
    have h3 : (eB'.symm m).toRingHom = (eB'.symm m').toRingHom := by
      have := congrArg CommRingCat.Hom.hom h2; simpa using this
    exact eB'.symm.injective (AlgHom.ext fun b => by simpa using congrArg (fun f : B' i₀ →+* Ω => f b) h3)
  have hq : ∀ m, ∃ ψ : B' i₀ →ₐ[R] Ω,
      (q m).1 ≫ pullback.fst c (SmoothProperCurve.specMap R Ω) = Spec.map (CommRingCat.ofHom ψ.toRingHom) ≫ z' i₀ :=
    fun m => ⟨eB'.symm m, ptOf_fst _⟩

  obtain ⟨e₁, e₂, he₁₂, a, a', ha, ha', -, H⟩ :=
    AlgebraicGeometry.RelPicard.exists_split_injective_forall_subsingleton_H1_and_support_subset_of_twoSidedBlocks_of_bijective_sections
      c 𝒱 hH0 ε U hεA hgoodU hgred g hg hbad A B deg hdeg φ z hz hzU hzdisj hzε B' deg' hdeg' φ' z' hz' hz'U hz'disj hzz' hz'ε
      r r' i₀ e he hr hr' b hdegb hdeg'b hMlt hM'lt Ω L₀ hL₀ h0 q hqinj hq
  refine ⟨e₁, e₂, he₁₂, a, a', ha, ha', fun v v' hv hv' => ?_⟩
  obtain ⟨H1, H2⟩ := H v v' hv hv'

  let W : Spec (CommRingCat.of (B' i₀)) ⟶ pullback c (𝟙 (Spec (CommRingCat.of R))) :=
    pullback.lift (z' i₀) (Spec.map (CommRingCat.ofHom (algebraMap R (B' i₀))))
      ((hz' i₀).trans (Category.comp_id _).symm)
  haveI : IsClosedImmersion W := by
    have : W ≫ pullback.fst c (𝟙 _) = z' i₀ := pullback.lift_fst _ _ _
    haveI : IsClosedImmersion (W ≫ pullback.fst c (𝟙 (Spec (CommRingCat.of R)))) := by rw [this]; infer_instance
    exact IsClosedImmersion.of_comp W (pullback.fst c (𝟙 _))
  have hWsnd : W ≫ pullback.snd c (𝟙 _) = Spec.map (CommRingCat.ofHom (algebraMap R (B' i₀))) := pullback.lift_snd _ _ _
  haveI : IsFinite (W ≫ pullback.snd c (𝟙 _)) := by
    rw [hWsnd, IsFinite.SpecMap_iff]
    exact RingHom.finite_algebraMap.mpr inferInstance
  haveI : Flat (W ≫ pullback.snd c (𝟙 _)) := by
    rw [hWsnd, Flat.SpecMap_iff]
    exact RingHom.flat_algebraMap_iff.mpr inferInstance
  haveI : Etale (W ≫ pullback.snd c (𝟙 _)) := by
    rw [hWsnd, HasRingHomProperty.Spec_iff (P := @Etale)]
    exact RingHom.etale_algebraMap.mpr inferInstance
  have hqW : ∀ m, ∃ y : Spec (CommRingCat.of Ω) ⟶ Spec (CommRingCat.of (B' i₀)),
      (q m).1 ≫ mapOnProdOver c (SmoothProperCurve.specMap R Ω) (Category.comp_id _) = y ≫ W := by
    intro m
    refine ⟨Spec.map (CommRingCat.ofHom (eB'.symm m).toRingHom), ?_⟩
    apply pullback.hom_ext
    · rw [Category.assoc, mapOnProdOver_fst, Category.assoc]
      show (ptOf (eB'.symm m)).1 ≫ _ = _ ≫ pullback.lift _ _ _ ≫ pullback.fst _ _
      rw [ptOf_fst, pullback.lift_fst]
    · rw [Category.assoc, mapOnProdOver_snd, ← Category.assoc, (q m).2, Category.id_comp, Category.assoc, hWsnd]
      show _ = Spec.map _ ≫ Spec.map _
      rw [← Spec.map_comp, ← CommRingCat.ofHom_comp, AlgHom.toRingHom_eq_coe, AlgHom.comp_algebraMap]
  have hqall : ∀ y : Spec (CommRingCat.of Ω) ⟶ Spec (CommRingCat.of (B' i₀)),
      y ≫ W ≫ pullback.snd c (𝟙 _) = (SmoothProperCurve.specMap R Ω) →
      ∃ m, (q m).1 ≫ mapOnProdOver c (SmoothProperCurve.specMap R Ω) (Category.comp_id _) = y ≫ W := by
    intro y hy

    obtain ⟨f, rfl⟩ : ∃ f : CommRingCat.of (B' i₀) ⟶ CommRingCat.of Ω, Spec.map f = y := ⟨Spec.preimage y, Spec.map_preimage y⟩
    have hf : f.hom.comp (algebraMap R (B' i₀)) = algebraMap R Ω := by
      rw [hWsnd] at hy
      have h1 : Spec.map (CommRingCat.ofHom (algebraMap R (B' i₀)) ≫ f) = Spec.map (CommRingCat.ofHom (algebraMap R Ω)) := by
        rw [Spec.map_comp]; exact hy
      have h2 := congrArg CommRingCat.Hom.hom (Spec.map_injective h1)
      simpa using h2
    let ψ : B' i₀ →ₐ[R] Ω :=
      { f.hom with
        commutes' := fun a => by
          have := congrArg (fun g : R →+* Ω => g a) hf
          simpa using this }
    refine ⟨eB' ψ, ?_⟩
    have hψ : Spec.map (CommRingCat.ofHom ψ.toRingHom) = Spec.map f := by congr 1
    obtain ⟨y', hy'⟩ := hqW (eB' ψ)

    apply pullback.hom_ext
    · rw [Category.assoc, mapOnProdOver_fst, Category.assoc]
      show (ptOf (eB'.symm (eB' ψ))).1 ≫ _ = _ ≫ pullback.lift _ _ _ ≫ pullback.fst _ _
      rw [ptOf_fst, pullback.lift_fst, Equiv.symm_apply_apply, hψ]
    · rw [Category.assoc, mapOnProdOver_snd, ← Category.assoc, (q (eB' ψ)).2, Category.id_comp, Category.assoc, hy]
  have hpε : (sectionFibrePoint ε (SmoothProperCurve.specMap R Ω)).1 ≫ pullback.fst c (SmoothProperCurve.specMap R Ω) = (SmoothProperCurve.specMap R Ω) ≫ ε.1 :=
    pullback.lift_fst _ _ _
  obtain ⟨eN10⟩ :=
    AlgebraicGeometry.RelEffCartierDiv.nonempty_lineBundle_pullbackAlong_iso_invModule_pow_ker_mul_pow_prod_ker
      R c ε E r r' (deg' i₀) W hEI (SmoothProperCurve.specMap R Ω) q hqinj hqW hqall (sectionFibrePoint ε (SmoothProperCurve.specMap R Ω)) hpε
  let eMod := whiskerLeftIso L₀ (whiskerRightIso eN10 (((∏ j, (v j).1.ker) * (∏ j, (v' j).1.ker)).module))
  refine ⟨fun 𝒲 => ?_, fun τ hτ => ?_⟩
  · obtain ⟨f1⟩ := H1_equiv_of_iso (pullback.snd c (SmoothProperCurve.specMap R Ω)) 𝒲 eMod
    haveI := H1 𝒲
    exact f1.toEquiv.subsingleton
  · have hτ' : τ ≫ eMod.hom ≠ 0 := fun h => hτ (by
      have h' := congrArg (· ≫ eMod.inv) h
      simp only [Category.assoc, Iso.hom_inv_id, Category.comp_id, Limits.zero_comp] at h'
      exact h')
    have := H2 (τ ≫ eMod.hom) hτ'
    rwa [Scheme.Modules.zeroSchemeIdeal_comp_eq_of_isIso] at this

end S_AlgebraicGeometry_RelPicard_exists_split_injective_forall_subsingleton_H1_lineBundle_and_support_subset_of_twoSidedBlocks_of_bijective_sections
end P2MW
export P2MW.S_AlgebraicGeometry_RelPicard_exists_split_injective_forall_subsingleton_H1_lineBundle_and_support_subset_of_twoSidedBlocks_of_bijective_sections (solution)
