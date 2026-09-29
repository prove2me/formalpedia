-- Prove2me | solution 1 for AlgebraicGeometry.RelPicard.finrank_H1_le_finrank_H1_unit_add_one_of_isAlgEquivZero_of_twoGluedSmoothCurves
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:03.589526+00:00
-- url     : https://prove2.me/submissions/a1e324de-8e42-5f7c-ac3e-cc1e634966d3

import Mathlib
import Definitions.Def_AlgebraicGeometry_NeronModelPropertyBundleCarrier
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import Definitions.Def_AlgebraicGeometry_RelPicardAlgEquivZeroCut
import Definitions.Def_AlgebraicGeometry_TwoAffineOpenCover
import Definitions.Def_AlgebraicGeometry_TwoChartCechSectionsOf
import Definitions.Def_SheafOfModules_Monoidal
import Definitions.Def_AlgebraicGeometry_ModulesTensorPow

import Definitions.Def_AlgebraicGeometry_OModulePresheafOfModules
import Definitions.Def_AlgebraicGeometry_ModulesPullbackMonoidal
import Definitions.Def_AlgebraicGeometry_ModulesSectionsTensor
import Definitions.Def_AlgebraicGeometry_ModulesPullbackLocalSection
import Theorems.Thm_AlgebraicGeometry_RelPicard_IsAlgEquivZero_eulerChar_sectionsOf_tensor_eq
import Theorems.Thm_AlgebraicGeometry_RelPicard_IsAlgEquivZero_nonempty_iso_tensorUnit_of_ne_zero
import Theorems.Thm_AlgebraicGeometry_RelPicard_finrank_H0_unit_fibre_eq_one
import Theorems.Thm_AlgebraicGeometry_Scheme_TwoAffineOpenCover_exists_linearEquiv_sectionsOf_of_iso
import Theorems.Thm_AlgebraicGeometry_Scheme_TwoAffineOpenCover_exists_linearEquiv_sectionsOf_H0
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_IsInvertible_exists_isFrameOn
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_IsFrameOn_pullbackLocalSection
import Theorems.Thm_AlgebraicGeometry_IsClosedImmersion_app_injective_and_exists_of_app_pullback_eq_of_isReduced
import Theorems.Thm_AlgebraicGeometry_OModulePresheaf_cechFinite_ofModules_of_locallyTrivial
import Theorems.Thm_AlgebraicGeometry_OModulePresheaf_cechFinite_toOrderedAffineCover_iff
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_RelPicard_finrank_H1_le_finrank_H1_unit_add_one_of_isAlgEquivZero_of_twoGluedSmoothCurves
p2m_attr_erase "instance" "AlgebraicGeometry.OModulePresheaf.instSubsingletonObjZero AlgebraicGeometry.OModulePresheaf.Leray.relAltC_scalarTower AlgebraicGeometry.OModulePresheaf.Leray.ker_relAltd_modΓ AlgebraicGeometry.OModulePresheaf.Leray.relAltC_modΓ AlgebraicGeometry.OModulePresheaf.Leray.biC_abGrp AlgebraicGeometry.OModulePresheaf.Leray.relAltH_modΓ AlgebraicGeometry.OModulePresheaf.Leray.ker_relAltd_smul AlgebraicGeometry.OModulePresheaf.Leray.relAltH_scalarTower AlgebraicGeometry.OModulePresheaf.Leray.relAltH_smul AlgebraicGeometry.OModulePresheaf.Leray.biC_module AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instDecidableEqIdx AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instFintype AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instLinearOrder AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instFintypeIdx DoubleComplex.instModuleE₂I DoubleComplex.Bounded.modR DoubleComplex.instModuleE₂II DoubleComplex.instAddCommGroupE₂II DoubleComplex.Bounded.abGrp DoubleComplex.instAddCommGroupE₂I AlgebraicGeometry.ChowDatum.hι_closed AlgebraicGeometry.ChowDatumProj.hιN_closed AlgebraicGeometry.ChowDatumProj.hp_proper AlgebraicGeometry.ChowDatum.hp_isoU AlgebraicGeometry.ChowDatum.hp_proper AlgebraicGeometry.ProjSpace.algebraAway AlgebraicGeometry.ProjSpace.instIsProperProdOverπ AlgebraicGeometry.ChowDatumProj.hp_isoU AlgebraicGeometry.ProjSpace.isProper_π AlgebraicGeometry.ProjSpace.finiteType_mvPolynomial ProjSpaceCech.GradedModule.H.module ProjSpaceCech.GradedModule.H.addCommGroup ProjSpaceCech.GradedModule.sec.instAdd ProjSpaceCech.GradedModule.sec.instNeg ProjSpaceCech.GradedModule.acg ProjSpaceCech.GradedModule.Frac.setoid ProjSpaceCech.GradedModule.modR ProjSpaceCech.GradedModule.sec.instModule ProjSpaceCech.GradedModule.sec.instAddCommGroup ProjSpaceCech.GradedModule.sec.instZero"
p2m_attr_erase "instance" "ProjSpaceCech.GradedModule.Presentation.fJ ProjSpaceCech.GradedModule.sec.instSMul ProjSpaceCech.Twist.H.module ProjSpaceCech.Idx.instFintype ProjSpaceCech.Twist.H.addCommGroup ProjSpaceCech.Idx.instDecidableEq ProjSpaceCech.Twist.Mon.instDecidableEq ProjSpaceCech.Twist.cochain.instAddCommGroup ProjSpaceCech.Twist.cochain.instModule AlgebraicGeometry.RelEffCartierDiv.subsingleton_of_degree_zero AlgebraicGeometry.RelEffCartierDiv.isIso_subschemeIota_snd_of_degree_one AlgebraicGeometry.isIso_ker_graphOver_subschemeIota_snd AlgebraicGeometry.isClosedImmersion_graphOver AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instNeg AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instSMulInt AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instAddCommGroup AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instAdd AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instSub AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instModuleCarrierObjOppositeOpensCarrierCarrierCommRingCatPresheafOpOpensTop AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instSMulCarrierObjOppositeOpensCarrierCarrierCommRingCatPresheafOpOpensTop AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instSMulNat AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instZero AlgebraicCurve.Place.instIsScalarTowerSubtypeMemValuationSubringToValuationSubring AlgebraicCurve.Divisor.instDistribMulActionAlgEquiv AlgebraicCurve.Place.instSMulAlgEquiv AlgebraicCurve.Place.instIsPrincipalIdealRingSubtypeMemValuationSubringToValuationSubring AlgebraicCurve.Place.instIsDiscreteValuationRingSubtypeMemValuationSubringToValuationSubring AlgebraicCurve.Pic0.instDistribMulActionAlgEquiv AlgebraicCurve.Place.instAlgebraSubtypeMemValuationSubringToValuationSubring AlgebraicCurve.Place.instMulActionAlgEquiv AlgebraicCurve.Pic0.instSMulAlgEquiv AlgebraicCurve.CurveModel.isProper AlgebraicCurve.CurveModel.isIntegral AlgebraicCurve.CurveModel.smooth SheafOfModules.isIso_ihomModelToIhom AlgebraicGeometry.SmoothOfRelativeDimension.fiberToSpecResidueField AlgebraicGeometry.SmoothOfRelativeDimension.pullback_snd AlgebraicGeometry.SmoothOfRelativeDimension.pullback_fst AlgebraicGeometry.SmoothOfRelativeDimension.smooth_one AlgebraicGeometry.SmoothProperCurve.isIntegral_pullback_Spec_field"
p2m_attr_erase "instance" "AlgebraicGeometry.IsProper.fiberToSpecResidueField AlgebraicCurve.IsCurveOver.instNontrivialKaehler AlgebraicCurve.IsCurveOver.instFreeKaehler AlgebraicCurve.IsCurveOver.toHasPrincipalDivisors AlgebraicCurve.IsCurveOver.instFiniteResidue AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.instFundamentalIdentityOfSumRamificationInertia AlgebraicCurve.Place.instIsScalarTowerResidueFieldRestrictPushforward AlgebraicCurve.Place.instAlgebraResidueFieldRestrictPushforward AlgebraicCurve.Place.instIsLocalHomRestrictInclusion AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.SemilinearAut.instDistribMulActionSubtypeProdRingAutMemSubgroupPic0 AlgebraicCurve.SemilinearAut.instDistribMulActionSubtypeProdRingAutMemSubgroupDivisor AlgebraicCurve.Pic0.instModuleZModTorsion AlgebraicCurve.SemilinearAut.instSMulSubtypeProdRingAutMemSubgroupPlace AlgebraicCurve.SemilinearAut.instDistribMulActionTorsion AlgebraicCurve.SemilinearAut.instSMulSubtypeProdRingAutMemSubgroupPic0 AlgebraicCurve.SemilinearAut.instSMulTorsion AlgebraicCurve.SemilinearAut.instMulActionSubtypeProdRingAutMemSubgroupPlace AlgebraicCurve.SemilinearAut.instSMulCommClassZModTorsion AlgebraicCurve.SemilinearAut.instMulSemiringActionSubtypeProdRingAutMemSubgroup instDecEqAlgebraicClosureRat WeierstrassCurve.Affine.Point.instDistribMulActionAlgEquiv WeierstrassCurve.Affine.Point.instModuleZModTorsionBy WeierstrassCurve.Affine.Point.instSMulTorsionBy WeierstrassCurve.Affine.Point.instDistribMulActionTorsionBy WeierstrassCurve.Affine.Point.instSMulAlgEquiv WeierstrassCurve.Affine.Point.instSMulCommClassAlgEquivZModTorsionBy AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions AlgebraicCurve.instHasLocalResidue_of_hasCanonicalLocalResidueK AlgebraicCurve.instHasCanonicalLocalResidueK_of_hasCanonicalLocalResidueKStar AlgebraicCurve.Place.kw_ffgc_finiteDimensional_adicCompletion instAlgebraSubtypeMemValuationSubring_definitions AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersIntegersCompletion ModularCurve.KwF4gRRTate.instAlgebraKAdicCompletionIntegers"
p2m_attr_erase "instance" "AlgebraicCurve.Place.kw_ffgc_continuousSMul_adicCompletionComap AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersCompletionCompletion IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions AlgebraicCurve.instHasCanonicalLocalResidueK AlgebraicCurve.Place.instAlgebra_restrictResidueField AlgebraicCurve.Place.instIsScalarTower_restrictResidueField AlgebraicCurve.instHasLocalResidue AlgebraicCurve.HasSeparableResidue.of_perfectField_of_isCurveOver AlgebraicCurve.HasSeparableResidue.of_perfectField AlgebraicCurve.Place.instIsLocalHom_restrictSubringHom AlgebraicCurve.instHasCanonicalLocalResidueKStar ModularCurve.KwNo6Pin.isLocalRing_completion"
p2m_attr_erase "simp" "TwoChartCech.Mumford.dK_apply TwoChartCech.Mumford.ι0_apply TwoChartCech.Mumford.ι1_apply TwoChartCech.KerCoprod.dK_apply TwoChartCech.KerCoprod.ι1_apply TwoChartCech.KerCoprod.ι0_apply AlgebraicGeometry.tilde.functorCompPullbackSpecIso_app AlgebraicGeometry.OModulePresheaf.prod_obj AlgebraicGeometry.OModulePresheaf.restrOpen_obj AlgebraicGeometry.OModulePresheaf.DevissageStep.mk.injEq AlgebraicGeometry.OModulePresheaf.pushforward_obj AlgebraicGeometry.OModulePresheaf.im_obj AlgebraicGeometry.OModulePresheaf.pow_obj AlgebraicGeometry.OModulePresheaf.fstHom_app AlgebraicGeometry.OModulePresheaf.ker_obj AlgebraicGeometry.OModulePresheaf.coker_obj AlgebraicGeometry.OModulePresheaf.DevissageStep.mk.sizeOf_spec AlgebraicGeometry.Scheme.OrderedAffineCover.preimage_U AlgebraicGeometry.OModulePresheaf.sndHom_app AlgebraicGeometry.OModulePresheaf.Hom.mk.injEq AlgebraicGeometry.OModulePresheaf.Hom.id_app AlgebraicGeometry.OModulePresheaf.AffHom.appSections_apply AlgebraicGeometry.OModulePresheaf.AffHom.comp_app AlgebraicGeometry.OModulePresheaf.AffSES.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.AffHom.kerMap_coe AlgebraicGeometry.OModulePresheaf.AffHom.id_app AlgebraicGeometry.OModulePresheaf.Hom.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.Hom.toAffHom_app AlgebraicGeometry.OModulePresheaf.SES.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.AffHom.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.Hom.comp_app AlgebraicGeometry.OModulePresheaf.SES.mk.injEq AlgebraicGeometry.OModulePresheaf.AffHom.mk.injEq AlgebraicGeometry.OModulePresheaf.Hom.appSections_apply AlgebraicGeometry.OModulePresheaf.AffSES.mk.injEq AlgebraicGeometry.OModulePresheaf.Leray.restrictToPreimage_U AlgebraicGeometry.Scheme.OrderedAffineCover.toCoverOf_U AlgebraicGeometry.Scheme.OrderedAffineCoverOf.mk.sizeOf_spec AlgebraicGeometry.Scheme.OrderedAffineCoverOf.mk.injEq AlgebraicGeometry.Scheme.OrderedAffineCover.restrict_U"
p2m_attr_erase "simp" "DoubleComplex.Bounded.mk.injEq DoubleComplex.Bounded.mk.sizeOf_spec DoubleComplex.Convergence.mk.injEq DoubleComplex.Convergence.mk.sizeOf_spec DoubleComplex.SubQuot.mk.sizeOf_spec DoubleComplex.SubQuot.mk.injEq AlgebraicGeometry.ChowDatumProj.mk.sizeOf_spec AlgebraicGeometry.ChowDatum.mk.sizeOf_spec AlgebraicGeometry.ChowDatumProj.mk.injEq AlgebraicGeometry.ChowDatum.mk.injEq ProjSpaceCech.GradedModule.mk.injEq ProjSpaceCech.GradedModule.mk.sizeOf_spec ProjSpaceCech.GradedModule.Frac.mk.sizeOf_spec ProjSpaceCech.GradedModule.Presentation.mk.injEq ProjSpaceCech.GradedModule.Frac.mk.injEq ProjSpaceCech.GradedModule.Presentation.mk.sizeOf_spec ProjSpaceCech.GradedModule.Hom.shift_toLinearMap ProjSpaceCech.GradedModule.Hom.mk.sizeOf_spec ProjSpaceCech.GradedModule.Hom.mk.injEq AlgebraicGeometry.Scheme.Modules.toUnitSection_ofUnitSection AlgebraicGeometry.Scheme.Modules.pullbackSection_def AlgebraicGeometry.Scheme.Modules.ofUnitSection_toUnitSection AlgebraicGeometry.RelEffCartierDiv.toRelEffDivisor_ofRelEffDivisor AlgebraicGeometry.RelEffCartierDiv.toRelEffDivisor_I AlgebraicGeometry.mapOnProdOver_fst_assoc AlgebraicGeometry.RelEffCartierDiv.mk.sizeOf_spec AlgebraicGeometry.RelEffCartierDiv.mk.injEq AlgebraicGeometry.mapOnProdOver_snd AlgebraicGeometry.mapOnProdOver_fst AlgebraicGeometry.mapOnProdOver_snd_assoc AlgebraicGeometry.mapOnProdOver_id AlgebraicCurve.RelEffDivisor.mk.sizeOf_spec AlgebraicCurve.mapOnProd_fst AlgebraicCurve.mapOnProd_fst_assoc AlgebraicCurve.mapOnProd_snd AlgebraicCurve.UnivDivisorPack.mk.injEq AlgebraicCurve.RelEffDivisor.mk.injEq AlgebraicCurve.UnivDivisorPack.mk.sizeOf_spec AlgebraicCurve.mapOnProd_snd_assoc AlgebraicGeometry.prodKerGraph_one"
p2m_attr_erase "simp" "AlgebraicGeometry.fibrePowOver.proj_comp AlgebraicGeometry.prodKerGraph_zero AlgebraicGeometry.RelEffCartierDiv.empty_I AlgebraicGeometry.fibrePowOver.proj_comp_assoc AlgebraicGeometry.graphOver_fst_assoc AlgebraicGeometry.RelEffCartierDiv.toPoint_comp AlgebraicGeometry.RelEffCartierDiv.toPoint_comp_assoc AlgebraicGeometry.graphOver_fst AlgebraicGeometry.RelEffCartierDiv.ofPoint_I AlgebraicGeometry.graphOver_snd AlgebraicGeometry.graphOver_snd_assoc AlgebraicCurve.SymmetricPowerPackage.mk.sizeOf_spec AlgebraicCurve.SymmetricPowerPackage.mk.injEq AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.sub_app AlgebraicGeometry.Scheme.IdealSheafData.sres_sresTop AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.add_app AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.mk.sizeOf_spec AlgebraicGeometry.Scheme.IdealSheafData.coe_resLE AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.smul_app AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.coe_ofLE_app AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.ideal_range AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.zero_app AlgebraicGeometry.Scheme.IdealSheafData.sres_sres AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.comp_app AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.neg_app AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.id_app AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.coe_mulRight_app AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.nsmul_app AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.mk.injEq AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.zsmul_app AlgebraicCurve.Place.mk.injEq AlgebraicCurve.Divisor.degree_single AlgebraicCurve.Divisor.smul_single AlgebraicCurve.Place.smul_toValuationSubring AlgebraicCurve.Place.heightOneSpectrum_asIdeal AlgebraicCurve.Place.coe_algebraMap AlgebraicCurve.Place.ord_one AlgebraicCurve.Place.coe_smulRingEquiv_apply AlgebraicCurve.Pic0.coe_degZeroSMulHom AlgebraicCurve.Place.deg_smul"
p2m_attr_erase "simp" "AlgebraicCurve.Pic0.mk_zero AlgebraicCurve.Place.mk.sizeOf_spec AlgebraicCurve.Divisor.degree_smul AlgebraicCurve.Pic0.mk_add AlgebraicCurve.Place.ord_zero AlgebraicCurve.Place.ofHeightOneSpectrum_toValuationSubring AlgebraicCurve.CurveModel.mk.injEq AlgebraicCurve.CurveModel.mk.sizeOf_spec PresheafOfModules.InternalHom.IsSheafAux.appAt_toPresheafHom SheafOfModules.ihomSectionsEquivFamily_unit AlgebraicGeometry.Scheme.Modules.restrictHomEquivFamily_apply SheafOfModules.ihomEval_unit_app AlgebraicGeometry.Scheme.Modules.ihomEval_zero_right AlgebraicGeometry.Scheme.Modules.ihomEval_zero_left AlgebraicGeometry.Scheme.Modules.homOfFamily_app_apply SheafOfModules.unit_ihomSectionsEquivFamily AlgebraicGeometry.Scheme.Modules.familyOfHom_app AlgebraicGeometry.Scheme.Modules.restrictUnitIso_hom_app_apply AlgebraicGeometry.Scheme.Modules.restrictUnitIso_inv_app_apply AlgebraicGeometry.Scheme.Modules.restrictHomOfFamily_app_apply AlgebraicGeometry.Scheme.Modules.restrictHomEquivFamily_symm_apply AlgebraicGeometry.SmoothProperCurve.sectionBaseChange_coe_snd AlgebraicGeometry.SmoothProperCurve.sectionBaseChange_coe_fst AlgebraicGeometry.RelPicard.fst_toProdSpec AlgebraicGeometry.RelPicard.toProdSpec_fst_assoc AlgebraicGeometry.RelPicard.pointsSubBasepointModule_cons AlgebraicGeometry.RelPicard.pointsSubBasepointModule_nil AlgebraicGeometry.RelPicard.fst_toProdSpec_assoc AlgebraicGeometry.RelPicard.toProdSpec_fst AlgebraicCurve.mulAdele_apply AlgebraicCurve.residuePairing_apply_coe AlgebraicCurve.mem_adeleBdd AlgebraicCurve.weilSmul_one AlgebraicCurve.diagonalHom_apply AlgebraicCurve.weilSmul_apply AlgebraicCurve.adeleSpaceMul_coe AlgebraicCurve.mulAdele_one AlgebraicCurve.coe_cechH0Equiv_apply AlgebraicCurve.cechH1ToH1_mk AlgebraicCurve.lSpaceOn_univ"
p2m_attr_erase "simp" "AlgebraicCurve.lSpaceOn_empty AlgebraicCurve.Place.congrEquiv_symm_apply AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply AlgebraicCurve.RationalFunctionField.deg_placeOfPoint AlgebraicCurve.Divisor.mapRestrict_single AlgebraicCurve.Divisor.pushforward_single AlgebraicCurve.Place.coe_restrictInclusion AlgebraicCurve.Place.mem_fiber AlgebraicCurve.Place.restrict_toValuationSubring AlgebraicCurve.Divisor.degree_pushforward AlgebraicCurve.Place.restrictResidueMap_residue AlgebraicCurve.Pic0.coe_pushforwardDegZeroHom AlgebraicCurve.Pic0.coe_pullbackDegZeroHom AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal AlgebraicCurve.IsFrobeniusEndo.frobNormRingHom_apply ModularCurve.frobeniusPushforwardGeomLevelPic0_mk ModularCurve.coe_frobeniusGeomLevelEquiv_apply ModularCurve.coe_frobeniusPushforwardGeomLevelDegZero ModularCurve.heckeFibreGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusGeomLevel_apply_coe ModularCurve.frobeniusPullbackGeomLevelPic0OfIsCurveOver_mk ModularCurve.coe_heckeFibreGeomLevelDegZero ModularCurve.coe_frobeniusPullbackGeomLevelDegZero ModularCurve.frobeniusPullbackGeomLevelPic0_mk ModularCurve.frobeniusPullbackGeomLevel_single ModularCurve.heckeFibreGeomLevelPic0_mk ModularCurve.frobeniusPushforwardGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusPushforwardGeomLevel_single ModularCurve.qExpandAlgC_apply AlgebraicCurve.Divisor.degree_pushforwardAlong AlgebraicCurve.Pic0.coe_degZeroCorrespondence AlgebraicCurve.Place.mem_fiberAlong AlgebraicCurve.SemilinearAut.toRingAut_inv"
p2m_attr_erase "simp" "AlgebraicCurve.SemilinearAut.smul_def AlgebraicCurve.SemilinearAut.smul_single AlgebraicCurve.SemilinearAut.smul_toValuationSubring AlgebraicCurve.SemilinearAut.baseAut_inv AlgebraicCurve.SemilinearAut.baseAut_ofAlgAut AlgebraicCurve.SemilinearAut.toRingAut_ofAlgAut AlgebraicCurve.SemilinearAut.torsionRep_apply AlgebraicCurve.SemilinearAut.toRingAut_one AlgebraicCurve.SemilinearAut.deg_smul AlgebraicCurve.SemilinearAut.degree_smul AlgebraicCurve.SemilinearAut.coe_degZeroSMulHom AlgebraicCurve.SemilinearAut.baseAut_mul AlgebraicCurve.SemilinearAut.coe_smulValuationSubringEquiv_apply AlgebraicCurve.SemilinearAut.baseAut_one AlgebraicCurve.SemilinearAut.ofAlgAut_smul AlgebraicCurve.SemilinearAut.coe_torsion_smul AlgebraicCurve.SemilinearAut.toRingAut_mul AlgebraicCurve.coe_frobeniusPushforwardDegZero AlgebraicCurve.IsFrobeniusEndo.coe_frobeniusPullbackDegZero ModularCurve.jqNModC_one ModularCurve.qExpand_coeff_mul ModularCurve.qExpandₐ_apply ModularCurve.jqN_one ModularCurve.qExpand_single ModularCurve.dedekindPsi_one ModularCurve.ModularPolynomialData.mk.sizeOf_spec ModularCurve.evalAtJ_X ModularCurve.ModularPolynomialData.mk.injEq ModularCurve.constantCoeff_jNum ModularCurve.constantCoeff_eisenstein4 ModularCurve.qExpand_C ModularCurve.coeff_jq_neg_one ModularCurve.constantCoeff_jNumQ ModularCurve.reduceModBivar_C_X ModularCurve.laurentMap_coeff ModularCurve.reduceModBivar_X ModularCurve.laurentMap_single ModularCurve.evalAtJInt_X ModularCurve.evalAtJMod_X ModularCurve.jqNMod_one"
p2m_attr_erase "simp" "ModularCurve.aeval_heckeGen ModularCurve.coe_mTorsionGaloisRep_apply ModularCurve.eisensteinSystem_of_dvd ModularCurve.eisensteinSystem_of_not_dvd FreyPackage.mk.sizeOf_spec FreyPackage.mk.injEq WeierstrassCurve.Affine.Point.galoisRepModuleEnd_apply AlgebraicCurve.RationalFunctionField.placeInfty_toValuationSubring AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none AlgebraicCurve.Divisor.evalFun_zero AlgebraicCurve.Place.evalAt_one AlgebraicCurve.Place.differentialCoeff_zero AlgebraicCurve.Place.differentialCoeff_dCoord AlgebraicCurve.TranscendenceTower.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.injEq AlgebraicCurve.TranscendenceTower.mk.injEq AlgebraicCurve.PoleDivisorPackage.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.sizeOf_spec AlgebraicCurve.PoleDivisorPackage.mk.injEq AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.sizeOf_spec AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.injEq AlgebraicCurve.adeleSingle_coe AlgebraicCurve.kaehlerResidueTermKFam_apply AlgebraicCurve.Place.LocalResidueData.mk.injEq AlgebraicCurve.Place.LocalResidueData.mk.sizeOf_spec AlgebraicCurve.Place.kw_ffgc_adicCompletionComapIntegers_coe AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.sizeOf_spec AlgebraicCurve.Place.mem_simplePoleSubmodule AlgebraicCurve.Place.coe_uniformizerSubring ModularCurve.Lg37.Lg37CompletionSection.mk.injEq AlgebraicCurve.Place.CoefficientFieldSection.mk.injEq AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.injEq ModularCurve.Lg37.Lg37CompletionSection.mk.sizeOf_spec AlgebraicCurve.Place.CoefficientFieldSection.mk.sizeOf_spec AlgebraicCurve.Place.poleSubmodule_one AlgebraicCurve.Place.mem_poleSubmodule"

set_option autoImplicit false

universe u

p2m_open "CategoryTheory CategoryTheory.Limits Opposite CategoryTheory.MonoidalCategory AlgebraicGeometry P2MW.S_AlgebraicGeometry_RelPicard_finrank_H1_le_finrank_H1_unit_add_one_of_isAlgEquivZero_of_twoGluedSmoothCurves.AlgebraicGeometry AlgebraicGeometry.RelPicard NeronModelInfra TensorProduct"

noncomputable section

namespace AlgebraicGeometry
p2m_export "AlgebraicGeometry" "Scheme.Modules.Hom.app_smul Scheme.Modules.Hom.zero_app SmoothOfRelativeDimension IsProper Scheme.Modules.pullback Scheme.Hom GeometricallyIntegral Scheme.Hom.appLE_comp_appLE Scheme.Modules.presheaf Scheme.Hom.preimage_inf GeometricallyIrreducible Scheme.Modules.Hom Spec Scheme Scheme.Modules.Hom.app IsClosedImmersion IsReduced Scheme.Modules.pullbackPushforwardAdjunction Scheme.Modules.pullbackId Scheme.Hom.preimage_sup Scheme.Modules IsAffineHom Scheme.ΓSpecIso Scheme.Hom.appLE_eq_app Scheme.Modules.IsInvertible Scheme.Modules.isInvertible_unit RelPicard.IsAlgEquivZero Scheme.TwoAffineOpenCover Scheme.TwoAffineOpenCover.algebraOfHom Scheme.TwoAffineOpenCover.moduleSectionsOfHom Scheme.TwoAffineOpenCover.sectionsOf_r0_apply Scheme.TwoAffineOpenCover.sectionsOf_r1_apply OModulePresheaf Scheme.Modules.pullbackTensorUnitObjIso Scheme.Modules.IsFrameOn Scheme.Modules.pullbackLocalSection Scheme.Modules.map_homOfLE_pullbackLocalSection RelPicard.IsAlgEquivZero.eulerChar_sectionsOf_tensor_eq RelPicard.IsAlgEquivZero.nonempty_iso_tensorUnit_of_ne_zero RelPicard.finrank_H0_unit_fibre_eq_one Scheme.TwoAffineOpenCover.exists_linearEquiv_sectionsOf_of_iso Scheme.TwoAffineOpenCover.exists_linearEquiv_sectionsOf_H0 Scheme.Modules.IsFrameOn.pullbackLocalSection IsClosedImmersion.app_injective_and_exists_of_app_pullback_eq_of_isReduced OModulePresheaf.cechFinite_ofModules_of_locallyTrivial OModulePresheaf.cechFinite_toOrderedAffineCover_iff Scheme.TwoAffineOpenCover.ext_N2bC2"
namespace H0Sum
p2m_open "AlgebraicGeometry"

variable {k : Type u} [Field k] {X Y : Scheme.{u}} (i : Y ⟶ X) (x : X ⟶ Spec (CommRingCat.of k))

def res (F : X.Modules) (U : X.Opens) : Γ(F, U) →+ Γ((Scheme.Modules.pullback i).obj F, i ⁻¹ᵁ U) :=
  (((Scheme.Modules.pullbackPushforwardAdjunction i).unit.app F).app U).hom

theorem res_apply (F : X.Modules) (U : X.Opens) (m : Γ(F, U)) :
    res i F U m = Scheme.Modules.pullbackLocalSection i m := rfl

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

theorem resₗ_apply (F : X.Modules) (U : X.Opens) (m : Γ(F, U)) : resₗ i x F U m = res i F U m := rfl

def comap {X' Y' : Scheme.{u}} (𝒲 : Y'.TwoAffineOpenCover) (f : X' ⟶ Y') [IsAffineHom f] : X'.TwoAffineOpenCover where
  U0 := f ⁻¹ᵁ 𝒲.U0
  U1 := f ⁻¹ᵁ 𝒲.U1
  isAffineOpen_U0 := 𝒲.isAffineOpen_U0.preimage f
  isAffineOpen_U1 := 𝒲.isAffineOpen_U1.preimage f
  sup_eq_top := by rw [← Scheme.Hom.preimage_sup, 𝒲.sup_eq_top]; rfl
  isAffineOpen_inf := by rw [← Scheme.Hom.preimage_inf]; exact 𝒲.isAffineOpen_inf.preimage f

end AlgebraicGeometry.H0Sum

namespace AlgebraicGeometry
p2m_export "AlgebraicGeometry" "Scheme.Modules.Hom.app_smul Scheme.Modules.Hom.zero_app SmoothOfRelativeDimension IsProper Scheme.Modules.pullback Scheme.Hom GeometricallyIntegral Scheme.Hom.appLE_comp_appLE Scheme.Modules.presheaf Scheme.Hom.preimage_inf GeometricallyIrreducible Scheme.Modules.Hom Spec Scheme Scheme.Modules.Hom.app IsClosedImmersion IsReduced Scheme.Modules.pullbackPushforwardAdjunction Scheme.Modules.pullbackId Scheme.Hom.preimage_sup Scheme.Modules IsAffineHom Scheme.ΓSpecIso Scheme.Hom.appLE_eq_app Scheme.Modules.IsInvertible Scheme.Modules.isInvertible_unit RelPicard.IsAlgEquivZero Scheme.TwoAffineOpenCover Scheme.TwoAffineOpenCover.algebraOfHom Scheme.TwoAffineOpenCover.moduleSectionsOfHom Scheme.TwoAffineOpenCover.sectionsOf_r0_apply Scheme.TwoAffineOpenCover.sectionsOf_r1_apply OModulePresheaf Scheme.Modules.pullbackTensorUnitObjIso Scheme.Modules.IsFrameOn Scheme.Modules.pullbackLocalSection Scheme.Modules.map_homOfLE_pullbackLocalSection RelPicard.IsAlgEquivZero.eulerChar_sectionsOf_tensor_eq RelPicard.IsAlgEquivZero.nonempty_iso_tensorUnit_of_ne_zero RelPicard.finrank_H0_unit_fibre_eq_one Scheme.TwoAffineOpenCover.exists_linearEquiv_sectionsOf_of_iso Scheme.TwoAffineOpenCover.exists_linearEquiv_sectionsOf_H0 Scheme.Modules.IsFrameOn.pullbackLocalSection IsClosedImmersion.app_injective_and_exists_of_app_pullback_eq_of_isReduced OModulePresheaf.cechFinite_ofModules_of_locallyTrivial OModulePresheaf.cechFinite_toOrderedAffineCover_iff Scheme.TwoAffineOpenCover.ext_N2bC2"
namespace H0Sum
p2m_open "AlgebraicGeometry"

theorem eq_zero_of_res_eq_zero {X Y₁ Y₂ : Scheme.{u}} [IsReduced X] (i₁ : Y₁ ⟶ X) (i₂ : Y₂ ⟶ X)
    [IsClosedImmersion i₁] [IsClosedImmersion i₂] (hcover : Set.range i₁.base ∪ Set.range i₂.base = Set.univ)
    (F : X.Modules) (hF : Scheme.Modules.IsInvertible F) (U : X.Opens) (m : Γ(F, U))
    (h₁ : res i₁ F U m = 0) (h₂ : res i₂ F U m = 0) : m = 0 := by
  classical

  choose V e hpV hframe using fun p : U => hF.exists_isFrameOn (p : X)
  let W : U → X.Opens := fun p => V p ⊓ U
  have hWU : ∀ p, W p ≤ U := fun p => inf_le_right
  have hcov : U ≤ iSup W := fun q hq => TopologicalSpace.Opens.mem_iSup.mpr ⟨⟨q, hq⟩, ⟨hpV ⟨q, hq⟩, hq⟩⟩

  apply TopCat.Sheaf.eq_of_locally_eq' (⟨F.presheaf, F.isSheaf⟩ : TopCat.Sheaf Ab X) W U (fun p => homOfLE (hWU p)) hcov
  intro p
  rw [map_zero]

  obtain ⟨g, hg, -⟩ := (hframe p).existsUnique (W := W p) inf_le_left inf_le_left (F.presheaf.map (homOfLE (hWU p)).op m)
  rw [← hg]

  have key : ∀ {Y : Scheme.{u}} (i : Y ⟶ X), res i F U m = 0 → (i.app (W p)).hom g = 0 := by
    intro Y i hi
    have hfr := (Scheme.Modules.IsFrameOn.pullbackLocalSection i (hframe p)).smul_eq_zero_iff
      (W := i ⁻¹ᵁ (W p)) (fun _ h => h.1) (fun _ h => h.1) ((i.app (W p)).hom g)
    refine hfr.mp ?_

    have h3 : res i F (W p) (g • F.presheaf.map (homOfLE (inf_le_left : W p ≤ V p)).op (e p)) = 0 := by
      rw [hg, res_map, hi, map_zero]
    rw [res_smul, res_apply, ← Scheme.Modules.map_homOfLE_pullbackLocalSection] at h3
    exact h3
  have hinj := (IsClosedImmersion.app_injective_and_exists_of_app_pullback_eq_of_isReduced i₁ i₂ hcover (W p)).1
  have hg0 : g = 0 := hinj (by
    change ((i₁.app (W p)) g, (i₂.app (W p)) g) = ((i₁.app (W p)) 0, (i₂.app (W p)) 0)
    rw [map_zero, map_zero]
    exact Prod.ext (key i₁ h₁) (key i₂ h₂))
  rw [hg0, zero_smul]

end AlgebraicGeometry.H0Sum

namespace AlgebraicGeometry
p2m_export "AlgebraicGeometry" "Scheme.Modules.Hom.app_smul Scheme.Modules.Hom.zero_app SmoothOfRelativeDimension IsProper Scheme.Modules.pullback Scheme.Hom GeometricallyIntegral Scheme.Hom.appLE_comp_appLE Scheme.Modules.presheaf Scheme.Hom.preimage_inf GeometricallyIrreducible Scheme.Modules.Hom Spec Scheme Scheme.Modules.Hom.app IsClosedImmersion IsReduced Scheme.Modules.pullbackPushforwardAdjunction Scheme.Modules.pullbackId Scheme.Hom.preimage_sup Scheme.Modules IsAffineHom Scheme.ΓSpecIso Scheme.Hom.appLE_eq_app Scheme.Modules.IsInvertible Scheme.Modules.isInvertible_unit RelPicard.IsAlgEquivZero Scheme.TwoAffineOpenCover Scheme.TwoAffineOpenCover.algebraOfHom Scheme.TwoAffineOpenCover.moduleSectionsOfHom Scheme.TwoAffineOpenCover.sectionsOf_r0_apply Scheme.TwoAffineOpenCover.sectionsOf_r1_apply OModulePresheaf Scheme.Modules.pullbackTensorUnitObjIso Scheme.Modules.IsFrameOn Scheme.Modules.pullbackLocalSection Scheme.Modules.map_homOfLE_pullbackLocalSection RelPicard.IsAlgEquivZero.eulerChar_sectionsOf_tensor_eq RelPicard.IsAlgEquivZero.nonempty_iso_tensorUnit_of_ne_zero RelPicard.finrank_H0_unit_fibre_eq_one Scheme.TwoAffineOpenCover.exists_linearEquiv_sectionsOf_of_iso Scheme.TwoAffineOpenCover.exists_linearEquiv_sectionsOf_H0 Scheme.Modules.IsFrameOn.pullbackLocalSection IsClosedImmersion.app_injective_and_exists_of_app_pullback_eq_of_isReduced OModulePresheaf.cechFinite_ofModules_of_locallyTrivial OModulePresheaf.cechFinite_toOrderedAffineCover_iff Scheme.TwoAffineOpenCover.ext_N2bC2"
namespace N2bCoreFwd
p2m_open "AlgebraicGeometry"

open AlgebraicGeometry.H0Sum

private theorem _root_.AlgebraicGeometry.Scheme.TwoAffineOpenCover.ext_N2bC2 {X : Scheme.{u}} {𝒱 𝒱' : X.TwoAffineOpenCover}
    (h0 : 𝒱.U0 = 𝒱'.U0) (h1 : 𝒱.U1 = 𝒱'.U1) : 𝒱 = 𝒱' := by
  cases 𝒱; cases 𝒱'; cases h0; cases h1; rfl

p2m_alias "P2MW.S_AlgebraicGeometry_RelPicard_finrank_H1_le_finrank_H1_unit_add_one_of_isAlgEquivZero_of_twoGluedSmoothCurves.AlgebraicGeometry.Scheme.TwoAffineOpenCover.ext_N2bC2" "AlgebraicGeometry.Scheme.TwoAffineOpenCover.ext_N2bC2"
theorem finrank_H0_H1_sectionsOf_eq_of_iso {k : Type u} [Field k] {X : Scheme.{u}} (x : X ⟶ Spec (CommRingCat.of k))
    {M M' : X.Modules} (e : M ≅ M') (𝒱 : X.TwoAffineOpenCover) :
    Module.finrank k (𝒱.sectionsOf x M).H0 = Module.finrank k (𝒱.sectionsOf x M').H0 ∧
      Module.finrank k (𝒱.sectionsOf x M).H1 = Module.finrank k (𝒱.sectionsOf x M').H1 := by
  obtain ⟨𝒱₁, h0, h1, ⟨e0⟩, ⟨e1⟩⟩ := Scheme.TwoAffineOpenCover.exists_linearEquiv_sectionsOf_of_iso x x (Iso.refl X)
    (Category.id_comp x) 𝒱 M' M (e ≪≫ ((Scheme.Modules.pullbackId X).app M').symm)
  have h0' : 𝒱₁.U0 = 𝒱.U0 := h0
  have h1' : 𝒱₁.U1 = 𝒱.U1 := h1
  obtain rfl : 𝒱₁ = 𝒱 := Scheme.TwoAffineOpenCover.ext_N2bC2 h0' h1'
  exact ⟨e0.finrank_eq, e1.finrank_eq⟩

theorem finrank_H0_sectionsOf_eq {k : Type u} [Field k] {X : Scheme.{u}} (x : X ⟶ Spec (CommRingCat.of k))
    (M : X.Modules) (𝒲 𝒲' : X.TwoAffineOpenCover) :
    Module.finrank k (𝒲.sectionsOf x M).H0 = Module.finrank k (𝒲'.sectionsOf x M).H0 := by
  letI := Scheme.TwoAffineOpenCover.moduleSectionsOfHom x M ⊤
  obtain ⟨e, -⟩ := Scheme.TwoAffineOpenCover.exists_linearEquiv_sectionsOf_H0 𝒲 x M
  obtain ⟨e', -⟩ := Scheme.TwoAffineOpenCover.exists_linearEquiv_sectionsOf_H0 𝒲' x M
  exact (e.symm.trans e').finrank_eq

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
  let 𝒱' : P.TwoAffineOpenCover := H0Sum.comap 𝒲 (pullback.fst y (𝟙 (Spec (CommRingCat.of k))))
  have h1 := RelPicard.finrank_H0_unit_fibre_eq_one y k (𝟙 _) 𝒱'
  obtain ⟨𝒱₁, -, -, ⟨e0⟩, -⟩ := Scheme.TwoAffineOpenCover.exists_linearEquiv_sectionsOf_of_iso y (pullback.snd y (𝟙 _))
    φ hφ 𝒱' (𝟙_ P.Modules) (SheafOfModules.unit Y.ringCatSheaf) (Scheme.Modules.pullbackTensorUnitObjIso φ.hom).symm
  rw [finrank_H0_sectionsOf_eq y _ 𝒲 𝒱₁, e0.finrank_eq]
  exact h1

theorem finite_H0 {k : Type u} [Field k] {X : Scheme.{u}} (x : X ⟶ Spec (CommRingCat.of k)) [IsProper x]
    (G : X.Modules) (hG : Scheme.Modules.IsInvertible G) (𝒲 : X.TwoAffineOpenCover) :
    Module.Finite k (𝒲.sectionsOf x G).H0 := by
  have hcf := OModulePresheaf.cechFinite_ofModules_of_locallyTrivial x G hG.1 𝒲.toOrderedAffineCover
  exact ((OModulePresheaf.cechFinite_toOrderedAffineCover_iff _ _).mp hcf).1

noncomputable def sectionOfGlobal {X : Scheme.{u}} (M : X.Modules) (σ : Γ(M, ⊤)) : M.val.sections :=
  ⟨fun U => (Scheme.Modules.presheaf M).map (homOfLE (le_top : U.unop ≤ ⊤)).op σ,
   fun {U V} f => by
     show (Scheme.Modules.presheaf M).map f ((Scheme.Modules.presheaf M).map (homOfLE (le_top : U.unop ≤ ⊤)).op σ) =
       (Scheme.Modules.presheaf M).map (homOfLE (le_top : V.unop ≤ ⊤)).op σ
     have hg : (homOfLE (le_top : U.unop ≤ ⊤)).op ≫ f = (homOfLE (le_top : V.unop ≤ ⊤)).op :=
       Subsingleton.elim _ _
     rw [← CategoryTheory.ConcreteCategory.comp_apply, ← Functor.map_comp, hg]⟩

theorem sectionOfGlobal_top {X : Scheme.{u}} (M : X.Modules) (σ : Γ(M, ⊤)) :
    (sectionOfGlobal M σ).val (op ⊤) = σ := by
  show (Scheme.Modules.presheaf M).map (homOfLE (le_top : (⊤ : X.Opens) ≤ ⊤)).op σ = σ
  have h1 : (homOfLE (le_top : (⊤ : X.Opens) ≤ ⊤)).op = 𝟙 (op ⊤) := Subsingleton.elim _ _
  rw [h1, CategoryTheory.Functor.map_id]
  rfl

theorem exists_hom_ne_zero {X : Scheme.{u}} (M : X.Modules) (σ : Γ(M, ⊤)) (hσ : σ ≠ 0) :
    ∃ s : 𝟙_ X.Modules ⟶ M, s ≠ 0 := by
  obtain ⟨s, hs⟩ : ∃ s : 𝟙_ X.Modules ⟶ M, (SheafOfModules.unitHomEquiv M) s = sectionOfGlobal M σ :=
    ⟨(SheafOfModules.unitHomEquiv M).symm (sectionOfGlobal M σ), Equiv.apply_symm_apply _ _⟩
  refine ⟨s, fun h0 => hσ ?_⟩
  have e2 : (sectionOfGlobal M σ).val (op ⊤) = σ := sectionOfGlobal_top M σ
  have e3 : (sectionOfGlobal M σ).val (op ⊤) = (Scheme.Modules.Hom.app s ⊤) (1 : Γ(X, ⊤)) := by
    rw [← hs]
    rfl
  rw [← e2, e3, h0, Scheme.Modules.Hom.zero_app]
  rfl

theorem finrank_H0_le_one_of_isAlgEquivZero {k : Type u} [Field k] [IsAlgClosed k] {Y : Scheme.{u}}
    (y : Y ⟶ Spec (CommRingCat.of k)) [IsProper y] [SmoothOfRelativeDimension 1 y] [GeometricallyIntegral y]
    (G : Y.Modules) (hG : Scheme.Modules.IsInvertible G) (h0 : IsAlgEquivZero y G) (𝒱 : Y.TwoAffineOpenCover) :
    Module.finrank k (𝒱.sectionsOf y G).H0 ≤ 1 := by
  haveI : GeometricallyIrreducible y := inferInstance
  letI := Scheme.TwoAffineOpenCover.moduleSectionsOfHom y G ⊤
  obtain ⟨eH, -⟩ := Scheme.TwoAffineOpenCover.exists_linearEquiv_sectionsOf_H0 𝒱 y G
  by_cases hzero : ∀ g : Γ(G, ⊤), g = 0
  · haveI : Subsingleton Γ(G, ⊤) := ⟨fun a b => by rw [hzero a, hzero b]⟩
    haveI : Subsingleton (𝒱.sectionsOf y G).H0 := eH.symm.toEquiv.subsingleton
    rw [Module.finrank_zero_of_subsingleton]
    exact zero_le_one
  · push Not at hzero
    obtain ⟨g, hg⟩ := hzero
    obtain ⟨s, hs⟩ := exists_hom_ne_zero G g hg
    obtain ⟨eG⟩ := RelPicard.IsAlgEquivZero.nonempty_iso_tensorUnit_of_ne_zero y 𝒱 hG h0 s hs
    rw [(finrank_H0_H1_sectionsOf_eq_of_iso y eG 𝒱).1]
    exact (finrank_H0_unit_eq_one y 𝒱).le

theorem finrank_H0_le_add {k : Type u} [Field k] {X Y₁ Y₂ : Scheme.{u}} (x : X ⟶ Spec (CommRingCat.of k)) [IsReduced X]
    (i₁ : Y₁ ⟶ X) (i₂ : Y₂ ⟶ X) [IsClosedImmersion i₁] [IsClosedImmersion i₂]
    (hcover : Set.range i₁.base ∪ Set.range i₂.base = Set.univ)
    (F : X.Modules) (hF : Scheme.Modules.IsInvertible F) (𝒲 : X.TwoAffineOpenCover)
    [Module.Finite k ((H0Sum.comap 𝒲 i₁).sectionsOf (i₁ ≫ x) ((Scheme.Modules.pullback i₁).obj F)).H0]
    [Module.Finite k ((H0Sum.comap 𝒲 i₂).sectionsOf (i₂ ≫ x) ((Scheme.Modules.pullback i₂).obj F)).H0] :
    Module.finrank k (𝒲.sectionsOf x F).H0 ≤
      Module.finrank k ((H0Sum.comap 𝒲 i₁).sectionsOf (i₁ ≫ x) ((Scheme.Modules.pullback i₁).obj F)).H0 +
      Module.finrank k ((H0Sum.comap 𝒲 i₂).sectionsOf (i₂ ≫ x) ((Scheme.Modules.pullback i₂).obj F)).H0 := by
  let S := 𝒲.sectionsOf x F

  have mk : ∀ {Y : Scheme.{u}} (i : Y ⟶ X) [IsClosedImmersion i],
      ∃ f : S.H0 →ₗ[k] ((H0Sum.comap 𝒲 i).sectionsOf (i ≫ x) ((Scheme.Modules.pullback i).obj F)).H0,
        ∀ s : S.H0, (f s).1.1 = res i F 𝒲.U0 s.1.1 ∧ (f s).1.2 = res i F 𝒲.U1 s.1.2 := by
    intro Y i _
    let S' := (H0Sum.comap 𝒲 i).sectionsOf (i ≫ x) ((Scheme.Modules.pullback i).obj F)
    let φ : (S.M0 × S.M1) →ₗ[k] (S'.M0 × S'.M1) :=
      (show S.M0 →ₗ[k] S'.M0 from resₗ i x F 𝒲.U0).prodMap (show S.M1 →ₗ[k] S'.M1 from resₗ i x F 𝒲.U1)
    have hφ : ∀ s ∈ S.H0, φ s ∈ S'.H0 := by
      rintro ⟨m0, m1⟩ hs
      rw [TwoChartCech.Sections.mem_H0_iff] at hs ⊢
      change S'.r0 (res i F 𝒲.U0 m0) = S'.r1 (res i F 𝒲.U1 m1)
      change ((H0Sum.comap 𝒲 i).sectionsOf (i ≫ x) ((Scheme.Modules.pullback i).obj F)).r0 _ =
        ((H0Sum.comap 𝒲 i).sectionsOf (i ≫ x) ((Scheme.Modules.pullback i).obj F)).r1 _
      rw [Scheme.TwoAffineOpenCover.sectionsOf_r0_apply, Scheme.TwoAffineOpenCover.sectionsOf_r1_apply]
      have hs' : (𝒲.sectionsOf x F).r0 m0 = (𝒲.sectionsOf x F).r1 m1 := hs
      rw [Scheme.TwoAffineOpenCover.sectionsOf_r0_apply, Scheme.TwoAffineOpenCover.sectionsOf_r1_apply] at hs'
      have := congrArg (res i F (𝒲.U0 ⊓ 𝒲.U1)) hs'
      rw [res_map, res_map] at this
      exact this
    exact ⟨φ.restrict hφ, fun s => ⟨rfl, rfl⟩⟩
  obtain ⟨f₁, hf₁⟩ := mk i₁
  obtain ⟨f₂, hf₂⟩ := mk i₂
  have hinj : Function.Injective (f₁.prod f₂) := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro s hs
    have hs₁ : f₁ s = 0 := congrArg Prod.fst hs
    have hs₂ : f₂ s = 0 := congrArg Prod.snd hs
    have a₁ := hf₁ s
    have a₂ := hf₂ s
    rw [hs₁] at a₁
    rw [hs₂] at a₂
    have e0 : s.1.1 = 0 :=
      eq_zero_of_res_eq_zero i₁ i₂ hcover F hF 𝒲.U0 _ a₁.1.symm a₂.1.symm
    have e1 : s.1.2 = 0 :=
      eq_zero_of_res_eq_zero i₁ i₂ hcover F hF 𝒲.U1 _ a₁.2.symm a₂.2.symm
    exact Subtype.ext (Prod.ext e0 e1)
  calc Module.finrank k (𝒲.sectionsOf x F).H0
      ≤ Module.finrank k (((H0Sum.comap 𝒲 i₁).sectionsOf (i₁ ≫ x) ((Scheme.Modules.pullback i₁).obj F)).H0 ×
          ((H0Sum.comap 𝒲 i₂).sectionsOf (i₂ ≫ x) ((Scheme.Modules.pullback i₂).obj F)).H0) :=
        LinearMap.finrank_le_finrank_of_injective hinj
    _ = _ := Module.finrank_prod

theorem main {k : Type u} [Field k] [IsAlgClosed k]
    {X C₁ C₂ : Scheme.{u}} (x : X ⟶ Spec (CommRingCat.of k)) [IsProper x] (hXred : IsReduced X)
    (c₁ : C₁ ⟶ Spec (CommRingCat.of k)) (c₂ : C₂ ⟶ Spec (CommRingCat.of k))
    [IsProper c₁] [SmoothOfRelativeDimension 1 c₁] [GeometricallyIntegral c₁]
    [IsProper c₂] [SmoothOfRelativeDimension 1 c₂] [GeometricallyIntegral c₂]
    (i₁ : SchemeHomOver c₁ x) (i₂ : SchemeHomOver c₂ x) [IsClosedImmersion i₁.1] [IsClosedImmersion i₂.1]
    (hjs : ∀ z : X, z ∈ Set.range i₁.1.base ∨ z ∈ Set.range i₂.1.base)
    (L : X.Modules) (hL : Scheme.Modules.IsInvertible L) (h0 : IsAlgEquivZero x L)
    (𝒲 : X.TwoAffineOpenCover)
    (hH0 : Module.finrank k (𝒲.sectionsOf x (SheafOfModules.unit X.ringCatSheaf : X.Modules)).H0 = 1) :
    Module.finrank k (𝒲.sectionsOf x L).H1 ≤
      Module.finrank k (𝒲.sectionsOf x (SheafOfModules.unit X.ringCatSheaf : X.Modules)).H1 + 1 := by
  haveI := hXred
  obtain ⟨j₁, hj₁⟩ := i₁
  obtain ⟨j₂, hj₂⟩ := i₂
  subst hj₁
  subst hj₂
  have hcover : Set.range j₁.base ∪ Set.range j₂.base = Set.univ :=
    Set.eq_univ_of_forall fun z => hjs z

  have hχ := RelPicard.IsAlgEquivZero.eulerChar_sectionsOf_tensor_eq x 𝒲 L (SheafOfModules.unit X.ringCatSheaf) hL
    (Scheme.Modules.isInvertible_unit X) h0
  obtain ⟨hρ0, hρ1⟩ := finrank_H0_H1_sectionsOf_eq_of_iso x (ρ_ L) 𝒲
  change Module.finrank k (𝒲.sectionsOf x (L ⊗ SheafOfModules.unit X.ringCatSheaf)).H0 = _ at hρ0
  change Module.finrank k (𝒲.sectionsOf x (L ⊗ SheafOfModules.unit X.ringCatSheaf)).H1 = _ at hρ1
  rw [hρ0, hρ1] at hχ

  haveI := finite_H0 (j₁ ≫ x) ((Scheme.Modules.pullback j₁).obj L) (hL.pullback j₁) (H0Sum.comap 𝒲 j₁)
  haveI := finite_H0 (j₂ ≫ x) ((Scheme.Modules.pullback j₂).obj L) (hL.pullback j₂) (H0Sum.comap 𝒲 j₂)
  have hsum := finrank_H0_le_add x j₁ j₂ hcover L hL 𝒲
  have b₁ := finrank_H0_le_one_of_isAlgEquivZero (j₁ ≫ x) ((Scheme.Modules.pullback j₁).obj L) (hL.pullback j₁)
    (h0.pullback j₁ rfl) (H0Sum.comap 𝒲 j₁)
  have b₂ := finrank_H0_le_one_of_isAlgEquivZero (j₂ ≫ x) ((Scheme.Modules.pullback j₂).obj L) (hL.pullback j₂)
    (h0.pullback j₂ rfl) (H0Sum.comap 𝒲 j₂)
  rw [hH0] at hχ
  omega

end AlgebraicGeometry.N2bCoreFwd

end

theorem solution
    {k : Type u} [Field k] [IsAlgClosed k]
    {X C₁ C₂ : Scheme.{u}} (x : X ⟶ Spec (CommRingCat.of k)) [IsProper x] (hXred : IsReduced X)
    (c₁ : C₁ ⟶ Spec (CommRingCat.of k)) (c₂ : C₂ ⟶ Spec (CommRingCat.of k))
    [IsProper c₁] [SmoothOfRelativeDimension 1 c₁] [GeometricallyIntegral c₁]
    [IsProper c₂] [SmoothOfRelativeDimension 1 c₂] [GeometricallyIntegral c₂]
    (i₁ : SchemeHomOver c₁ x) (i₂ : SchemeHomOver c₂ x) [IsClosedImmersion i₁.1] [IsClosedImmersion i₂.1]
    (hjs : ∀ z : X, z ∈ Set.range i₁.1.base ∨ z ∈ Set.range i₂.1.base)
    (L : X.Modules) (hL : Scheme.Modules.IsInvertible L) (h0 : IsAlgEquivZero x L)
    (𝒲 : X.TwoAffineOpenCover)
    (hH0 : Module.finrank k (𝒲.sectionsOf x (SheafOfModules.unit X.ringCatSheaf : X.Modules)).H0 = 1) :
    Module.finrank k (𝒲.sectionsOf x L).H1 ≤
      Module.finrank k (𝒲.sectionsOf x (SheafOfModules.unit X.ringCatSheaf : X.Modules)).H1 + 1 :=
  AlgebraicGeometry.N2bCoreFwd.main x hXred c₁ c₂ i₁ i₂ hjs L hL h0 𝒲 hH0

end S_AlgebraicGeometry_RelPicard_finrank_H1_le_finrank_H1_unit_add_one_of_isAlgEquivZero_of_twoGluedSmoothCurves
end P2MW
export P2MW.S_AlgebraicGeometry_RelPicard_finrank_H1_le_finrank_H1_unit_add_one_of_isAlgEquivZero_of_twoGluedSmoothCurves (solution)
