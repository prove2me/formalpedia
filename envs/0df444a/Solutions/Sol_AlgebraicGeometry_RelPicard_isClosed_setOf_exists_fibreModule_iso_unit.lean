-- Prove2me | solution 1 for AlgebraicGeometry.RelPicard.isClosed_setOf_exists_fibreModule_iso_unit
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:03.589526+00:00
-- url     : https://prove2.me/submissions/133e853e-11e3-51fc-85cd-788190d5aae4

import Mathlib
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import Definitions.Def_AlgebraicGeometry_RepresentsRelSubPic
import Definitions.Def_AlgebraicGeometry_RelPicardAlgEquivZeroCut
import Definitions.Def_AlgebraicGeometry_RelSubPicPresheaf
import Definitions.Def_JacJ1Iface
import Definitions.Def_AlgebraicGeometry_SmoothProperCurveFiniteMapData
import Definitions.Def_AlgebraicCurve_CurveModel
import Definitions.Def_AlgebraicCurve_AdelicIndex
import Definitions.Def_AlgebraicGeometry_RelPicardThetaBundle
import Definitions.Def_SheafOfModules_Monoidal
import Definitions.Def_AlgebraicGeometry_TwoAffineOpenCover
import Definitions.Def_AlgebraicGeometry_TwoChartCechSectionsOf
import Definitions.Def_AlgebraicGeometry_ModulesPullbackMonoidal
import Definitions.Def_AlgebraicGeometry_OModulePresheafOfModules
import Theorems.Thm_AlgebraicGeometry_RelPicard_exists_twoAffineOpenCover_fibre_finrank_eq_finrank_cechDiff_baseChange_residueField
import Theorems.Thm_TwoChartCech_isClosed_setOf_le_finrank_ker_baseChange
import Theorems.Thm_AlgebraicGeometry_Scheme_TwoAffineOpenCover_flat_sections_of_flat
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_projective_sections_of_locallyTrivial
import Theorems.Thm_AlgebraicGeometry_OModulePresheaf_cechFinite_ofModules_of_locallyTrivial
import Theorems.Thm_AlgebraicGeometry_OModulePresheaf_cechFinite_toOrderedAffineCover_iff
import Theorems.Thm_AlgebraicGeometry_Scheme_TwoAffineOpenCover_exists_linearEquiv_sectionsOf_of_iso
import Theorems.Thm_AlgebraicGeometry_RelPicard_finrank_H0_unit_fibre_eq_one
import Theorems.Thm_AlgebraicGeometry_Scheme_TwoAffineOpenCover_exists_linearEquiv_sectionsOf_H0
import Theorems.Thm_AlgebraicGeometry_RelPicard_IsAlgEquivZero_nonempty_iso_tensorUnit_of_ne_zero
import Theorems.Thm_AlgebraicGeometry_geometricallyIntegral_of_isAlgClosed
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_RelPicard_isClosed_setOf_exists_fibreModule_iso_unit
p2m_attr_erase "instance" "AlgebraicGeometry.OModulePresheaf.instSubsingletonObjZero AlgebraicGeometry.OModulePresheaf.Leray.relAltC_scalarTower AlgebraicGeometry.OModulePresheaf.Leray.ker_relAltd_modΓ AlgebraicGeometry.OModulePresheaf.Leray.relAltC_modΓ AlgebraicGeometry.OModulePresheaf.Leray.biC_abGrp AlgebraicGeometry.OModulePresheaf.Leray.relAltH_modΓ AlgebraicGeometry.OModulePresheaf.Leray.ker_relAltd_smul AlgebraicGeometry.OModulePresheaf.Leray.relAltH_scalarTower AlgebraicGeometry.OModulePresheaf.Leray.relAltH_smul AlgebraicGeometry.OModulePresheaf.Leray.biC_module AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instDecidableEqIdx AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instFintype AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instLinearOrder AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instFintypeIdx DoubleComplex.instModuleE₂I DoubleComplex.Bounded.modR DoubleComplex.instModuleE₂II DoubleComplex.instAddCommGroupE₂II DoubleComplex.Bounded.abGrp DoubleComplex.instAddCommGroupE₂I AlgebraicGeometry.ChowDatum.hι_closed AlgebraicGeometry.ChowDatumProj.hιN_closed AlgebraicGeometry.ChowDatumProj.hp_proper AlgebraicGeometry.ChowDatum.hp_isoU AlgebraicGeometry.ChowDatum.hp_proper AlgebraicGeometry.ProjSpace.algebraAway AlgebraicGeometry.ProjSpace.instIsProperProdOverπ AlgebraicGeometry.ChowDatumProj.hp_isoU AlgebraicGeometry.ProjSpace.isProper_π AlgebraicGeometry.ProjSpace.finiteType_mvPolynomial ProjSpaceCech.GradedModule.H.module ProjSpaceCech.GradedModule.H.addCommGroup ProjSpaceCech.GradedModule.sec.instAdd ProjSpaceCech.GradedModule.sec.instNeg ProjSpaceCech.GradedModule.acg ProjSpaceCech.GradedModule.Frac.setoid ProjSpaceCech.GradedModule.modR ProjSpaceCech.GradedModule.sec.instModule ProjSpaceCech.GradedModule.sec.instAddCommGroup ProjSpaceCech.GradedModule.sec.instZero"
p2m_attr_erase "instance" "ProjSpaceCech.GradedModule.Presentation.fJ ProjSpaceCech.GradedModule.sec.instSMul ProjSpaceCech.Twist.H.module ProjSpaceCech.Idx.instFintype ProjSpaceCech.Twist.H.addCommGroup ProjSpaceCech.Idx.instDecidableEq ProjSpaceCech.Twist.Mon.instDecidableEq ProjSpaceCech.Twist.cochain.instAddCommGroup ProjSpaceCech.Twist.cochain.instModule AlgebraicGeometry.SmoothOfRelativeDimension.fiberToSpecResidueField AlgebraicGeometry.SmoothOfRelativeDimension.pullback_snd AlgebraicGeometry.SmoothOfRelativeDimension.pullback_fst AlgebraicGeometry.SmoothOfRelativeDimension.smooth_one AlgebraicGeometry.SmoothProperCurve.isIntegral_pullback_Spec_field AlgebraicGeometry.IsProper.fiberToSpecResidueField AlgebraicGeometry.RelEffCartierDiv.isIso_subschemeIota_snd_of_degree_one AlgebraicGeometry.isIso_ker_graphOver_subschemeIota_snd AlgebraicGeometry.isClosedImmersion_graphOver AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instNeg AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instSMulInt AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instAddCommGroup AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instAdd AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instSub AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instModuleCarrierObjOppositeOpensCarrierCarrierCommRingCatPresheafOpOpensTop AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instSMulCarrierObjOppositeOpensCarrierCarrierCommRingCatPresheafOpOpensTop AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instSMulNat AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instZero AlgebraicCurve.IsCurveOver.instNontrivialKaehler AlgebraicCurve.IsCurveOver.instFreeKaehler AlgebraicCurve.IsCurveOver.toHasPrincipalDivisors AlgebraicCurve.IsCurveOver.instFiniteResidue AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.instFundamentalIdentityOfSumRamificationInertia AlgebraicCurve.Place.instIsScalarTowerResidueFieldRestrictPushforward AlgebraicCurve.Place.instAlgebraResidueFieldRestrictPushforward AlgebraicCurve.Place.instIsLocalHomRestrictInclusion AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt"
p2m_attr_erase "instance" "AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.SemilinearAut.instDistribMulActionSubtypeProdRingAutMemSubgroupPic0 AlgebraicCurve.SemilinearAut.instDistribMulActionSubtypeProdRingAutMemSubgroupDivisor AlgebraicCurve.Pic0.instModuleZModTorsion AlgebraicCurve.SemilinearAut.instSMulSubtypeProdRingAutMemSubgroupPlace AlgebraicCurve.SemilinearAut.instDistribMulActionTorsion AlgebraicCurve.SemilinearAut.instSMulSubtypeProdRingAutMemSubgroupPic0 AlgebraicCurve.SemilinearAut.instSMulTorsion AlgebraicCurve.SemilinearAut.instMulActionSubtypeProdRingAutMemSubgroupPlace AlgebraicCurve.SemilinearAut.instSMulCommClassZModTorsion AlgebraicCurve.SemilinearAut.instMulSemiringActionSubtypeProdRingAutMemSubgroup instDecEqAlgebraicClosureRat WeierstrassCurve.Affine.Point.instDistribMulActionAlgEquiv WeierstrassCurve.Affine.Point.instModuleZModTorsionBy WeierstrassCurve.Affine.Point.instSMulTorsionBy WeierstrassCurve.Affine.Point.instDistribMulActionTorsionBy WeierstrassCurve.Affine.Point.instSMulAlgEquiv WeierstrassCurve.Affine.Point.instSMulCommClassAlgEquivZModTorsionBy AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions AlgebraicCurve.instHasLocalResidue_of_hasCanonicalLocalResidueK AlgebraicCurve.instHasCanonicalLocalResidueK_of_hasCanonicalLocalResidueKStar AlgebraicCurve.Place.kw_ffgc_finiteDimensional_adicCompletion instAlgebraSubtypeMemValuationSubring_definitions AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersIntegersCompletion ModularCurve.KwF4gRRTate.instAlgebraKAdicCompletionIntegers AlgebraicCurve.Place.kw_ffgc_continuousSMul_adicCompletionComap AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersCompletionCompletion IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions AlgebraicCurve.instHasCanonicalLocalResidueK AlgebraicCurve.Place.instAlgebra_restrictResidueField AlgebraicCurve.Place.instIsScalarTower_restrictResidueField AlgebraicCurve.instHasLocalResidue AlgebraicCurve.HasSeparableResidue.of_perfectField_of_isCurveOver AlgebraicCurve.HasSeparableResidue.of_perfectField"
p2m_attr_erase "instance" "AlgebraicCurve.Place.instIsLocalHom_restrictSubringHom AlgebraicCurve.instHasCanonicalLocalResidueKStar ModularCurve.KwNo6Pin.isLocalRing_completion AlgebraicGeometry.RelEffCartierDiv.subsingleton_of_degree_zero SheafOfModules.isIso_ihomModelToIhom"
p2m_attr_erase "simp" "AlgebraicGeometry.tilde.functorCompPullbackSpecIso_app CoherentBaseChange.FibreH0Family.mk.sizeOf_spec CoherentBaseChange.FibreH0Family.mk.injEq AlgebraicGeometry.OModulePresheaf.prod_obj AlgebraicGeometry.OModulePresheaf.restrOpen_obj AlgebraicGeometry.OModulePresheaf.DevissageStep.mk.injEq AlgebraicGeometry.OModulePresheaf.pushforward_obj AlgebraicGeometry.OModulePresheaf.im_obj AlgebraicGeometry.OModulePresheaf.pow_obj AlgebraicGeometry.OModulePresheaf.fstHom_app AlgebraicGeometry.OModulePresheaf.ker_obj AlgebraicGeometry.OModulePresheaf.coker_obj AlgebraicGeometry.OModulePresheaf.DevissageStep.mk.sizeOf_spec AlgebraicGeometry.Scheme.OrderedAffineCover.preimage_U AlgebraicGeometry.OModulePresheaf.sndHom_app AlgebraicGeometry.OModulePresheaf.Hom.mk.injEq AlgebraicGeometry.OModulePresheaf.Hom.id_app AlgebraicGeometry.OModulePresheaf.AffHom.appSections_apply AlgebraicGeometry.OModulePresheaf.AffHom.comp_app AlgebraicGeometry.OModulePresheaf.AffSES.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.AffHom.kerMap_coe AlgebraicGeometry.OModulePresheaf.AffHom.id_app AlgebraicGeometry.OModulePresheaf.Hom.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.Hom.toAffHom_app AlgebraicGeometry.OModulePresheaf.SES.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.AffHom.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.Hom.comp_app AlgebraicGeometry.OModulePresheaf.SES.mk.injEq AlgebraicGeometry.OModulePresheaf.AffHom.mk.injEq AlgebraicGeometry.OModulePresheaf.Hom.appSections_apply AlgebraicGeometry.OModulePresheaf.AffSES.mk.injEq AlgebraicGeometry.OModulePresheaf.Leray.restrictToPreimage_U AlgebraicGeometry.Scheme.OrderedAffineCover.toCoverOf_U AlgebraicGeometry.Scheme.OrderedAffineCoverOf.mk.sizeOf_spec AlgebraicGeometry.Scheme.OrderedAffineCoverOf.mk.injEq AlgebraicGeometry.Scheme.OrderedAffineCover.restrict_U DoubleComplex.Bounded.mk.injEq DoubleComplex.Bounded.mk.sizeOf_spec DoubleComplex.Convergence.mk.injEq DoubleComplex.Convergence.mk.sizeOf_spec"
p2m_attr_erase "simp" "DoubleComplex.SubQuot.mk.sizeOf_spec DoubleComplex.SubQuot.mk.injEq AlgebraicGeometry.ChowDatumProj.mk.sizeOf_spec AlgebraicGeometry.ChowDatum.mk.sizeOf_spec AlgebraicGeometry.ChowDatumProj.mk.injEq AlgebraicGeometry.ChowDatum.mk.injEq ProjSpaceCech.GradedModule.mk.injEq ProjSpaceCech.GradedModule.mk.sizeOf_spec ProjSpaceCech.GradedModule.Frac.mk.sizeOf_spec ProjSpaceCech.GradedModule.Presentation.mk.injEq ProjSpaceCech.GradedModule.Frac.mk.injEq ProjSpaceCech.GradedModule.Presentation.mk.sizeOf_spec ProjSpaceCech.GradedModule.Hom.shift_toLinearMap ProjSpaceCech.GradedModule.Hom.mk.sizeOf_spec ProjSpaceCech.GradedModule.Hom.mk.injEq AlgebraicGeometry.SmoothProperCurve.sectionBaseChange_coe_snd AlgebraicGeometry.SmoothProperCurve.sectionBaseChange_coe_fst AlgebraicGeometry.RelPicard.fst_toProdSpec AlgebraicGeometry.RelPicard.toProdSpec_fst_assoc AlgebraicGeometry.RelPicard.pointsSubBasepointModule_cons AlgebraicGeometry.RelPicard.pointsSubBasepointModule_nil AlgebraicGeometry.RelPicard.fst_toProdSpec_assoc AlgebraicGeometry.RelPicard.toProdSpec_fst AlgebraicGeometry.graphOver_fst_assoc AlgebraicGeometry.RelEffCartierDiv.toPoint_comp AlgebraicGeometry.RelEffCartierDiv.toPoint_comp_assoc AlgebraicGeometry.graphOver_fst AlgebraicGeometry.RelEffCartierDiv.ofPoint_I AlgebraicGeometry.graphOver_snd AlgebraicGeometry.graphOver_snd_assoc AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.sub_app AlgebraicGeometry.Scheme.IdealSheafData.sres_sresTop AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.add_app AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.mk.sizeOf_spec AlgebraicGeometry.Scheme.IdealSheafData.coe_resLE AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.smul_app AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.coe_ofLE_app AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.ideal_range AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.zero_app AlgebraicGeometry.Scheme.IdealSheafData.sres_sres"
p2m_attr_erase "simp" "AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.comp_app AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.neg_app AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.id_app AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.coe_mulRight_app AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.nsmul_app AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.mk.injEq AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.zsmul_app AlgebraicCurve.coe_cechH0Equiv_apply AlgebraicCurve.cechH1ToH1_mk AlgebraicCurve.lSpaceOn_univ AlgebraicCurve.lSpaceOn_empty AlgebraicCurve.Place.congrEquiv_symm_apply AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply AlgebraicCurve.RationalFunctionField.deg_placeOfPoint AlgebraicCurve.Divisor.mapRestrict_single AlgebraicCurve.Divisor.pushforward_single AlgebraicCurve.Place.coe_restrictInclusion AlgebraicCurve.Place.mem_fiber AlgebraicCurve.Place.restrict_toValuationSubring AlgebraicCurve.Divisor.degree_pushforward AlgebraicCurve.Place.restrictResidueMap_residue AlgebraicCurve.Pic0.coe_pushforwardDegZeroHom AlgebraicCurve.Pic0.coe_pullbackDegZeroHom AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal AlgebraicCurve.IsFrobeniusEndo.frobNormRingHom_apply ModularCurve.frobeniusPushforwardGeomLevelPic0_mk ModularCurve.coe_frobeniusGeomLevelEquiv_apply ModularCurve.coe_frobeniusPushforwardGeomLevelDegZero ModularCurve.heckeFibreGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusGeomLevel_apply_coe ModularCurve.frobeniusPullbackGeomLevelPic0OfIsCurveOver_mk ModularCurve.coe_heckeFibreGeomLevelDegZero ModularCurve.coe_frobeniusPullbackGeomLevelDegZero"
p2m_attr_erase "simp" "ModularCurve.frobeniusPullbackGeomLevelPic0_mk ModularCurve.frobeniusPullbackGeomLevel_single ModularCurve.heckeFibreGeomLevelPic0_mk ModularCurve.frobeniusPushforwardGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusPushforwardGeomLevel_single ModularCurve.qExpandAlgC_apply AlgebraicCurve.Divisor.degree_pushforwardAlong AlgebraicCurve.Pic0.coe_degZeroCorrespondence AlgebraicCurve.Place.mem_fiberAlong AlgebraicCurve.SemilinearAut.toRingAut_inv AlgebraicCurve.SemilinearAut.smul_def AlgebraicCurve.SemilinearAut.smul_single AlgebraicCurve.SemilinearAut.smul_toValuationSubring AlgebraicCurve.SemilinearAut.baseAut_inv AlgebraicCurve.SemilinearAut.baseAut_ofAlgAut AlgebraicCurve.SemilinearAut.toRingAut_ofAlgAut AlgebraicCurve.SemilinearAut.torsionRep_apply AlgebraicCurve.SemilinearAut.toRingAut_one AlgebraicCurve.SemilinearAut.deg_smul AlgebraicCurve.SemilinearAut.degree_smul AlgebraicCurve.SemilinearAut.coe_degZeroSMulHom AlgebraicCurve.SemilinearAut.baseAut_mul AlgebraicCurve.SemilinearAut.coe_smulValuationSubringEquiv_apply AlgebraicCurve.SemilinearAut.baseAut_one AlgebraicCurve.SemilinearAut.ofAlgAut_smul AlgebraicCurve.SemilinearAut.coe_torsion_smul AlgebraicCurve.SemilinearAut.toRingAut_mul AlgebraicCurve.coe_frobeniusPushforwardDegZero AlgebraicCurve.IsFrobeniusEndo.coe_frobeniusPullbackDegZero ModularCurve.jqNModC_one ModularCurve.qExpand_coeff_mul ModularCurve.qExpandₐ_apply ModularCurve.jqN_one ModularCurve.qExpand_single ModularCurve.dedekindPsi_one ModularCurve.ModularPolynomialData.mk.sizeOf_spec ModularCurve.evalAtJ_X ModularCurve.ModularPolynomialData.mk.injEq ModularCurve.constantCoeff_jNum ModularCurve.constantCoeff_eisenstein4"
p2m_attr_erase "simp" "ModularCurve.qExpand_C ModularCurve.coeff_jq_neg_one ModularCurve.constantCoeff_jNumQ ModularCurve.reduceModBivar_C_X ModularCurve.laurentMap_coeff ModularCurve.reduceModBivar_X ModularCurve.laurentMap_single ModularCurve.evalAtJInt_X ModularCurve.evalAtJMod_X ModularCurve.jqNMod_one ModularCurve.aeval_heckeGen ModularCurve.coe_mTorsionGaloisRep_apply ModularCurve.eisensteinSystem_of_dvd ModularCurve.eisensteinSystem_of_not_dvd FreyPackage.mk.sizeOf_spec FreyPackage.mk.injEq WeierstrassCurve.Affine.Point.galoisRepModuleEnd_apply AlgebraicCurve.RationalFunctionField.placeInfty_toValuationSubring AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none AlgebraicCurve.Divisor.evalFun_zero AlgebraicCurve.Place.evalAt_one AlgebraicCurve.Place.differentialCoeff_zero AlgebraicCurve.Place.differentialCoeff_dCoord AlgebraicCurve.TranscendenceTower.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.injEq AlgebraicCurve.TranscendenceTower.mk.injEq AlgebraicCurve.PoleDivisorPackage.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.sizeOf_spec AlgebraicCurve.PoleDivisorPackage.mk.injEq AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.sizeOf_spec AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.injEq AlgebraicCurve.adeleSingle_coe AlgebraicCurve.kaehlerResidueTermKFam_apply AlgebraicCurve.Place.LocalResidueData.mk.injEq AlgebraicCurve.Place.LocalResidueData.mk.sizeOf_spec AlgebraicCurve.Place.kw_ffgc_adicCompletionComapIntegers_coe AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.sizeOf_spec"
p2m_attr_erase "simp" "AlgebraicCurve.Place.mem_simplePoleSubmodule AlgebraicCurve.Place.coe_uniformizerSubring ModularCurve.Lg37.Lg37CompletionSection.mk.injEq AlgebraicCurve.Place.CoefficientFieldSection.mk.injEq AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.injEq ModularCurve.Lg37.Lg37CompletionSection.mk.sizeOf_spec AlgebraicCurve.Place.CoefficientFieldSection.mk.sizeOf_spec AlgebraicCurve.Place.poleSubmodule_one AlgebraicCurve.Place.mem_poleSubmodule AlgebraicGeometry.Scheme.Modules.toUnitSection_ofUnitSection AlgebraicGeometry.Scheme.Modules.pullbackSection_def AlgebraicGeometry.Scheme.Modules.ofUnitSection_toUnitSection AlgebraicGeometry.prodKerGraph_one AlgebraicGeometry.fibrePowOver.proj_comp AlgebraicGeometry.prodKerGraph_zero AlgebraicGeometry.RelEffCartierDiv.empty_I AlgebraicGeometry.fibrePowOver.proj_comp_assoc AlgebraicCurve.SymmetricPowerPackage.mk.sizeOf_spec AlgebraicCurve.SymmetricPowerPackage.mk.injEq PresheafOfModules.InternalHom.IsSheafAux.appAt_toPresheafHom SheafOfModules.ihomSectionsEquivFamily_unit AlgebraicGeometry.Scheme.Modules.restrictHomEquivFamily_apply SheafOfModules.ihomEval_unit_app AlgebraicGeometry.Scheme.Modules.ihomEval_zero_right AlgebraicGeometry.Scheme.Modules.ihomEval_zero_left AlgebraicGeometry.Scheme.Modules.homOfFamily_app_apply SheafOfModules.unit_ihomSectionsEquivFamily AlgebraicGeometry.Scheme.Modules.familyOfHom_app AlgebraicGeometry.Scheme.Modules.restrictUnitIso_hom_app_apply AlgebraicGeometry.Scheme.Modules.restrictUnitIso_inv_app_apply AlgebraicGeometry.Scheme.Modules.restrictHomOfFamily_app_apply AlgebraicGeometry.Scheme.Modules.restrictHomEquivFamily_symm_apply AlgebraicGeometry.Scheme.Modules.tensorSections_zero_right AlgebraicGeometry.Scheme.Modules.map_unitSection AlgebraicGeometry.Scheme.Modules.tensorSectionsBilin_apply AlgebraicGeometry.Scheme.Modules.tensorPowSection_zero AlgebraicGeometry.Scheme.Modules.tensorSections_zero_left AlgebraicGeometry.Scheme.Modules.tensorPow_zero AlgebraicGeometry.Scheme.Modules.tensorPow_succ AlgebraicGeometry.Scheme.Modules.pullbackLocalSection_neg"
p2m_attr_erase "simp" "AlgebraicGeometry.Scheme.Modules.pullbackLocalSection_zero AlgebraicGeometry.Scheme.Modules.pullbackLocalSection_sub AlgebraicGeometry.Scheme.Modules.pullbackLocalSection_add TwoChartCech.Mumford.dK_apply TwoChartCech.Mumford.ι0_apply TwoChartCech.Mumford.ι1_apply TwoChartCech.KerCoprod.dK_apply TwoChartCech.KerCoprod.ι1_apply TwoChartCech.KerCoprod.ι0_apply"

set_option autoImplicit false

universe u

p2m_open "CategoryTheory CategoryTheory.Limits AlgebraicGeometry P2MW.S_AlgebraicGeometry_RelPicard_isClosed_setOf_exists_fibreModule_iso_unit.AlgebraicGeometry AlgebraicGeometry.RelPicard P2MW.S_AlgebraicGeometry_RelPicard_isClosed_setOf_exists_fibreModule_iso_unit.AlgebraicGeometry.RelPicard NeronModelInfra GoodReductionJacobian AlgebraicCurve~cechDiff CategoryTheory.MonoidalCategory"

noncomputable section

namespace AlgebraicGeometry
p2m_export "AlgebraicGeometry" "Spec.map_comp IsLocallyNoetherian SmoothOfRelativeDimension.smooth Scheme.Modules.Hom.zero_app SmoothOfRelativeDimension IsProper Scheme.Modules.pullback LocallyOfFiniteType.isLocallyNoetherian GeometricallyIntegral.geometrically_isIntegral GeometricallyIntegral Scheme.Modules.presheaf IsAffineOpen.fromSpec_top Scheme.Modules.Hom IsAffineOpen.SpecMap_appLE_fromSpec LocallyOfFiniteType Spec IsIntegral Scheme Smooth Scheme.Modules.Hom.app Scheme.isoSpec_Spec_inv Flat IsLocallyNoetherian.component_noetherian smoothOfRelativeDimension_isStableUnderBaseChange exists_isAffineOpen_mem_and_subset isAffineOpen_top Scheme.Modules.pullbackId IsAffineOpen Scheme.Modules geometrically Scheme.ΓSpecIso Scheme.Modules.IsInvertible Scheme.Modules.isInvertible_unit SmoothProperCurve.FiniteMapData Scheme.TwoAffineOpenCover Scheme.TwoAffineOpenCover.specMap Scheme.TwoAffineOpenCover.algebraOfHom Scheme.TwoAffineOpenCover.moduleSectionsOfHom Scheme.TwoAffineOpenCover.isScalarTower_sections Scheme.Modules.pullbackTensorUnitObjIso OModulePresheaf Scheme.TwoAffineOpenCover.flat_sections_of_flat Scheme.Modules.projective_sections_of_locallyTrivial OModulePresheaf.cechFinite_ofModules_of_locallyTrivial OModulePresheaf.cechFinite_toOrderedAffineCover_iff Scheme.TwoAffineOpenCover.exists_linearEquiv_sectionsOf_of_iso Scheme.TwoAffineOpenCover.exists_linearEquiv_sectionsOf_H0 geometricallyIntegral_of_isAlgClosed"
namespace RelPicard
p2m_export "AlgebraicGeometry.RelPicard" "RigidifiedLineBundle fibreAt IsAlgEquivZero FibrewiseAlgEquivZero fibreModule exists_twoAffineOpenCover_fibre_finrank_eq_finrank_cechDiff_baseChange_residueField finrank_H0_unit_fibre_eq_one IsAlgEquivZero.nonempty_iso_tensorUnit_of_ne_zero"
namespace UnitClosed
p2m_open "AlgebraicGeometry.RelPicard AlgebraicGeometry"

open TensorProduct Opposite

theorem cover_ext {X : Scheme.{u}} {𝒱 𝒱' : X.TwoAffineOpenCover}
    (h0 : 𝒱.U0 = 𝒱'.U0) (h1 : 𝒱.U1 = 𝒱'.U1) : 𝒱 = 𝒱' := by
  cases 𝒱; cases 𝒱'; cases h0; cases h1; rfl

theorem finrank_H0_congr {k : Type u} [Field k] {X : Scheme.{u}} (x : X ⟶ Spec (CommRingCat.of k))
    (𝒱 : X.TwoAffineOpenCover) {M M' : X.Modules} (e : M ≅ M') :
    Module.finrank k (𝒱.sectionsOf x M).H0 = Module.finrank k (𝒱.sectionsOf x M').H0 := by
  obtain ⟨𝒱₂, h0, h1, ⟨e0⟩, -⟩ :=
    Scheme.TwoAffineOpenCover.exists_linearEquiv_sectionsOf_of_iso x x (Iso.refl X) (Category.id_comp x)
      𝒱 M' M (e ≪≫ ((Scheme.Modules.pullbackId X).app M').symm)
  obtain rfl : 𝒱₂ = 𝒱 := cover_ext h0 h1
  exact e0.finrank_eq

theorem specMap_residueField_base {A : Type u} [CommRing A] (𝔭 : PrimeSpectrum A)
    (p : Spec (CommRingCat.of 𝔭.asIdeal.ResidueField)) :
    (Scheme.TwoAffineOpenCover.specMap A 𝔭.asIdeal.ResidueField).base p = 𝔭 := by
  apply PrimeSpectrum.ext
  have hp : p.asIdeal = ⊥ := (Ideal.eq_bot_or_top _).resolve_right p.isPrime.ne_top
  change Ideal.comap (algebraMap A 𝔭.asIdeal.ResidueField) p.asIdeal = 𝔭.asIdeal
  rw [hp, ← RingHom.ker_eq_comap_bot, Ideal.ker_algebraMap_residueField]

def sectionOfGlobal {X : Scheme.{u}} (M : X.Modules) (σ : Γ(M, ⊤)) : M.val.sections :=
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

theorem flat_prod {S : Type*} [CommRing S] (M N : Type*) [AddCommGroup M] [Module S M] [AddCommGroup N]
    [Module S N] [Module.Flat S M] [Module.Flat S N] : Module.Flat S (M × N) := by
  rw [Module.Flat.iff_lTensor_injective']
  intro I
  have hM := (Module.Flat.iff_lTensor_injective'.mp (inferInstance : Module.Flat S M)) I
  have hN := (Module.Flat.iff_lTensor_injective'.mp (inferInstance : Module.Flat S N)) I
  have key' : ∀ (p : M × N) (i : I), TensorProduct.prodLeft S S M N S (LinearMap.lTensor (M × N) I.subtype (p ⊗ₜ i)) =
      ((LinearMap.lTensor M I.subtype).prodMap (LinearMap.lTensor N I.subtype)) (TensorProduct.prodLeft S S M N I (p ⊗ₜ i)) := by
    intro p i
    obtain ⟨m, n⟩ := p
    simp [TensorProduct.prodLeft_tmul, LinearMap.lTensor_tmul]
  have key : ∀ x, TensorProduct.prodLeft S S M N S (LinearMap.lTensor (M × N) I.subtype x) =
      ((LinearMap.lTensor M I.subtype).prodMap (LinearMap.lTensor N I.subtype)) (TensorProduct.prodLeft S S M N I x) := by
    intro x
    induction x using TensorProduct.induction_on with
    | zero => simp only [map_zero]
    | add x y hx hy => simp only [map_add, hx, hy]
    | tmul p i => exact key' p i
  intro x y hxy
  apply (TensorProduct.prodLeft S S M N I).injective
  have hxy' := congrArg (TensorProduct.prodLeft S S M N S) hxy
  rw [key, key] at hxy'
  have h1 := congrArg Prod.fst hxy'
  have h2 := congrArg Prod.snd hxy'
  simp only [LinearMap.prodMap_apply] at h1 h2
  exact Prod.ext (hM h1) (hN h2)

theorem isClosed_setOf_le_finrank_ker_cechDiff_baseChange
    {A : Type u} [CommRing A] [IsNoetherianRing A] {X : Scheme.{u}} (π : X ⟶ Spec (CommRingCat.of A))
    [IsProper π] [Flat π] (𝒱 : X.TwoAffineOpenCover) (M : X.Modules) (hM : Scheme.Modules.IsInvertible M) (n : ℕ) :
    IsClosed {𝔭 : PrimeSpectrum A | n ≤ Module.finrank 𝔭.asIdeal.ResidueField
      (LinearMap.ker ((𝒱.sectionsOf π M).cechDiff.baseChange 𝔭.asIdeal.ResidueField))} := by

  have flatOf : ∀ (U : X.Opens) (hU : IsAffineOpen U),
      letI := Scheme.TwoAffineOpenCover.moduleSectionsOfHom π M U
      Module.Flat A Γ(M, U) := by
    intro U hU
    letI := Scheme.TwoAffineOpenCover.algebraOfHom π U
    letI := Scheme.TwoAffineOpenCover.moduleSectionsOfHom π M U
    haveI := Scheme.TwoAffineOpenCover.isScalarTower_sections π M U
    haveI : Module.Flat A Γ(X, U) := Scheme.TwoAffineOpenCover.flat_sections_of_flat π U hU
    haveI : Module.Projective Γ(X, U) Γ(M, U) :=
      Scheme.Modules.projective_sections_of_locallyTrivial _ hM.1 ⟨U, hU⟩
    exact Module.Flat.trans A Γ(X, U) Γ(M, U)
  haveI : Module.Flat A (𝒱.sectionsOf π M).M0 := flatOf _ 𝒱.isAffineOpen_U0
  haveI : Module.Flat A (𝒱.sectionsOf π M).M1 := flatOf _ 𝒱.isAffineOpen_U1
  haveI : Module.Flat A (𝒱.sectionsOf π M).M01 := flatOf _ 𝒱.isAffineOpen_inf
  haveI : Module.Flat A ((𝒱.sectionsOf π M).M0 × (𝒱.sectionsOf π M).M1) := flat_prod _ _

  have hcf := OModulePresheaf.cechFinite_ofModules_of_locallyTrivial π M hM.1 𝒱.toOrderedAffineCover
  obtain ⟨hfin0, hfin1⟩ := (OModulePresheaf.cechFinite_toOrderedAffineCover_iff _ _).mp hcf
  haveI : Module.Finite A (LinearMap.ker (𝒱.sectionsOf π M).cechDiff) := hfin0
  haveI : Module.Finite A ((𝒱.sectionsOf π M).M01 ⧸ LinearMap.range (𝒱.sectionsOf π M).cechDiff) := hfin1
  have h := TwoChartCech.isClosed_setOf_le_finrank_ker_baseChange (𝒱.sectionsOf π M).cechDiff
    (𝟙 (Spec (CommRingCat.of A))) n
  simp at h
  exact h

theorem finrank_H0_fibreModule_unit_eq_one
    {R : Type u} [CommRing R] {C : Scheme.{u}} (c : C ⟶ Spec (CommRingCat.of R))
    [IsProper c] [SmoothOfRelativeDimension 1 c] [GeometricallyIntegral c]
    {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R))
    (k : Type u) [Field k] [IsAlgClosed k] (s : Spec (CommRingCat.of k) ⟶ T)
    (𝒲 : (pullback (pullback.snd c t) s).TwoAffineOpenCover) :
    Module.finrank k (𝒲.sectionsOf (fibreAt c t s) (fibreModule c t s (𝟙_ (pullback c t).Modules))).H0 = 1 := by

  let φ : pullback (pullback.snd c t) s ≅ pullback c (s ≫ t) := pullbackLeftPullbackSndIso c t s
  have hφ : φ.symm.hom ≫ fibreAt c t s = pullback.snd c (s ≫ t) := by
    rw [Iso.symm_hom, Iso.inv_comp_eq]
    exact (pullbackLeftPullbackSndIso_hom_snd c t s).symm

  have e : (𝟙_ (pullback c (s ≫ t)).Modules) ≅ (Scheme.Modules.pullback φ.symm.hom).obj
      (fibreModule c t s (𝟙_ (pullback c t).Modules)) :=
    (Scheme.Modules.pullbackTensorUnitObjIso φ.symm.hom).symm ≪≫
      (Scheme.Modules.pullback φ.symm.hom).mapIso
        (Scheme.Modules.pullbackTensorUnitObjIso (pullback.fst (pullback.snd c t) s)).symm
  obtain ⟨𝒱, -, -, ⟨e0⟩, -⟩ := Scheme.TwoAffineOpenCover.exists_linearEquiv_sectionsOf_of_iso
    (pullback.snd c (s ≫ t)) (fibreAt c t s) φ.symm hφ 𝒲 _ _ e
  rw [← e0.finrank_eq]
  exact finrank_H0_unit_fibre_eq_one c k (s ≫ t) 𝒱

end AlgebraicGeometry.RelPicard.UnitClosed

open AlgebraicGeometry.RelPicard.UnitClosed TensorProduct in

theorem solution
    (R : Type u) [CommRing R] [IsNoetherianRing R] {C : Scheme.{u}} (c : C ⟶ Spec (CommRingCat.of R))
    [IsProper c] [SmoothOfRelativeDimension 1 c] [GeometricallyIntegral c]
    (ε : SchemeHomOver (𝟙 (Spec (CommRingCat.of R))) c)
    (h𝔉 : ∀ m₀ : ℕ, ∃ 𝔉 : SmoothProperCurve.FiniteMapData c ε, m₀ ≤ 𝔉.m)
    {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) [LocallyOfFiniteType t]
    (L : RigidifiedLineBundle c ε t) (hL : FibrewiseAlgEquivZero L) :
    IsClosed {x : T | ∃ (k : Type u) (_ : Field k) (s : Spec (CommRingCat.of k) ⟶ T),
      s.base (IsLocalRing.closedPoint k) = x ∧
        Nonempty (fibreModule c t s L.L ≅ 𝟙_ (pullback (pullback.snd c t) s).Modules)} := by
  classical
  obtain ⟨𝔉, -⟩ := h𝔉 0
  haveI : Smooth c := SmoothOfRelativeDimension.smooth (n := 1) (f := c)
  haveI := smoothOfRelativeDimension_isStableUnderBaseChange (n := 1)
  haveI : IsLocallyNoetherian T := LocallyOfFiniteType.isLocallyNoetherian t

  have fibre_inst : ∀ {k : Type u} [Field k] [IsAlgClosed k] (s : Spec (CommRingCat.of k) ⟶ T),
      IsIntegral (pullback (pullback.snd c t) s) ∧ IsProper (fibreAt c t s) ∧
        SmoothOfRelativeDimension 1 (fibreAt c t s) := by
    intro k _ _ s
    haveI : SmoothOfRelativeDimension 1 (pullback.snd c t) :=
      MorphismProperty.pullback_snd (P := @SmoothOfRelativeDimension 1) _ _ inferInstance
    haveI : IsProper (pullback.snd c t) := MorphismProperty.pullback_snd (P := @IsProper) _ _ inferInstance
    refine ⟨?_, ?_, ?_⟩
    · exact GeometricallyIntegral.geometrically_isIntegral (f := pullback.snd c t) s
        (pullback.fst (pullback.snd c t) s) (pullback.snd (pullback.snd c t) s) (IsPullback.of_hasPullback _ _)
    · exact MorphismProperty.pullback_snd (P := @IsProper) _ _ inferInstance
    · exact MorphismProperty.pullback_snd (P := @SmoothOfRelativeDimension 1) _ _ inferInstance

  have pointwise : ∀ {k : Type u} [Field k] [IsAlgClosed k] (s : Spec (CommRingCat.of k) ⟶ T)
      (𝒲 : (pullback (pullback.snd c t) s).TwoAffineOpenCover),
      1 ≤ Module.finrank k (𝒲.sectionsOf (fibreAt c t s) (fibreModule c t s L.L)).H0 →
        Nonempty (fibreModule c t s L.L ≅ 𝟙_ (pullback (pullback.snd c t) s).Modules) := by
    intro k _ _ s 𝒲 h1
    obtain ⟨hint, hprop, hsm⟩ := fibre_inst s
    haveI := hint; haveI := hprop; haveI := hsm

    haveI : Nontrivial (𝒲.sectionsOf (fibreAt c t s) (fibreModule c t s L.L)).H0 :=
      Module.nontrivial_of_finrank_pos (R := k) h1
    obtain ⟨y, hy⟩ := exists_ne (0 : (𝒲.sectionsOf (fibreAt c t s) (fibreModule c t s L.L)).H0)
    obtain ⟨eΓ, -⟩ := Scheme.TwoAffineOpenCover.exists_linearEquiv_sectionsOf_H0 𝒲 (fibreAt c t s)
      (fibreModule c t s L.L)
    have hσ : eΓ.symm y ≠ 0 := fun h => hy (by rw [← eΓ.apply_symm_apply y, h, map_zero])
    obtain ⟨σ, hσ0⟩ := exists_hom_ne_zero (fibreModule c t s L.L) (eΓ.symm y) hσ

    haveI : GeometricallyIntegral (fibreAt c t s) := geometricallyIntegral_of_isAlgClosed (fibreAt c t s)
    exact IsAlgEquivZero.nonempty_iso_tensorUnit_of_ne_zero (fibreAt c t s) 𝒲 (L.isInvertible.pullback _)
      (hL k s) σ hσ0

  rw [← isOpen_compl_iff, isOpen_iff_forall_mem_open]
  intro x hx
  rw [Set.mem_compl_iff, Set.mem_setOf_eq] at hx

  obtain ⟨W, hW, hxW, -⟩ := exists_isAffineOpen_mem_and_subset (x := x) (U := (⊤ : T.Opens)) trivial
  haveI : IsNoetherianRing Γ(T, W) := IsLocallyNoetherian.component_noetherian ⟨W, hW⟩
  letI : Algebra R Γ(T, W) := Scheme.TwoAffineOpenCover.algebraOfHom t W
  set A : Type u := Γ(T, W) with hA
  set j : Spec (CommRingCat.of A) ⟶ T := hW.fromSpec with hjdef
  have hj : j ≫ t = Scheme.TwoAffineOpenCover.specMap R A := by
    have e1 : CommRingCat.ofHom (algebraMap R A) = (Scheme.ΓSpecIso (.of R)).inv ≫ t.appLE ⊤ W le_top := rfl
    rw [hjdef, Scheme.TwoAffineOpenCover.specMap, e1, Spec.map_comp, ← Scheme.isoSpec_Spec_inv,
      ← IsAffineOpen.fromSpec_top, IsAffineOpen.SpecMap_appLE_fromSpec t (isAffineOpen_top _) hW]

  set CA := pullback c (Scheme.TwoAffineOpenCover.specMap R A) with hCA
  set πA : CA ⟶ Spec (CommRingCat.of A) := pullback.snd c (Scheme.TwoAffineOpenCover.specMap R A) with hπA
  set g' : CA ⟶ pullback c t := pullback.map c (Scheme.TwoAffineOpenCover.specMap R A) c t (𝟙 C) j (𝟙 _)
    (by simp) (by rw [Category.comp_id, hj]) with hg'
  have hg'fst : g' ≫ pullback.fst c t = pullback.fst c (Scheme.TwoAffineOpenCover.specMap R A) := by
    rw [hg', pullback.lift_fst, Category.comp_id]
  have hg'snd : g' ≫ pullback.snd c t = πA ≫ j := by
    rw [hg', pullback.lift_snd]
  have hcart : IsPullback g' πA (pullback.snd c t) j := by
    refine IsPullback.of_right ?_ hg'snd (IsPullback.of_hasPullback c t)
    rw [hg'fst, hj]
    exact IsPullback.of_hasPullback c (Scheme.TwoAffineOpenCover.specMap R A)
  haveI : IsProper πA := MorphismProperty.pullback_snd (P := @IsProper) _ _ inferInstance
  haveI : Flat πA := MorphismProperty.pullback_snd (P := @Flat) _ _ inferInstance
  let 𝒱 : CA.TwoAffineOpenCover := 𝔉.twoAffineOpenCover.pullback c A

  let h0 : (pullback c t).Modules → PrimeSpectrum A → ℕ := fun M 𝔭 =>
    Module.finrank 𝔭.asIdeal.ResidueField
      (LinearMap.ker ((𝒱.sectionsOf πA ((Scheme.Modules.pullback g').obj M)).cechDiff.baseChange
        𝔭.asIdeal.ResidueField))
  have hVclosed : IsClosed {𝔭 : PrimeSpectrum A | 1 ≤ h0 L.L 𝔭} :=
    isClosed_setOf_le_finrank_ker_cechDiff_baseChange πA 𝒱 _ (L.isInvertible.pullback g') 1

  have geom : ∀ 𝔭 : PrimeSpectrum A, ∃ (K : Type u) (_ : Field K) (_ : IsAlgClosed K) (sb : Spec (CommRingCat.of K) ⟶ T),
      sb.base (IsLocalRing.closedPoint K) = j.base 𝔭 := by
    intro 𝔭
    refine ⟨AlgebraicClosure 𝔭.asIdeal.ResidueField, inferInstance, inferInstance,
      Scheme.TwoAffineOpenCover.specMap 𝔭.asIdeal.ResidueField (AlgebraicClosure 𝔭.asIdeal.ResidueField) ≫
        Scheme.TwoAffineOpenCover.specMap A 𝔭.asIdeal.ResidueField ≫ j, ?_⟩
    change j.base ((Scheme.TwoAffineOpenCover.specMap A 𝔭.asIdeal.ResidueField).base
      ((Scheme.TwoAffineOpenCover.specMap 𝔭.asIdeal.ResidueField (AlgebraicClosure 𝔭.asIdeal.ResidueField)).base
        (IsLocalRing.closedPoint _))) = j.base 𝔭
    rw [specMap_residueField_base]

  have hO1 : ∀ 𝔭 : PrimeSpectrum A, h0 (𝟙_ (pullback c t).Modules) 𝔭 = 1 := by
    intro 𝔭
    obtain ⟨K, _, _, sb, hsb⟩ := geom 𝔭
    obtain ⟨𝒲, h𝒲⟩ :=
      exists_twoAffineOpenCover_fibre_finrank_eq_finrank_cechDiff_baseChange_residueField c t j πA g' hcart 𝒱 𝔭 sb hsb
    obtain ⟨hO0, -⟩ := h𝒲 (𝟙_ (pullback c t).Modules) (Scheme.Modules.isInvertible_unit _)
    change Module.finrank _ _ = 1
    rw [← hO0]
    exact finrank_H0_fibreModule_unit_eq_one c t K sb 𝒲

  have key : ∀ 𝔭 : PrimeSpectrum A,
      (∃ (k : Type u) (_ : Field k) (s : Spec (CommRingCat.of k) ⟶ T),
        s.base (IsLocalRing.closedPoint k) = j.base 𝔭 ∧
          Nonempty (fibreModule c t s L.L ≅ 𝟙_ (pullback (pullback.snd c t) s).Modules)) ↔ 1 ≤ h0 L.L 𝔭 := by
    intro 𝔭
    constructor
    · rintro ⟨k, _, s, hs, ⟨e⟩⟩
      obtain ⟨𝒲, h𝒲⟩ :=
        exists_twoAffineOpenCover_fibre_finrank_eq_finrank_cechDiff_baseChange_residueField c t j πA g' hcart 𝒱 𝔭 s hs
      obtain ⟨hL0, -⟩ := h𝒲 L.L L.isInvertible
      obtain ⟨hO0, -⟩ := h𝒲 (𝟙_ (pullback c t).Modules) (Scheme.Modules.isInvertible_unit _)
      have hcongr := finrank_H0_congr (fibreAt c t s) 𝒲
        (e ≪≫ (Scheme.Modules.pullbackTensorUnitObjIso (pullback.fst (pullback.snd c t) s)).symm)
      rw [← hO1 𝔭]
      change Module.finrank _ _ ≤ Module.finrank _ _
      rw [← hL0, ← hO0, hcongr]
    · intro h
      obtain ⟨K, _, _, sb, hsb⟩ := geom 𝔭
      obtain ⟨𝒲, h𝒲⟩ :=
        exists_twoAffineOpenCover_fibre_finrank_eq_finrank_cechDiff_baseChange_residueField c t j πA g' hcart 𝒱 𝔭 sb hsb
      obtain ⟨hL0, -⟩ := h𝒲 L.L L.isInvertible
      refine ⟨K, inferInstance, sb, hsb, pointwise sb 𝒲 ?_⟩
      rw [hL0]
      exact h
  refine ⟨j.base '' {𝔭 : PrimeSpectrum A | 1 ≤ h0 L.L 𝔭}ᶜ, ?_, j.isOpenEmbedding.isOpenMap _ hVclosed.isOpen_compl, ?_⟩
  ·
    rintro _ ⟨𝔭, h𝔭, rfl⟩ hmem
    exact h𝔭 ((key 𝔭).mp hmem)
  ·
    have hxr : x ∈ Set.range ⇑j.base := by
      rw [hjdef]
      change x ∈ Set.range hW.fromSpec
      rw [hW.range_fromSpec]; exact hxW
    obtain ⟨𝔭, rfl⟩ := hxr
    exact ⟨𝔭, fun h𝔭 => hx ((key 𝔭).mpr h𝔭), rfl⟩

end
end S_AlgebraicGeometry_RelPicard_isClosed_setOf_exists_fibreModule_iso_unit
end P2MW
export P2MW.S_AlgebraicGeometry_RelPicard_isClosed_setOf_exists_fibreModule_iso_unit (solution)
