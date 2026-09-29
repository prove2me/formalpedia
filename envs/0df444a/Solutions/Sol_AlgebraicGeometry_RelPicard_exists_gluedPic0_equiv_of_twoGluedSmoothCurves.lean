-- Prove2me | solution 1 for AlgebraicGeometry.RelPicard.exists_gluedPic0_equiv_of_twoGluedSmoothCurves
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:03.589526+00:00
-- url     : https://prove2.me/submissions/7649e68c-b29f-5b16-b7d7-ba99cec896a6

import Mathlib
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import Definitions.Def_AlgebraicGeometry_RepresentsRelSubPic
import Definitions.Def_AlgebraicGeometry_RelPicardAlgEquivZeroCut
import Definitions.Def_AlgebraicGeometry_RelPicardAlgEquivZeroGroupCut
import Definitions.Def_AlgebraicGeometry_RelPicardPullback
import Definitions.Def_AlgebraicGeometry_ModulesRigidify
import Definitions.Def_AlgebraicGeometry_NeronModelEndomorphismExtension
import Definitions.Def_AlgebraicGeometry_TwoGluedCurvesNodeUnitModule
import Definitions.Def_AlgebraicGeometry_IdealSheafModule
import Definitions.Def_AlgebraicGeometry_RelEffCartierDiv
import Definitions.Def_AlgebraicGeometry_RelEffCartierDivOfPoint
import Definitions.Def_SheafOfModules_Monoidal
import Definitions.Def_AlgebraicCurve_CurveModel
import Definitions.Def_AlgebraicCurve_GluedPic0
import Definitions.Def_AlgebraicCurve_DivisorClassGroup
import Definitions.Def_AlgebraicCurve_AdelicIndex
import Theorems.Thm_AlgebraicGeometry_RelPicard_exists_hom_admissible_of_twoGluedSmoothCurves
import Theorems.Thm_AlgebraicGeometry_RelPicard_gluedPic0_mk_eq_zero_of_hom_admissible_eq_one_of_twoGluedSmoothCurves
import Theorems.Thm_AlgebraicGeometry_RelPicard_exists_hom_admissible_eq_of_twoGluedSmoothCurves
import Theorems.Thm_AlgebraicGeometry_RelPicard_exists_restrictHom_pair_of_twoGluedSmoothCurves
import Theorems.Thm_AlgebraicGeometry_exists_rationalPoint_enumeration_of_natCard_pullback_eq
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_RelPicard_exists_gluedPic0_equiv_of_twoGluedSmoothCurves
p2m_attr_erase "instance" "AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instNeg AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instSMulInt AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instAddCommGroup AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instAdd AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instSub AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instModuleCarrierObjOppositeOpensCarrierCarrierCommRingCatPresheafOpOpensTop AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instSMulCarrierObjOppositeOpensCarrierCarrierCommRingCatPresheafOpOpensTop AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instSMulNat AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instZero AlgebraicGeometry.RelEffCartierDiv.isClosedImmersion_subschemeι_resProdMap AlgebraicGeometry.RelEffCartierDiv.isOpenImmersion_resProdMap SheafOfModules.isIso_ihomModelToIhom AlgebraicGeometry.ChowDatum.hι_closed AlgebraicGeometry.ChowDatumProj.hιN_closed AlgebraicGeometry.ChowDatumProj.hp_proper AlgebraicGeometry.ChowDatum.hp_isoU AlgebraicGeometry.ChowDatum.hp_proper AlgebraicGeometry.ProjSpace.algebraAway AlgebraicGeometry.ProjSpace.instIsProperProdOverπ AlgebraicGeometry.ChowDatumProj.hp_isoU AlgebraicGeometry.ProjSpace.isProper_π AlgebraicGeometry.ProjSpace.finiteType_mvPolynomial AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation TwoChartCech.Sections.M0_moduleA TwoChartCech.Sections.M1_module TwoChartCech.Cover.A01_algebra TwoChartCech.Cover.A0_algebra TwoChartCech.Cover.A1_commRing TwoChartCech.Cover.A1_algebra TwoChartCech.Sections.M01_module TwoChartCech.Sections.M0_addCommGroup TwoChartCech.Sections.M0_tower TwoChartCech.Sections.M01_addCommGroup TwoChartCech.Cover.A0_commRing TwoChartCech.Sections.M1_tower TwoChartCech.Sections.M01_moduleA TwoChartCech.Sections.M0_module TwoChartCech.Sections.M1_moduleA TwoChartCech.Sections.M1_addCommGroup"
p2m_attr_erase "instance" "TwoChartCech.Cover.A01_commRing TwoChartCech.Sections.M01_tower CoherentBaseChange.TwoTermComplex.C0_module CoherentBaseChange.TwoTermComplex.C0_addCommGroup CoherentBaseChange.TwoTermComplex.C1_module CoherentBaseChange.TwoTermComplex.C1_addCommGroup CoherentBaseChange.TwoTermComplex.C0_free CoherentBaseChange.TwoTermComplex.C1_finite CoherentBaseChange.TwoTermComplex.C0_finite CoherentBaseChange.TwoTermComplex.C1_free AlgebraicCurve.IsCurveOver.instNontrivialKaehler AlgebraicCurve.IsCurveOver.instFreeKaehler AlgebraicCurve.IsCurveOver.toHasPrincipalDivisors AlgebraicCurve.IsCurveOver.instFiniteResidue AlgebraicCurve.instFundamentalIdentityOfSumRamificationInertia AlgebraicCurve.Place.instIsScalarTowerResidueFieldRestrictPushforward AlgebraicCurve.Place.instAlgebraResidueFieldRestrictPushforward AlgebraicCurve.Place.instIsLocalHomRestrictInclusion AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.SemilinearAut.instDistribMulActionSubtypeProdRingAutMemSubgroupPic0 AlgebraicCurve.SemilinearAut.instDistribMulActionSubtypeProdRingAutMemSubgroupDivisor AlgebraicCurve.Pic0.instModuleZModTorsion AlgebraicCurve.SemilinearAut.instSMulSubtypeProdRingAutMemSubgroupPlace AlgebraicCurve.SemilinearAut.instDistribMulActionTorsion AlgebraicCurve.SemilinearAut.instSMulSubtypeProdRingAutMemSubgroupPic0 AlgebraicCurve.SemilinearAut.instSMulTorsion AlgebraicCurve.SemilinearAut.instMulActionSubtypeProdRingAutMemSubgroupPlace AlgebraicCurve.SemilinearAut.instSMulCommClassZModTorsion AlgebraicCurve.SemilinearAut.instMulSemiringActionSubtypeProdRingAutMemSubgroup instDecEqAlgebraicClosureRat WeierstrassCurve.Affine.Point.instDistribMulActionAlgEquiv WeierstrassCurve.Affine.Point.instModuleZModTorsionBy WeierstrassCurve.Affine.Point.instSMulTorsionBy WeierstrassCurve.Affine.Point.instDistribMulActionTorsionBy WeierstrassCurve.Affine.Point.instSMulAlgEquiv WeierstrassCurve.Affine.Point.instSMulCommClassAlgEquivZModTorsionBy"
p2m_attr_erase "instance" "AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions AlgebraicGeometry.SmoothOfRelativeDimension.fiberToSpecResidueField AlgebraicGeometry.SmoothOfRelativeDimension.pullback_snd AlgebraicGeometry.SmoothOfRelativeDimension.pullback_fst AlgebraicGeometry.SmoothOfRelativeDimension.smooth_one AlgebraicGeometry.SmoothProperCurve.isIntegral_pullback_Spec_field AlgebraicGeometry.IsProper.fiberToSpecResidueField AlgebraicGeometry.RelEffCartierDiv.subsingleton_of_degree_zero AlgebraicCurve.instHasLocalResidue_of_hasCanonicalLocalResidueK AlgebraicCurve.instHasCanonicalLocalResidueK_of_hasCanonicalLocalResidueKStar AlgebraicCurve.Place.kw_ffgc_finiteDimensional_adicCompletion instAlgebraSubtypeMemValuationSubring_definitions AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersIntegersCompletion ModularCurve.KwF4gRRTate.instAlgebraKAdicCompletionIntegers AlgebraicCurve.Place.kw_ffgc_continuousSMul_adicCompletionComap AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersCompletionCompletion IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions AlgebraicCurve.instHasCanonicalLocalResidueK AlgebraicCurve.Place.instAlgebra_restrictResidueField AlgebraicCurve.Place.instIsScalarTower_restrictResidueField AlgebraicCurve.instHasLocalResidue AlgebraicCurve.HasSeparableResidue.of_perfectField_of_isCurveOver AlgebraicCurve.HasSeparableResidue.of_perfectField AlgebraicCurve.Place.instIsLocalHom_restrictSubringHom AlgebraicCurve.instHasCanonicalLocalResidueKStar ModularCurve.KwNo6Pin.isLocalRing_completion AlgebraicGeometry.OModulePresheaf.isScalarTower AlgebraicGeometry.Scheme.OrderedAffineCover.instLinearOrder AlgebraicGeometry.OModulePresheaf.module AlgebraicGeometry.Scheme.OrderedAffineCover.instFintype AlgebraicGeometry.Scheme.OrderedAffineCover.instFintypeIdx AlgebraicGeometry.OModulePresheaf.addCommGroup AlgebraicGeometry.Scheme.OrderedAffineCover.instDecidableEqIdx AlgebraicGeometry.OModulePresheaf.moduleSections AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instDecidableEqIdx"
p2m_attr_erase "instance" "AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instFintype AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instLinearOrder AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instFintypeIdx AlgebraicGeometry.OModulePresheaf.instSubsingletonObjZero AlgebraicGeometry.OModulePresheaf.Leray.relAltC_scalarTower AlgebraicGeometry.OModulePresheaf.Leray.ker_relAltd_modΓ AlgebraicGeometry.OModulePresheaf.Leray.relAltC_modΓ AlgebraicGeometry.OModulePresheaf.Leray.biC_abGrp AlgebraicGeometry.OModulePresheaf.Leray.relAltH_modΓ AlgebraicGeometry.OModulePresheaf.Leray.ker_relAltd_smul AlgebraicGeometry.OModulePresheaf.Leray.relAltH_scalarTower AlgebraicGeometry.OModulePresheaf.Leray.relAltH_smul AlgebraicGeometry.OModulePresheaf.Leray.biC_module DoubleComplex.instModuleE₂I DoubleComplex.Bounded.modR DoubleComplex.instModuleE₂II DoubleComplex.instAddCommGroupE₂II DoubleComplex.Bounded.abGrp DoubleComplex.instAddCommGroupE₂I ProjSpaceCech.GradedModule.H.module ProjSpaceCech.GradedModule.H.addCommGroup ProjSpaceCech.GradedModule.sec.instAdd ProjSpaceCech.GradedModule.sec.instNeg ProjSpaceCech.GradedModule.acg ProjSpaceCech.GradedModule.Frac.setoid ProjSpaceCech.GradedModule.modR ProjSpaceCech.GradedModule.sec.instModule ProjSpaceCech.GradedModule.sec.instAddCommGroup ProjSpaceCech.GradedModule.sec.instZero ProjSpaceCech.GradedModule.Presentation.fJ ProjSpaceCech.GradedModule.sec.instSMul ProjSpaceCech.Twist.H.module ProjSpaceCech.Idx.instFintype ProjSpaceCech.Twist.H.addCommGroup ProjSpaceCech.Idx.instDecidableEq ProjSpaceCech.Twist.Mon.instDecidableEq ProjSpaceCech.Twist.cochain.instAddCommGroup ProjSpaceCech.Twist.cochain.instModule"
p2m_attr_erase "simp" "AlgebraicGeometry.RelPicard.rigSection_snd AlgebraicGeometry.RelPicard.RigidifiedLineBundle.ofInvertible_L AlgebraicGeometry.RelPicard.rigSection_snd_assoc AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.sub_app AlgebraicGeometry.Scheme.IdealSheafData.sres_sresTop AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.add_app AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.mk.sizeOf_spec AlgebraicGeometry.Scheme.IdealSheafData.coe_resLE AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.smul_app AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.coe_ofLE_app AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.ideal_range AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.zero_app AlgebraicGeometry.Scheme.IdealSheafData.sres_sres AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.comp_app AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.neg_app AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.id_app AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.coe_mulRight_app AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.nsmul_app AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.mk.injEq AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.zsmul_app AlgebraicGeometry.Scheme.Modules.toUnitSection_ofUnitSection AlgebraicGeometry.Scheme.Modules.pullbackSection_def AlgebraicGeometry.Scheme.Modules.ofUnitSection_toUnitSection AlgebraicGeometry.RelEffCartierDiv.supportedIn_top AlgebraicGeometry.RelEffCartierDiv.mem_supportedIn_iff AlgebraicGeometry.RelEffCartierDiv.supportedIn_top_eq AlgebraicGeometry.RelEffCartierDiv.IsUniversal.lift_comp AlgebraicGeometry.RelEffCartierDiv.functor_map_fst AlgebraicGeometry.RelEffCartierDiv.IsUniversal.homEquiv_apply AlgebraicGeometry.RelEffCartierDiv.IsUniversal.lift_pullbackAlong AlgebraicGeometry.RelEffCartierDiv.IsUniversal.homEquiv_symm_apply AlgebraicGeometry.RelEffCartierDiv.IsUniversal.lift_comp_assoc AlgebraicGeometry.RelEffCartierDiv.restrictAlong_extendAlong AlgebraicGeometry.RelEffCartierDiv.extendAlong_I AlgebraicGeometry.RelEffCartierDiv.resProdMap_snd AlgebraicGeometry.RelEffCartierDiv.restrictAlong_I AlgebraicGeometry.RelEffCartierDiv.extendAlong_restrictAlong AlgebraicGeometry.RelEffCartierDiv.resProdMap_fst_assoc AlgebraicGeometry.RelEffCartierDiv.resProdMap_snd_assoc AlgebraicGeometry.RelEffCartierDiv.resProdMap_fst"
p2m_attr_erase "simp" "AlgebraicGeometry.Scheme.Modules.tensorSections_zero_right AlgebraicGeometry.Scheme.Modules.map_unitSection AlgebraicGeometry.Scheme.Modules.tensorSectionsBilin_apply AlgebraicGeometry.Scheme.Modules.tensorPowSection_zero AlgebraicGeometry.Scheme.Modules.tensorSections_zero_left AlgebraicGeometry.Scheme.Modules.tensorPow_zero AlgebraicGeometry.Scheme.Modules.tensorPow_succ AlgebraicGeometry.Scheme.Modules.pullbackLocalSection_neg AlgebraicGeometry.Scheme.Modules.pullbackLocalSection_zero AlgebraicGeometry.Scheme.Modules.pullbackLocalSection_sub AlgebraicGeometry.Scheme.Modules.pullbackLocalSection_add PresheafOfModules.InternalHom.IsSheafAux.appAt_toPresheafHom SheafOfModules.ihomSectionsEquivFamily_unit AlgebraicGeometry.Scheme.Modules.restrictHomEquivFamily_apply SheafOfModules.ihomEval_unit_app AlgebraicGeometry.Scheme.Modules.ihomEval_zero_right AlgebraicGeometry.Scheme.Modules.ihomEval_zero_left AlgebraicGeometry.Scheme.Modules.homOfFamily_app_apply SheafOfModules.unit_ihomSectionsEquivFamily AlgebraicGeometry.Scheme.Modules.familyOfHom_app AlgebraicGeometry.Scheme.Modules.restrictUnitIso_hom_app_apply AlgebraicGeometry.Scheme.Modules.restrictUnitIso_inv_app_apply AlgebraicGeometry.Scheme.Modules.restrictHomOfFamily_app_apply AlgebraicGeometry.Scheme.Modules.restrictHomEquivFamily_symm_apply AlgebraicGeometry.Scheme.Modules.ProjPresentation.mk.injEq AlgebraicGeometry.Scheme.Modules.ProjPresentation.mk.sizeOf_spec AlgebraicGeometry.ChowDatumProj.mk.sizeOf_spec AlgebraicGeometry.ChowDatum.mk.sizeOf_spec AlgebraicGeometry.ChowDatumProj.mk.injEq AlgebraicGeometry.ChowDatum.mk.injEq AlgebraicCurve.Place.congrEquiv_symm_apply AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply AlgebraicCurve.RationalFunctionField.deg_placeOfPoint AlgebraicCurve.coe_cechH0Equiv_apply AlgebraicCurve.cechH1ToH1_mk AlgebraicCurve.lSpaceOn_univ AlgebraicCurve.lSpaceOn_empty"
p2m_attr_erase "simp" "TwoChartCech.Sections.mk.injEq TwoChartCech.Cover.mk.injEq TwoChartCech.GrothendieckComplex.mk.injEq TwoChartCech.Sections.mk.sizeOf_spec TwoChartCech.Cover.mk.sizeOf_spec TwoChartCech.Cover.lineBundle_r0_apply TwoChartCech.GrothendieckComplex.mk.sizeOf_spec TwoChartCech.Cover.lineBundle_r1_apply CoherentBaseChange.TwoTermComplex.mk.sizeOf_spec CoherentBaseChange.TwoTermComplex.mk.injEq AlgebraicCurve.Divisor.mapRestrict_single AlgebraicCurve.Divisor.pushforward_single AlgebraicCurve.Place.coe_restrictInclusion AlgebraicCurve.Place.mem_fiber AlgebraicCurve.Place.restrict_toValuationSubring AlgebraicCurve.Divisor.degree_pushforward AlgebraicCurve.Place.restrictResidueMap_residue AlgebraicCurve.Pic0.coe_pushforwardDegZeroHom AlgebraicCurve.Pic0.coe_pullbackDegZeroHom AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal AlgebraicCurve.IsFrobeniusEndo.frobNormRingHom_apply ModularCurve.frobeniusPushforwardGeomLevelPic0_mk ModularCurve.coe_frobeniusGeomLevelEquiv_apply ModularCurve.coe_frobeniusPushforwardGeomLevelDegZero ModularCurve.heckeFibreGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusGeomLevel_apply_coe ModularCurve.frobeniusPullbackGeomLevelPic0OfIsCurveOver_mk ModularCurve.coe_heckeFibreGeomLevelDegZero ModularCurve.coe_frobeniusPullbackGeomLevelDegZero ModularCurve.frobeniusPullbackGeomLevelPic0_mk ModularCurve.frobeniusPullbackGeomLevel_single ModularCurve.heckeFibreGeomLevelPic0_mk ModularCurve.frobeniusPushforwardGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusPushforwardGeomLevel_single ModularCurve.qExpandAlgC_apply AlgebraicCurve.Divisor.degree_pushforwardAlong"
p2m_attr_erase "simp" "AlgebraicCurve.Pic0.coe_degZeroCorrespondence AlgebraicCurve.Place.mem_fiberAlong AlgebraicCurve.SemilinearAut.toRingAut_inv AlgebraicCurve.SemilinearAut.smul_def AlgebraicCurve.SemilinearAut.smul_single AlgebraicCurve.SemilinearAut.smul_toValuationSubring AlgebraicCurve.SemilinearAut.baseAut_inv AlgebraicCurve.SemilinearAut.baseAut_ofAlgAut AlgebraicCurve.SemilinearAut.toRingAut_ofAlgAut AlgebraicCurve.SemilinearAut.torsionRep_apply AlgebraicCurve.SemilinearAut.toRingAut_one AlgebraicCurve.SemilinearAut.deg_smul AlgebraicCurve.SemilinearAut.degree_smul AlgebraicCurve.SemilinearAut.coe_degZeroSMulHom AlgebraicCurve.SemilinearAut.baseAut_mul AlgebraicCurve.SemilinearAut.coe_smulValuationSubringEquiv_apply AlgebraicCurve.SemilinearAut.baseAut_one AlgebraicCurve.SemilinearAut.ofAlgAut_smul AlgebraicCurve.SemilinearAut.coe_torsion_smul AlgebraicCurve.SemilinearAut.toRingAut_mul AlgebraicCurve.coe_frobeniusPushforwardDegZero AlgebraicCurve.IsFrobeniusEndo.coe_frobeniusPullbackDegZero ModularCurve.jqNModC_one ModularCurve.qExpand_coeff_mul ModularCurve.qExpandₐ_apply ModularCurve.jqN_one ModularCurve.qExpand_single ModularCurve.dedekindPsi_one ModularCurve.ModularPolynomialData.mk.sizeOf_spec ModularCurve.evalAtJ_X ModularCurve.ModularPolynomialData.mk.injEq ModularCurve.constantCoeff_jNum ModularCurve.constantCoeff_eisenstein4 ModularCurve.qExpand_C ModularCurve.coeff_jq_neg_one ModularCurve.constantCoeff_jNumQ ModularCurve.reduceModBivar_C_X ModularCurve.laurentMap_coeff ModularCurve.reduceModBivar_X ModularCurve.laurentMap_single"
p2m_attr_erase "simp" "ModularCurve.evalAtJInt_X ModularCurve.evalAtJMod_X ModularCurve.jqNMod_one ModularCurve.aeval_heckeGen ModularCurve.coe_mTorsionGaloisRep_apply ModularCurve.eisensteinSystem_of_dvd ModularCurve.eisensteinSystem_of_not_dvd FreyPackage.mk.sizeOf_spec FreyPackage.mk.injEq WeierstrassCurve.Affine.Point.galoisRepModuleEnd_apply AlgebraicCurve.RationalFunctionField.placeInfty_toValuationSubring AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none AlgebraicCurve.Divisor.evalFun_zero AlgebraicCurve.Place.evalAt_one ModularCurve.coeffEmb_coeff ModularCurve.coeffMap_coeff ModularCurve.coeffMap_id ModularCurve.coeffMap_single AlgebraicGeometry.SmoothProperCurve.sectionBaseChange_coe_snd AlgebraicGeometry.SmoothProperCurve.sectionBaseChange_coe_fst AlgebraicGeometry.prodKerGraph_one AlgebraicGeometry.fibrePowOver.proj_comp AlgebraicGeometry.prodKerGraph_zero AlgebraicGeometry.RelEffCartierDiv.empty_I AlgebraicGeometry.fibrePowOver.proj_comp_assoc AlgebraicCurve.SymmetricPowerPackage.mk.sizeOf_spec AlgebraicCurve.SymmetricPowerPackage.mk.injEq AlgebraicGeometry.Scheme.TwoAffineOpenCover.mk.injEq AlgebraicGeometry.Scheme.TwoAffineOpenCover.mk.sizeOf_spec AlgebraicGeometry.Scheme.TwoAffineOpenCover.pullback_U1 AlgebraicGeometry.Scheme.TwoAffineOpenCover.pullback_U0 AlgebraicGeometry.RelPicard.fst_toProdSpec AlgebraicGeometry.RelPicard.toProdSpec_fst_assoc AlgebraicGeometry.RelPicard.pointsSubBasepointModule_cons AlgebraicGeometry.RelPicard.pointsSubBasepointModule_nil AlgebraicGeometry.RelPicard.fst_toProdSpec_assoc AlgebraicGeometry.RelPicard.toProdSpec_fst"
p2m_attr_erase "simp" "AlgebraicCurve.Place.differentialCoeff_zero AlgebraicCurve.Place.differentialCoeff_dCoord AlgebraicCurve.TranscendenceTower.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.injEq AlgebraicCurve.TranscendenceTower.mk.injEq AlgebraicCurve.PoleDivisorPackage.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.sizeOf_spec AlgebraicCurve.PoleDivisorPackage.mk.injEq AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.sizeOf_spec AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.injEq AlgebraicCurve.adeleSingle_coe AlgebraicCurve.kaehlerResidueTermKFam_apply AlgebraicCurve.Place.LocalResidueData.mk.injEq AlgebraicCurve.Place.LocalResidueData.mk.sizeOf_spec AlgebraicCurve.Place.kw_ffgc_adicCompletionComapIntegers_coe AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.sizeOf_spec AlgebraicCurve.Place.mem_simplePoleSubmodule AlgebraicCurve.Place.coe_uniformizerSubring ModularCurve.Lg37.Lg37CompletionSection.mk.injEq AlgebraicCurve.Place.CoefficientFieldSection.mk.injEq AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.injEq ModularCurve.Lg37.Lg37CompletionSection.mk.sizeOf_spec AlgebraicCurve.Place.CoefficientFieldSection.mk.sizeOf_spec AlgebraicCurve.Place.poleSubmodule_one AlgebraicCurve.Place.mem_poleSubmodule AlgebraicGeometry.Scheme.OrderedAffineCover.mk.injEq AlgebraicGeometry.OModulePresheaf.mk.sizeOf_spec AlgebraicGeometry.Scheme.OrderedAffineCover.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.mk.injEq AlgebraicGeometry.Scheme.OrderedAffineCover.toCoverOf_U AlgebraicGeometry.Scheme.OrderedAffineCoverOf.mk.sizeOf_spec AlgebraicGeometry.Scheme.OrderedAffineCoverOf.mk.injEq AlgebraicGeometry.Scheme.OrderedAffineCover.restrict_U AlgebraicGeometry.OModulePresheaf.Hom.mk.injEq AlgebraicGeometry.OModulePresheaf.Hom.id_app AlgebraicGeometry.OModulePresheaf.AffHom.appSections_apply AlgebraicGeometry.OModulePresheaf.AffHom.comp_app AlgebraicGeometry.OModulePresheaf.AffSES.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.AffHom.kerMap_coe AlgebraicGeometry.OModulePresheaf.AffHom.id_app"
p2m_attr_erase "simp" "AlgebraicGeometry.OModulePresheaf.Hom.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.Hom.toAffHom_app AlgebraicGeometry.OModulePresheaf.SES.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.AffHom.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.Hom.comp_app AlgebraicGeometry.OModulePresheaf.SES.mk.injEq AlgebraicGeometry.OModulePresheaf.AffHom.mk.injEq AlgebraicGeometry.OModulePresheaf.Hom.appSections_apply AlgebraicGeometry.OModulePresheaf.AffSES.mk.injEq AlgebraicGeometry.OModulePresheaf.prod_obj AlgebraicGeometry.OModulePresheaf.restrOpen_obj AlgebraicGeometry.OModulePresheaf.DevissageStep.mk.injEq AlgebraicGeometry.OModulePresheaf.pushforward_obj AlgebraicGeometry.OModulePresheaf.im_obj AlgebraicGeometry.OModulePresheaf.pow_obj AlgebraicGeometry.OModulePresheaf.fstHom_app AlgebraicGeometry.OModulePresheaf.ker_obj AlgebraicGeometry.OModulePresheaf.coker_obj AlgebraicGeometry.OModulePresheaf.DevissageStep.mk.sizeOf_spec AlgebraicGeometry.Scheme.OrderedAffineCover.preimage_U AlgebraicGeometry.OModulePresheaf.sndHom_app AlgebraicGeometry.OModulePresheaf.Leray.restrictToPreimage_U DoubleComplex.Bounded.mk.injEq DoubleComplex.Bounded.mk.sizeOf_spec DoubleComplex.Convergence.mk.injEq DoubleComplex.Convergence.mk.sizeOf_spec DoubleComplex.SubQuot.mk.sizeOf_spec DoubleComplex.SubQuot.mk.injEq ProjSpaceCech.GradedModule.mk.injEq ProjSpaceCech.GradedModule.mk.sizeOf_spec ProjSpaceCech.GradedModule.Frac.mk.sizeOf_spec ProjSpaceCech.GradedModule.Presentation.mk.injEq ProjSpaceCech.GradedModule.Frac.mk.injEq ProjSpaceCech.GradedModule.Presentation.mk.sizeOf_spec ProjSpaceCech.GradedModule.Hom.shift_toLinearMap ProjSpaceCech.GradedModule.Hom.mk.sizeOf_spec ProjSpaceCech.GradedModule.Hom.mk.injEq TwoChartCech.Mumford.dK_apply TwoChartCech.Mumford.ι0_apply TwoChartCech.Mumford.ι1_apply"
p2m_attr_erase "simp" "TwoChartCech.KerCoprod.dK_apply TwoChartCech.KerCoprod.ι1_apply TwoChartCech.KerCoprod.ι0_apply AlgebraicGeometry.tilde.functorCompPullbackSpecIso_app"
set_option autoImplicit false

universe u

p2m_open "CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory AlgebraicGeometry NeronModelInfra GoodReductionJacobian AlgebraicGeometry.RelPicard AlgebraicGeometry.TwoGluedCurves AlgebraicCurve"

private theorem kpt_ext {k : Type u} [Field k] {Y : Scheme.{u}} (y : Y ⟶ Spec (CommRingCat.of k))
    (p q : Spec (CommRingCat.of k) ⟶ Y) (hp : p ≫ y = 𝟙 _) (hq : q ≫ y = 𝟙 _)
    (hpq : p.base (IsLocalRing.closedPoint k) = q.base (IsLocalRing.closedPoint k)) : p = q := by
  apply (Scheme.SpecToEquivOfField k Y).injective
  rw [Scheme.SpecToEquivOfField_eq_iff]
  refine ⟨hpq, ?_⟩
  set x := p.base (IsLocalRing.closedPoint k) with hx
  set φp : Y.residueField x ⟶ CommRingCat.of k := Y.descResidueField (Scheme.stalkClosedPointTo p) with hφp
  set φq : Y.residueField (q.base (IsLocalRing.closedPoint k)) ⟶ CommRingCat.of k :=
    Y.descResidueField (Scheme.stalkClosedPointTo q) with hφq
  change φp = (Y.residueFieldCongr hpq).hom ≫ φq
  let ι : CommRingCat.of k ⟶ Y.residueField x := Spec.preimage (Y.fromSpecResidueField x ≫ y)
  have hι : Spec.map ι = Y.fromSpecResidueField x ≫ y := Spec.map_preimage _
  have hp' : Spec.map φp ≫ Y.fromSpecResidueField x = p :=
    Scheme.descResidueField_stalkClosedPointTo_fromSpecResidueField k Y p
  have hq' : Spec.map ((Y.residueFieldCongr hpq).hom ≫ φq) ≫ Y.fromSpecResidueField x = q := by
    rw [Spec.map_comp, Category.assoc, Scheme.residueFieldCongr_fromSpecResidueField]
    exact Scheme.descResidueField_stalkClosedPointTo_fromSpecResidueField k Y q
  have h1 : ι ≫ φp = 𝟙 _ := by
    apply Spec.map_injective
    rw [Spec.map_comp, Spec.map_id, hι, ← Category.assoc, hp', hp]
  have h2 : ι ≫ ((Y.residueFieldCongr hpq).hom ≫ φq) = 𝟙 _ := by
    apply Spec.map_injective
    rw [Spec.map_comp, Spec.map_id, hι, ← Category.assoc, hq', hq]
  have hmono : Mono φp := by
    apply ConcreteCategory.mono_of_injective
    exact (φp.hom).injective
  haveI : IsSplitEpi φp := IsSplitEpi.mk' ⟨ι, h1⟩
  haveI : IsIso φp := isIso_of_mono_of_isSplitEpi φp
  have hι' : ι = inv φp := by
    rw [← cancel_mono φp, h1, IsIso.inv_hom_id]
  rw [hι'] at h2
  rw [← Category.id_comp ((Y.residueFieldCongr hpq).hom ≫ φq), ← IsIso.hom_inv_id φp, Category.assoc, h2,
    Category.comp_id]

theorem solution
    {k : Type u} [Field k] [IsAlgClosed k]
    {X C₁ C₂ : Scheme.{u}} (x : X ⟶ Spec (CommRingCat.of k)) [IsProper x] (hXred : IsReduced X)
    (c₁ : C₁ ⟶ Spec (CommRingCat.of k)) (c₂ : C₂ ⟶ Spec (CommRingCat.of k))
    [IsProper c₁] [SmoothOfRelativeDimension 1 c₁] [GeometricallyIntegral c₁]
    [IsProper c₂] [SmoothOfRelativeDimension 1 c₂] [GeometricallyIntegral c₂]
    (i₁ : SchemeHomOver c₁ x) (i₂ : SchemeHomOver c₂ x) [IsClosedImmersion i₁.1] [IsClosedImmersion i₂.1]
    (hjs : ∀ z : X, z ∈ Set.range i₁.1.base ∨ z ∈ Set.range i₂.1.base)
    (hcr : IsReduced (pullback i₁.1 i₂.1)) (s : ℕ) (hs : Nat.card ↥(pullback i₁.1 i₂.1) = s) (hs0 : 0 < s)

    (hc : pullback.snd i₁.1 i₂.1 ≫ c₂ = pullback.fst i₁.1 i₂.1 ≫ c₁)
    (ε : SchemeHomOver (𝟙 _) x) (ε₁ : SchemeHomOver (𝟙 _) c₁) (hε : ε₁.1 ≫ i₁.1 = ε.1)
    (ε₂ : SchemeHomOver (𝟙 _) c₂)
    (D : RelativePic0Designation k x) (hD : RepresentsRelSubPic x ε (algEquivZeroCut x ε) D)
    (D₁ : RelativePic0Designation k c₁) (hD₁ : RepresentsRelSubPic c₁ ε₁ (algEquivZeroCut c₁ ε₁) D₁)
    (D₂ : RelativePic0Designation k c₂) (hD₂ : RepresentsRelSubPic c₂ ε₂ (algEquivZeroCut c₂ ε₂) D₂)
    (ν₁ : SchemeHomOver D.toBase D₁.toBase) (ν₂ : SchemeHomOver D.toBase D₂.toBase)
    (hν₁ : ν₁ = RepresentsRelSubPic.pullbackHom i₁.1 i₁.2 hε hD hD₁)
    (hν₂ : ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of k)) (a : SchemeHomOver t D.toBase),
        Nonempty ((hD₂.poincare.pullbackAlong (NeronModelInfra.schemeHomOverComp a ν₂)).L ≅
          Scheme.Modules.rigidify (rigSection c₂ t ε₂) (pullback.snd c₂ t)
            ((Scheme.Modules.pullback (curveChange i₂.1 i₂.2 t)).obj (hD.poincare.pullbackAlong a).L)))

    (F : Type u) [Field F] [Algebra k F] [HasPrincipalDivisors k F] (hCB : ConstantsAreBase k F)
    (Mdl₁ : CurveModel k F) (e₁ : Mdl₁.C ≅ C₁) (he₁ : e₁.hom ≫ c₁ = Mdl₁.toBase)
    (Mdl₂ : CurveModel k F) (e₂ : Mdl₂.C ≅ C₂) (he₂ : e₂.hom ≫ c₂ = Mdl₂.toBase)

    (Φ₁ : Pic0 k F ≃ SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) D₁.toBase)
    (hΦ₁_add : ∀ a b, Φ₁ (a + b) =
      (RepresentsRelSubPic.relativeGroupLaw (P := algEquivZeroGroupCut c₁ ε₁) hD₁).mul _ (Φ₁ a) (Φ₁ b))
    (hΦ₁ : ∀ (P : SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) c₁) (Dv : Divisor.degZero (K := k) (F := F)),
      (Dv : Divisor k F) =
        Finsupp.single (Mdl₁.pointEquivPlace ⟨P.1 ≫ e₁.inv, by rw [← he₁, Category.assoc, e₁.inv_hom_id_assoc]; exact P.2⟩) 1 -
          Finsupp.single (Mdl₁.pointEquivPlace ⟨ε₁.1 ≫ e₁.inv, by rw [← he₁, Category.assoc, e₁.inv_hom_id_assoc]; exact ε₁.2⟩) 1 →
      Nonempty ((hD₁.poincare.pullbackAlong (Φ₁ (Pic0.mk Dv))).L ≅
        (RelEffCartierDiv.ofPoint c₁ P.1 P.2).lineBundle ⊗ (RelEffCartierDiv.ofPoint c₁ ε₁.1 ε₁.2).idealModule))
    (Φ₂ : Pic0 k F ≃ SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) D₂.toBase)
    (hΦ₂_add : ∀ a b, Φ₂ (a + b) =
      (RepresentsRelSubPic.relativeGroupLaw (P := algEquivZeroGroupCut c₂ ε₂) hD₂).mul _ (Φ₂ a) (Φ₂ b))
    (hΦ₂ : ∀ (P : SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) c₂) (Dv : Divisor.degZero (K := k) (F := F)),
      (Dv : Divisor k F) =
        Finsupp.single (Mdl₂.pointEquivPlace ⟨P.1 ≫ e₂.inv, by rw [← he₂, Category.assoc, e₂.inv_hom_id_assoc]; exact P.2⟩) 1 -
          Finsupp.single (Mdl₂.pointEquivPlace ⟨ε₂.1 ≫ e₂.inv, by rw [← he₂, Category.assoc, e₂.inv_hom_id_assoc]; exact ε₂.2⟩) 1 →
      Nonempty ((hD₂.poincare.pullbackAlong (Φ₂ (Pic0.mk Dv))).L ≅
        (RelEffCartierDiv.ofPoint c₂ P.1 P.2).lineBundle ⊗ (RelEffCartierDiv.ofPoint c₂ ε₂.1 ε₂.2).idealModule)) :
    ∃ (S : Finset (Place k F × Place k F))
      (nd : ↥S ≃ SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) (pullback.fst i₁.1 i₂.1 ≫ c₁))
      (Φ : GluedPic0 k F S ≃ SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) D.toBase),

      (∀ σ : ↥S,
        (σ : Place k F × Place k F).1 = Mdl₁.pointEquivPlace ⟨((nd σ).1 ≫ pullback.fst i₁.1 i₂.1) ≫ e₁.inv,
            by rw [← he₁, Category.assoc, e₁.inv_hom_id_assoc, Category.assoc]; exact (nd σ).2⟩ ∧
        (σ : Place k F × Place k F).2 = Mdl₂.pointEquivPlace ⟨((nd σ).1 ≫ pullback.snd i₁.1 i₂.1) ≫ e₂.inv,
            by rw [← he₂, Category.assoc, e₂.inv_hom_id_assoc, Category.assoc, hc]; exact (nd σ).2⟩) ∧
      S.card = s ∧

      (∀ a b, Φ (a + b) = (RepresentsRelSubPic.relativeGroupLaw (P := algEquivZeroGroupCut x ε) hD).mul _ (Φ a) (Φ b)) ∧

      (∀ a, postComp ν₁ (Φ a) = Φ₁ (GluedPic0.toPic0Pair S a).1 ∧ postComp ν₂ (Φ a) = Φ₂ (GluedPic0.toPic0Pair S a).2) ∧

      (∀ w : ↥S → Additive kˣ,
        IsNodeUnitModule x i₁ i₂
          (fun σ => ⟨(nd σ).1 ≫ pullback.fst i₁.1 i₂.1, by rw [Category.assoc]; exact (nd σ).2⟩)
          (fun σ => ⟨(nd σ).1 ≫ pullback.snd i₁.1 i₂.1, by rw [Category.assoc, hc]; exact (nd σ).2⟩)
          (𝟙 (Spec (CommRingCat.of k)))
          (fun σ => Units.map (Scheme.ΓSpecIso (CommRingCat.of k)).inv.hom.toMonoidHom (Additive.toMul (w σ))⁻¹)
          (hD.poincare.pullbackAlong (Φ (GluedPic0.nodeUnit S w))).L) ∧

      (∀ (P Q : SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) c₁)
        (_ : (P.1 ≫ i₁.1).base (IsLocalRing.closedPoint k) ∉ Set.range i₂.1.base)
        (_ : (Q.1 ≫ i₁.1).base (IsLocalRing.closedPoint k) ∉ Set.range i₂.1.base)
        (a : ↥(GluingData.admissible S))
        (_ : (a : GluingData k F S).1 =
          Finsupp.single (Mdl₁.pointEquivPlace ⟨P.1 ≫ e₁.inv, by rw [← he₁, Category.assoc, e₁.inv_hom_id_assoc]; exact P.2⟩) 1 -
            Finsupp.single (Mdl₁.pointEquivPlace ⟨Q.1 ≫ e₁.inv, by rw [← he₁, Category.assoc, e₁.inv_hom_id_assoc]; exact Q.2⟩) 1)
        (_ : (a : GluingData k F S).2.1 = 0) (_ : (a : GluingData k F S).2.2 = 0),
        Nonempty ((hD.poincare.pullbackAlong (Φ (GluedPic0.mk S a))).L ≅
          (RelEffCartierDiv.ofPoint x (P.1 ≫ i₁.1) (by rw [Category.assoc, i₁.2]; exact P.2)).lineBundle ⊗
            (RelEffCartierDiv.ofPoint x (Q.1 ≫ i₁.1) (by rw [Category.assoc, i₁.2]; exact Q.2)).idealModule)) ∧

      (∀ (P Q : SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) c₂)
        (_ : (P.1 ≫ i₂.1).base (IsLocalRing.closedPoint k) ∉ Set.range i₁.1.base)
        (_ : (Q.1 ≫ i₂.1).base (IsLocalRing.closedPoint k) ∉ Set.range i₁.1.base)
        (a : ↥(GluingData.admissible S))
        (_ : (a : GluingData k F S).1 = 0)
        (_ : (a : GluingData k F S).2.1 =
          Finsupp.single (Mdl₂.pointEquivPlace ⟨P.1 ≫ e₂.inv, by rw [← he₂, Category.assoc, e₂.inv_hom_id_assoc]; exact P.2⟩) 1 -
            Finsupp.single (Mdl₂.pointEquivPlace ⟨Q.1 ≫ e₂.inv, by rw [← he₂, Category.assoc, e₂.inv_hom_id_assoc]; exact Q.2⟩) 1)
        (_ : (a : GluingData k F S).2.2 = 0),
        Nonempty ((hD.poincare.pullbackAlong (Φ (GluedPic0.mk S a))).L ≅
          (RelEffCartierDiv.ofPoint x (P.1 ≫ i₂.1) (by rw [Category.assoc, i₂.2]; exact P.2)).lineBundle ⊗
            (RelEffCartierDiv.ofPoint x (Q.1 ≫ i₂.1) (by rw [Category.assoc, i₂.2]; exact Q.2)).idealModule)) := by
  classical

  obtain ⟨p₁, p₂, hinj, hnode, hinter⟩ :=
    AlgebraicGeometry.exists_rationalPoint_enumeration_of_natCard_pullback_eq k x i₁ i₂ s hs hs0

  let z : Fin s → SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) (pullback.fst i₁.1 i₂.1 ≫ c₁) := fun j =>
    ⟨pullback.lift (p₁ j).1 (p₂ j).1 (hnode j), by rw [pullback.lift_fst_assoc]; exact (p₁ j).2⟩
  have hz_fst : ∀ j, (z j).1 ≫ pullback.fst i₁.1 i₂.1 = (p₁ j).1 := fun j => pullback.lift_fst _ _ _
  have hz_snd : ∀ j, (z j).1 ≫ pullback.snd i₁.1 i₂.1 = (p₂ j).1 := fun j => pullback.lift_snd _ _ _
  have hz_bij : Function.Bijective z := by
    refine ⟨fun j j' h => ?_, fun w => ?_⟩
    · have h1 : (z j).1 ≫ pullback.fst i₁.1 i₂.1 = (z j').1 ≫ pullback.fst i₁.1 i₂.1 := by rw [h]
      rw [hz_fst, hz_fst] at h1
      exact hinj (show (p₁ j).1.base (IsLocalRing.closedPoint k) = (p₁ j').1.base (IsLocalRing.closedPoint k) by
        rw [h1])
    · have hw₁ : (w.1 ≫ pullback.fst i₁.1 i₂.1) ≫ c₁ = 𝟙 _ := by rw [Category.assoc]; exact w.2
      have hw₂ : (w.1 ≫ pullback.snd i₁.1 i₂.1) ≫ c₂ = 𝟙 _ := by rw [Category.assoc, hc]; exact w.2
      have hx : i₁.1.base ((w.1 ≫ pullback.fst i₁.1 i₂.1).base (IsLocalRing.closedPoint k)) =
          i₂.1.base ((w.1 ≫ pullback.snd i₁.1 i₂.1).base (IsLocalRing.closedPoint k)) := by
        simp only [← Scheme.Hom.comp_apply, Category.assoc, pullback.condition]
      obtain ⟨j, hj₁, hj₂⟩ := hinter _ _ hx
      refine ⟨j, Subtype.ext (pullback.hom_ext ?_ ?_)⟩
      · rw [hz_fst]; exact (kpt_ext c₁ _ _ hw₁ (p₁ j).2 hj₁).symm
      · rw [hz_snd]; exact (kpt_ext c₂ _ _ hw₂ (p₂ j).2 hj₂).symm

  let σ : Fin s → Place k F × Place k F := fun j =>
    (Mdl₁.pointEquivPlace ⟨(p₁ j).1 ≫ e₁.inv, by rw [← he₁, Category.assoc, e₁.inv_hom_id_assoc]; exact (p₁ j).2⟩,
     Mdl₂.pointEquivPlace ⟨(p₂ j).1 ≫ e₂.inv, by rw [← he₂, Category.assoc, e₂.inv_hom_id_assoc]; exact (p₂ j).2⟩)
  have hσ_inj : Function.Injective σ := by
    intro j j' h
    have h1 : (σ j).1 = (σ j').1 := congrArg Prod.fst h
    simp only [σ] at h1
    have h2 := congrArg Subtype.val (Mdl₁.pointEquivPlace.injective h1)
    have h3 : (p₁ j).1 = (p₁ j').1 := by simpa using h2
    exact hinj (show (p₁ j).1.base (IsLocalRing.closedPoint k) = (p₁ j').1.base (IsLocalRing.closedPoint k) by rw [h3])
  let S : Finset (Place k F × Place k F) := Finset.univ.image σ
  have hS_card : S.card = s := by
    rw [Finset.card_image_of_injective _ hσ_inj, Finset.card_univ, Fintype.card_fin]

  let toS : Fin s → ↥S := fun j => ⟨σ j, Finset.mem_image_of_mem σ (Finset.mem_univ j)⟩
  have htoS : Function.Bijective toS := by
    refine ⟨fun a b h => hσ_inj (congrArg Subtype.val h), fun y => ?_⟩
    obtain ⟨j, -, hj⟩ := Finset.mem_image.mp y.2
    exact ⟨j, Subtype.ext hj⟩
  let nd : ↥S ≃ SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) (pullback.fst i₁.1 i₂.1 ≫ c₁) :=
    (Equiv.ofBijective toS htoS).symm.trans (Equiv.ofBijective z hz_bij)
  have hnd : ∀ j, nd (toS j) = z j := fun j => by
    simp only [nd, Equiv.trans_apply, Equiv.ofBijective_symm_apply_apply, Equiv.ofBijective_apply]
  have hS : ∀ σ' : ↥S,
      (σ' : Place k F × Place k F).1 = Mdl₁.pointEquivPlace ⟨((nd σ').1 ≫ pullback.fst i₁.1 i₂.1) ≫ e₁.inv,
          by rw [← he₁, Category.assoc, e₁.inv_hom_id_assoc, Category.assoc]; exact (nd σ').2⟩ ∧
      (σ' : Place k F × Place k F).2 = Mdl₂.pointEquivPlace ⟨((nd σ').1 ≫ pullback.snd i₁.1 i₂.1) ≫ e₂.inv,
          by rw [← he₂, Category.assoc, e₂.inv_hom_id_assoc, Category.assoc, hc]; exact (nd σ').2⟩ := by
    intro σ'
    obtain ⟨j, rfl⟩ := htoS.2 σ'
    have hj : nd (toS j) = z j := hnd j
    refine ⟨?_, ?_⟩
    · show (σ j).1 = _
      simp only [σ]
      congr 1
      apply Subtype.ext
      show (p₁ j).1 ≫ e₁.inv = ((nd (toS j)).1 ≫ pullback.fst i₁.1 i₂.1) ≫ e₁.inv
      rw [hj, hz_fst]
    · show (σ j).2 = _
      simp only [σ]
      congr 1
      apply Subtype.ext
      show (p₂ j).1 ≫ e₂.inv = ((nd (toS j)).1 ≫ pullback.snd i₁.1 i₂.1) ≫ e₂.inv
      rw [hj, hz_snd]

  obtain ⟨φ, hφ_mul, hφ_princ, hφ_res, hφ_node, hφ_pin₁, hφ_pin₂⟩ :=
    AlgebraicGeometry.RelPicard.exists_hom_admissible_of_twoGluedSmoothCurves x hXred c₁ c₂ i₁ i₂ hjs hcr s hs hs0 hc
      ε ε₁ hε ε₂ D hD D₁ hD₁ D₂ hD₂ ν₁ ν₂ hν₁ hν₂ F hCB Mdl₁ e₁ he₁ Mdl₂ e₂ he₂ Φ₁ hΦ₁_add hΦ₁ Φ₂ hΦ₂_add hΦ₂ S nd hS

  obtain ⟨ν₁', ν₂', hν₁', hν₂', hν₁'_mul, hν₂'_mul⟩ :=
    AlgebraicGeometry.RelPicard.exists_restrictHom_pair_of_twoGluedSmoothCurves x hXred c₁ c₂ i₁ i₂ hjs hcr s hs hs0
      ε ε₁ hε ε₂ D hD D₁ hD₁ D₂ hD₂
  have hν₁eq : ν₁ = ν₁' := hν₁.trans hν₁'.symm
  have hν₁_mul : ∀ a b : SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) D.toBase,
      postComp ν₁ ((RepresentsRelSubPic.relativeGroupLaw (P := algEquivZeroGroupCut x ε) hD).mul _ a b) =
        (RepresentsRelSubPic.relativeGroupLaw (P := algEquivZeroGroupCut c₁ ε₁) hD₁).mul _ (postComp ν₁ a) (postComp ν₁ b) := by
    intro a b
    rw [hν₁eq]
    exact hν₁'_mul (𝟙 _) a b

  have hν₂pt : ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of k)) (a : SchemeHomOver t D.toBase),
      postComp ν₂ a = postComp ν₂' a := fun t a =>
    hD₂.ext_of_iso t _ _ ⟨(hν₂ t a).some ≪≫ (hν₂' t a).some.symm⟩
  have hν₂_mul : ∀ a b : SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) D.toBase,
      postComp ν₂ ((RepresentsRelSubPic.relativeGroupLaw (P := algEquivZeroGroupCut x ε) hD).mul _ a b) =
        (RepresentsRelSubPic.relativeGroupLaw (P := algEquivZeroGroupCut c₂ ε₂) hD₂).mul _ (postComp ν₂ a) (postComp ν₂ b) := by
    intro a b
    rw [hν₂pt, hν₂pt _ a, hν₂pt _ b]
    exact hν₂'_mul (𝟙 _) a b

  let law := RepresentsRelSubPic.relativeGroupLaw (P := algEquivZeroGroupCut x ε) hD
  letI : Group (SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) D.toBase) := law.pointGroup (𝟙 _)
  have hmul_def : ∀ a b : SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) D.toBase, a * b = law.mul _ a b := fun _ _ => rfl
  have hone_def : (1 : SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) D.toBase) = law.one _ := rfl

  have hφ_mul' : ∀ a b, φ (a + b) = φ a * φ b := fun a b => (hφ_mul a b).trans (hmul_def _ _).symm
  have hφ_zero : φ 0 = 1 := by
    have h := hφ_mul' 0 0
    rw [add_zero] at h
    exact left_eq_mul.mp h
  have hφ_neg : ∀ a, φ (-a) = (φ a)⁻¹ := fun a => by
    apply eq_inv_of_mul_eq_one_left
    rw [← hφ_mul', neg_add_cancel, hφ_zero]
  have hφ_princ' : ∀ a : ↥(GluingData.admissible S), GluingData.IsGluedPrincipal S (a : GluingData k F S) → φ a = 1 :=
    fun a ha => (hφ_princ a ha).trans hone_def.symm

  have hφ_wd : ∀ a b : ↥(GluingData.admissible S),
      (QuotientAddGroup.leftRel ((GluingData.gluedPrincipal S).addSubgroupOf (GluingData.admissible S))) a b → φ a = φ b := by
    intro a b hab
    rw [QuotientAddGroup.leftRel_apply, AddSubgroup.mem_addSubgroupOf] at hab
    have h1 : φ (-a + b) = 1 := hφ_princ' _ hab
    rw [hφ_mul', hφ_neg, inv_mul_eq_one] at h1
    exact h1
  let Φf : GluedPic0 k F S → SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) D.toBase :=
    Quotient.lift φ hφ_wd
  have hΦf_mk : ∀ a, Φf (GluedPic0.mk S a) = φ a := fun a => rfl

  have hΦf_inj : Function.Injective Φf := by
    intro ξ η h
    obtain ⟨a, rfl⟩ := GluedPic0.mk_surjective S ξ
    obtain ⟨b, rfl⟩ := GluedPic0.mk_surjective S η
    change φ a = φ b at h
    have h1 : φ (-a + b) = 1 := by rw [hφ_mul', hφ_neg, h, inv_mul_cancel]
    have h2 : GluedPic0.mk S (-a + b) = 0 :=
      AlgebraicGeometry.RelPicard.gluedPic0_mk_eq_zero_of_hom_admissible_eq_one_of_twoGluedSmoothCurves x hXred c₁ c₂
        i₁ i₂ hjs hcr s hs hs0 hc ε ε₁ hε ε₂ D hD D₁ hD₁ D₂ hD₂ ν₁ ν₂ hν₁ hν₂ F hCB Mdl₁ e₁ he₁ Mdl₂ e₂ he₂
        Φ₁ hΦ₁_add hΦ₁ Φ₂ hΦ₂_add hΦ₂ S nd hS φ hφ_mul hφ_princ hφ_res hφ_node hν₁_mul hν₂_mul (-a + b) (h1.trans hone_def)
    rwa [map_add, map_neg, neg_add_eq_zero] at h2
  have hΦf_surj : Function.Surjective Φf := by
    intro g
    obtain ⟨a, ha⟩ :=
      AlgebraicGeometry.RelPicard.exists_hom_admissible_eq_of_twoGluedSmoothCurves x hXred c₁ c₂
        i₁ i₂ hjs hcr s hs hs0 hc ε ε₁ hε ε₂ D hD D₁ hD₁ D₂ hD₂ ν₁ ν₂ hν₁ hν₂ F hCB Mdl₁ e₁ he₁ Mdl₂ e₂ he₂
        Φ₁ hΦ₁_add hΦ₁ Φ₂ hΦ₂_add hΦ₂ S nd hS φ hφ_mul hφ_princ hφ_res hφ_node hν₁_mul hν₂_mul g
    exact ⟨GluedPic0.mk S a, ha⟩
  let Φ : GluedPic0 k F S ≃ SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) D.toBase := Equiv.ofBijective Φf ⟨hΦf_inj, hΦf_surj⟩
  have hΦ_mk : ∀ a, Φ (GluedPic0.mk S a) = φ a := fun a => rfl
  refine ⟨S, nd, Φ, hS, hS_card, ?_, ?_, ?_, ?_, ?_⟩
  ·
    intro ξ η
    obtain ⟨a, rfl⟩ := GluedPic0.mk_surjective S ξ
    obtain ⟨b, rfl⟩ := GluedPic0.mk_surjective S η
    rw [← map_add, hΦ_mk, hΦ_mk, hΦ_mk]
    exact hφ_mul a b
  ·
    intro ξ
    obtain ⟨a, rfl⟩ := GluedPic0.mk_surjective S ξ
    rw [hΦ_mk, GluedPic0.toPic0Pair_mk]
    exact hφ_res a
  ·
    intro w
    exact hφ_node w
  ·
    intro P Q hP hQ a h₁ h₂ h₃
    exact hφ_pin₁ P Q hP hQ a h₁ h₂ h₃
  ·
    intro P Q hP hQ a h₁ h₂ h₃
    exact hφ_pin₂ P Q hP hQ a h₁ h₂ h₃

end S_AlgebraicGeometry_RelPicard_exists_gluedPic0_equiv_of_twoGluedSmoothCurves
end P2MW
export P2MW.S_AlgebraicGeometry_RelPicard_exists_gluedPic0_equiv_of_twoGluedSmoothCurves (solution)
