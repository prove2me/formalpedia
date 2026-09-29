-- Prove2me | solution 1 for AlgebraicGeometry.RelPicard.exists_hom_admissible_of_twoGluedSmoothCurves
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:03.589526+00:00
-- url     : https://prove2.me/submissions/e9df820f-aa8c-5664-96e2-2c448ad23c7b

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
import Definitions.Def_AlgebraicGeometry_RelSubPicGroup
import Definitions.Def_AlgebraicGeometry_RelativeGroupLawGrpObj
import Definitions.Def_AlgebraicGeometry_RigidifiedLineBundleOfInvertible
import Definitions.Def_AlgebraicGeometry_ModulesPullbackMonoidal
import Theorems.Thm_AlgebraicGeometry_RelPicard_exists_gluedTwist_admissible_of_twoGluedSmoothCurves
import Theorems.Thm_AlgebraicGeometry_RelPicard_nonempty_poincare_pullbackAlong_iso_foldr_ofPoint_of_additive_of_pinned
import Theorems.Thm_AlgebraicGeometry_TwoGluedCurves_exists_isInvertible_isNodeUnitModule
import Theorems.Thm_AlgebraicGeometry_TwoGluedCurves_IsNodeUnitModule_tensor
import Theorems.Thm_AlgebraicGeometry_TwoGluedCurves_isNodeUnitModule_one_unit
import Theorems.Thm_AlgebraicGeometry_TwoGluedCurves_IsNodeUnitModule_nonempty_iso
import Theorems.Thm_AlgebraicGeometry_TwoGluedCurves_IsNodeUnitModule_fibrewiseAlgEquivZero
import Theorems.Thm_AlgebraicGeometry_TwoGluedCurves_IsNodeUnitModule_nonempty_pullback_curveChange_iso_unit
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_IsInvertible_tensor
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_IsInvertible_nonempty_iso_tensorUnit_of_isLocalRing
import Theorems.Thm_AlgebraicGeometry_RelPicard_RepresentsRelSubPic_nonempty_poincare_pullbackAlong_mul_iso
import Theorems.Thm_AlgebraicGeometry_RelPicard_isAlgEquivZero_foldr_ofPoint_of_sum_filter_eq_zero
import Theorems.Thm_AlgebraicGeometry_RelPicard_isAlgEquivZero_of_isAlgEquivZero_pullback_curveChange_of_twoGluedSmoothCurves
import Theorems.Thm_AlgebraicGeometry_RelPicard_IsAlgEquivZero_baseChange
import Theorems.Thm_AlgebraicCurve_Place_deg_eq_one_iff_surjective_algebraMap_residueField
import Theorems.Thm_AlgebraicGeometry_exists_rationalPoint_enumeration_of_natCard_pullback_eq
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_RelPicard_exists_hom_admissible_of_twoGluedSmoothCurves
p2m_attr_erase "instance" "AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instNeg AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instSMulInt AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instAddCommGroup AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instAdd AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instSub AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instModuleCarrierObjOppositeOpensCarrierCarrierCommRingCatPresheafOpOpensTop AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instSMulCarrierObjOppositeOpensCarrierCarrierCommRingCatPresheafOpOpensTop AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instSMulNat AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instZero AlgebraicGeometry.RelEffCartierDiv.isClosedImmersion_subschemeι_resProdMap AlgebraicGeometry.RelEffCartierDiv.isOpenImmersion_resProdMap SheafOfModules.isIso_ihomModelToIhom AlgebraicGeometry.ChowDatum.hι_closed AlgebraicGeometry.ChowDatumProj.hιN_closed AlgebraicGeometry.ChowDatumProj.hp_proper AlgebraicGeometry.ChowDatum.hp_isoU AlgebraicGeometry.ChowDatum.hp_proper AlgebraicGeometry.ProjSpace.algebraAway AlgebraicGeometry.ProjSpace.instIsProperProdOverπ AlgebraicGeometry.ChowDatumProj.hp_isoU AlgebraicGeometry.ProjSpace.isProper_π AlgebraicGeometry.ProjSpace.finiteType_mvPolynomial AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation TwoChartCech.Sections.M0_moduleA TwoChartCech.Sections.M1_module TwoChartCech.Cover.A01_algebra TwoChartCech.Cover.A0_algebra TwoChartCech.Cover.A1_commRing TwoChartCech.Cover.A1_algebra TwoChartCech.Sections.M01_module TwoChartCech.Sections.M0_addCommGroup TwoChartCech.Sections.M0_tower TwoChartCech.Sections.M01_addCommGroup TwoChartCech.Cover.A0_commRing TwoChartCech.Sections.M1_tower TwoChartCech.Sections.M01_moduleA TwoChartCech.Sections.M0_module TwoChartCech.Sections.M1_moduleA TwoChartCech.Sections.M1_addCommGroup"
p2m_attr_erase "instance" "TwoChartCech.Cover.A01_commRing TwoChartCech.Sections.M01_tower CoherentBaseChange.TwoTermComplex.C0_module CoherentBaseChange.TwoTermComplex.C0_addCommGroup CoherentBaseChange.TwoTermComplex.C1_module CoherentBaseChange.TwoTermComplex.C1_addCommGroup CoherentBaseChange.TwoTermComplex.C0_free CoherentBaseChange.TwoTermComplex.C1_finite CoherentBaseChange.TwoTermComplex.C0_finite CoherentBaseChange.TwoTermComplex.C1_free AlgebraicCurve.IsCurveOver.instNontrivialKaehler AlgebraicCurve.IsCurveOver.instFreeKaehler AlgebraicCurve.IsCurveOver.toHasPrincipalDivisors AlgebraicCurve.IsCurveOver.instFiniteResidue AlgebraicCurve.instFundamentalIdentityOfSumRamificationInertia AlgebraicCurve.Place.instIsScalarTowerResidueFieldRestrictPushforward AlgebraicCurve.Place.instAlgebraResidueFieldRestrictPushforward AlgebraicCurve.Place.instIsLocalHomRestrictInclusion AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.SemilinearAut.instDistribMulActionSubtypeProdRingAutMemSubgroupPic0 AlgebraicCurve.SemilinearAut.instDistribMulActionSubtypeProdRingAutMemSubgroupDivisor AlgebraicCurve.Pic0.instModuleZModTorsion AlgebraicCurve.SemilinearAut.instSMulSubtypeProdRingAutMemSubgroupPlace AlgebraicCurve.SemilinearAut.instDistribMulActionTorsion AlgebraicCurve.SemilinearAut.instSMulSubtypeProdRingAutMemSubgroupPic0 AlgebraicCurve.SemilinearAut.instSMulTorsion AlgebraicCurve.SemilinearAut.instMulActionSubtypeProdRingAutMemSubgroupPlace AlgebraicCurve.SemilinearAut.instSMulCommClassZModTorsion AlgebraicCurve.SemilinearAut.instMulSemiringActionSubtypeProdRingAutMemSubgroup instDecEqAlgebraicClosureRat WeierstrassCurve.Affine.Point.instDistribMulActionAlgEquiv WeierstrassCurve.Affine.Point.instModuleZModTorsionBy WeierstrassCurve.Affine.Point.instSMulTorsionBy WeierstrassCurve.Affine.Point.instDistribMulActionTorsionBy WeierstrassCurve.Affine.Point.instSMulAlgEquiv WeierstrassCurve.Affine.Point.instSMulCommClassAlgEquivZModTorsionBy"
p2m_attr_erase "instance" "AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions AlgebraicGeometry.SmoothOfRelativeDimension.fiberToSpecResidueField AlgebraicGeometry.SmoothOfRelativeDimension.pullback_snd AlgebraicGeometry.SmoothOfRelativeDimension.pullback_fst AlgebraicGeometry.SmoothOfRelativeDimension.smooth_one AlgebraicGeometry.SmoothProperCurve.isIntegral_pullback_Spec_field AlgebraicGeometry.IsProper.fiberToSpecResidueField AlgebraicGeometry.RelEffCartierDiv.subsingleton_of_degree_zero AlgebraicCurve.instHasLocalResidue_of_hasCanonicalLocalResidueK AlgebraicCurve.instHasCanonicalLocalResidueK_of_hasCanonicalLocalResidueKStar AlgebraicCurve.Place.kw_ffgc_finiteDimensional_adicCompletion instAlgebraSubtypeMemValuationSubring_definitions AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersIntegersCompletion ModularCurve.KwF4gRRTate.instAlgebraKAdicCompletionIntegers AlgebraicCurve.Place.kw_ffgc_continuousSMul_adicCompletionComap AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersCompletionCompletion IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions AlgebraicCurve.instHasCanonicalLocalResidueK AlgebraicCurve.Place.instAlgebra_restrictResidueField AlgebraicCurve.Place.instIsScalarTower_restrictResidueField AlgebraicCurve.instHasLocalResidue AlgebraicCurve.HasSeparableResidue.of_perfectField_of_isCurveOver AlgebraicCurve.HasSeparableResidue.of_perfectField AlgebraicCurve.Place.instIsLocalHom_restrictSubringHom AlgebraicCurve.instHasCanonicalLocalResidueKStar ModularCurve.KwNo6Pin.isLocalRing_completion AlgebraicGeometry.OModulePresheaf.isScalarTower AlgebraicGeometry.Scheme.OrderedAffineCover.instLinearOrder AlgebraicGeometry.OModulePresheaf.module AlgebraicGeometry.Scheme.OrderedAffineCover.instFintype AlgebraicGeometry.Scheme.OrderedAffineCover.instFintypeIdx AlgebraicGeometry.OModulePresheaf.addCommGroup AlgebraicGeometry.Scheme.OrderedAffineCover.instDecidableEqIdx AlgebraicGeometry.OModulePresheaf.moduleSections AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instDecidableEqIdx"
p2m_attr_erase "instance" "AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instFintype AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instLinearOrder AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instFintypeIdx AlgebraicGeometry.OModulePresheaf.instSubsingletonObjZero AlgebraicGeometry.OModulePresheaf.Leray.relAltC_scalarTower AlgebraicGeometry.OModulePresheaf.Leray.ker_relAltd_modΓ AlgebraicGeometry.OModulePresheaf.Leray.relAltC_modΓ AlgebraicGeometry.OModulePresheaf.Leray.biC_abGrp AlgebraicGeometry.OModulePresheaf.Leray.relAltH_modΓ AlgebraicGeometry.OModulePresheaf.Leray.ker_relAltd_smul AlgebraicGeometry.OModulePresheaf.Leray.relAltH_scalarTower AlgebraicGeometry.OModulePresheaf.Leray.relAltH_smul AlgebraicGeometry.OModulePresheaf.Leray.biC_module DoubleComplex.instModuleE₂I DoubleComplex.Bounded.modR DoubleComplex.instModuleE₂II DoubleComplex.instAddCommGroupE₂II DoubleComplex.Bounded.abGrp DoubleComplex.instAddCommGroupE₂I ProjSpaceCech.GradedModule.H.module ProjSpaceCech.GradedModule.H.addCommGroup ProjSpaceCech.GradedModule.sec.instAdd ProjSpaceCech.GradedModule.sec.instNeg ProjSpaceCech.GradedModule.acg ProjSpaceCech.GradedModule.Frac.setoid ProjSpaceCech.GradedModule.modR ProjSpaceCech.GradedModule.sec.instModule ProjSpaceCech.GradedModule.sec.instAddCommGroup ProjSpaceCech.GradedModule.sec.instZero ProjSpaceCech.GradedModule.Presentation.fJ ProjSpaceCech.GradedModule.sec.instSMul ProjSpaceCech.Twist.H.module ProjSpaceCech.Idx.instFintype ProjSpaceCech.Twist.H.addCommGroup ProjSpaceCech.Idx.instDecidableEq ProjSpaceCech.Twist.Mon.instDecidableEq ProjSpaceCech.Twist.cochain.instAddCommGroup ProjSpaceCech.Twist.cochain.instModule"
p2m_attr_erase "simp" "AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.sub_app AlgebraicGeometry.Scheme.IdealSheafData.sres_sresTop AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.add_app AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.mk.sizeOf_spec AlgebraicGeometry.Scheme.IdealSheafData.coe_resLE AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.smul_app AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.coe_ofLE_app AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.ideal_range AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.zero_app AlgebraicGeometry.Scheme.IdealSheafData.sres_sres AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.comp_app AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.neg_app AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.id_app AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.coe_mulRight_app AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.nsmul_app AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.mk.injEq AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.zsmul_app AlgebraicGeometry.Scheme.Modules.toUnitSection_ofUnitSection AlgebraicGeometry.Scheme.Modules.pullbackSection_def AlgebraicGeometry.Scheme.Modules.ofUnitSection_toUnitSection AlgebraicGeometry.RelEffCartierDiv.supportedIn_top AlgebraicGeometry.RelEffCartierDiv.mem_supportedIn_iff AlgebraicGeometry.RelEffCartierDiv.supportedIn_top_eq AlgebraicGeometry.RelEffCartierDiv.IsUniversal.lift_comp AlgebraicGeometry.RelEffCartierDiv.functor_map_fst AlgebraicGeometry.RelEffCartierDiv.IsUniversal.homEquiv_apply AlgebraicGeometry.RelEffCartierDiv.IsUniversal.lift_pullbackAlong AlgebraicGeometry.RelEffCartierDiv.IsUniversal.homEquiv_symm_apply AlgebraicGeometry.RelEffCartierDiv.IsUniversal.lift_comp_assoc AlgebraicGeometry.RelEffCartierDiv.restrictAlong_extendAlong AlgebraicGeometry.RelEffCartierDiv.extendAlong_I AlgebraicGeometry.RelEffCartierDiv.resProdMap_snd AlgebraicGeometry.RelEffCartierDiv.restrictAlong_I AlgebraicGeometry.RelEffCartierDiv.extendAlong_restrictAlong AlgebraicGeometry.RelEffCartierDiv.resProdMap_fst_assoc AlgebraicGeometry.RelEffCartierDiv.resProdMap_snd_assoc AlgebraicGeometry.RelEffCartierDiv.resProdMap_fst AlgebraicGeometry.Scheme.Modules.pullbackLocalSection_neg AlgebraicGeometry.Scheme.Modules.pullbackLocalSection_zero AlgebraicGeometry.Scheme.Modules.pullbackLocalSection_sub"
p2m_attr_erase "simp" "AlgebraicGeometry.Scheme.Modules.pullbackLocalSection_add PresheafOfModules.InternalHom.IsSheafAux.appAt_toPresheafHom SheafOfModules.ihomSectionsEquivFamily_unit AlgebraicGeometry.Scheme.Modules.restrictHomEquivFamily_apply SheafOfModules.ihomEval_unit_app AlgebraicGeometry.Scheme.Modules.ihomEval_zero_right AlgebraicGeometry.Scheme.Modules.ihomEval_zero_left AlgebraicGeometry.Scheme.Modules.homOfFamily_app_apply SheafOfModules.unit_ihomSectionsEquivFamily AlgebraicGeometry.Scheme.Modules.familyOfHom_app AlgebraicGeometry.Scheme.Modules.restrictUnitIso_hom_app_apply AlgebraicGeometry.Scheme.Modules.restrictUnitIso_inv_app_apply AlgebraicGeometry.Scheme.Modules.restrictHomOfFamily_app_apply AlgebraicGeometry.Scheme.Modules.restrictHomEquivFamily_symm_apply AlgebraicGeometry.Scheme.Modules.ProjPresentation.mk.injEq AlgebraicGeometry.Scheme.Modules.ProjPresentation.mk.sizeOf_spec AlgebraicGeometry.ChowDatumProj.mk.sizeOf_spec AlgebraicGeometry.ChowDatum.mk.sizeOf_spec AlgebraicGeometry.ChowDatumProj.mk.injEq AlgebraicGeometry.ChowDatum.mk.injEq AlgebraicCurve.Place.congrEquiv_symm_apply AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply AlgebraicCurve.RationalFunctionField.deg_placeOfPoint AlgebraicCurve.coe_cechH0Equiv_apply AlgebraicCurve.cechH1ToH1_mk AlgebraicCurve.lSpaceOn_univ AlgebraicCurve.lSpaceOn_empty TwoChartCech.Sections.mk.injEq TwoChartCech.Cover.mk.injEq TwoChartCech.GrothendieckComplex.mk.injEq TwoChartCech.Sections.mk.sizeOf_spec TwoChartCech.Cover.mk.sizeOf_spec TwoChartCech.Cover.lineBundle_r0_apply TwoChartCech.GrothendieckComplex.mk.sizeOf_spec TwoChartCech.Cover.lineBundle_r1_apply CoherentBaseChange.TwoTermComplex.mk.sizeOf_spec CoherentBaseChange.TwoTermComplex.mk.injEq"
p2m_attr_erase "simp" "AlgebraicCurve.Divisor.mapRestrict_single AlgebraicCurve.Divisor.pushforward_single AlgebraicCurve.Place.coe_restrictInclusion AlgebraicCurve.Place.mem_fiber AlgebraicCurve.Place.restrict_toValuationSubring AlgebraicCurve.Divisor.degree_pushforward AlgebraicCurve.Place.restrictResidueMap_residue AlgebraicCurve.Pic0.coe_pushforwardDegZeroHom AlgebraicCurve.Pic0.coe_pullbackDegZeroHom AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal AlgebraicCurve.IsFrobeniusEndo.frobNormRingHom_apply ModularCurve.frobeniusPushforwardGeomLevelPic0_mk ModularCurve.coe_frobeniusGeomLevelEquiv_apply ModularCurve.coe_frobeniusPushforwardGeomLevelDegZero ModularCurve.heckeFibreGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusGeomLevel_apply_coe ModularCurve.frobeniusPullbackGeomLevelPic0OfIsCurveOver_mk ModularCurve.coe_heckeFibreGeomLevelDegZero ModularCurve.coe_frobeniusPullbackGeomLevelDegZero ModularCurve.frobeniusPullbackGeomLevelPic0_mk ModularCurve.frobeniusPullbackGeomLevel_single ModularCurve.heckeFibreGeomLevelPic0_mk ModularCurve.frobeniusPushforwardGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusPushforwardGeomLevel_single ModularCurve.qExpandAlgC_apply AlgebraicCurve.Divisor.degree_pushforwardAlong AlgebraicCurve.Pic0.coe_degZeroCorrespondence AlgebraicCurve.Place.mem_fiberAlong AlgebraicCurve.SemilinearAut.toRingAut_inv AlgebraicCurve.SemilinearAut.smul_def AlgebraicCurve.SemilinearAut.smul_single AlgebraicCurve.SemilinearAut.smul_toValuationSubring AlgebraicCurve.SemilinearAut.baseAut_inv AlgebraicCurve.SemilinearAut.baseAut_ofAlgAut AlgebraicCurve.SemilinearAut.toRingAut_ofAlgAut AlgebraicCurve.SemilinearAut.torsionRep_apply"
p2m_attr_erase "simp" "AlgebraicCurve.SemilinearAut.toRingAut_one AlgebraicCurve.SemilinearAut.deg_smul AlgebraicCurve.SemilinearAut.degree_smul AlgebraicCurve.SemilinearAut.coe_degZeroSMulHom AlgebraicCurve.SemilinearAut.baseAut_mul AlgebraicCurve.SemilinearAut.coe_smulValuationSubringEquiv_apply AlgebraicCurve.SemilinearAut.baseAut_one AlgebraicCurve.SemilinearAut.ofAlgAut_smul AlgebraicCurve.SemilinearAut.coe_torsion_smul AlgebraicCurve.SemilinearAut.toRingAut_mul AlgebraicCurve.coe_frobeniusPushforwardDegZero AlgebraicCurve.IsFrobeniusEndo.coe_frobeniusPullbackDegZero ModularCurve.jqNModC_one ModularCurve.qExpand_coeff_mul ModularCurve.qExpandₐ_apply ModularCurve.jqN_one ModularCurve.qExpand_single ModularCurve.dedekindPsi_one ModularCurve.ModularPolynomialData.mk.sizeOf_spec ModularCurve.evalAtJ_X ModularCurve.ModularPolynomialData.mk.injEq ModularCurve.constantCoeff_jNum ModularCurve.constantCoeff_eisenstein4 ModularCurve.qExpand_C ModularCurve.coeff_jq_neg_one ModularCurve.constantCoeff_jNumQ ModularCurve.reduceModBivar_C_X ModularCurve.laurentMap_coeff ModularCurve.reduceModBivar_X ModularCurve.laurentMap_single ModularCurve.evalAtJInt_X ModularCurve.evalAtJMod_X ModularCurve.jqNMod_one ModularCurve.aeval_heckeGen ModularCurve.coe_mTorsionGaloisRep_apply ModularCurve.eisensteinSystem_of_dvd ModularCurve.eisensteinSystem_of_not_dvd FreyPackage.mk.sizeOf_spec FreyPackage.mk.injEq WeierstrassCurve.Affine.Point.galoisRepModuleEnd_apply"
p2m_attr_erase "simp" "AlgebraicCurve.RationalFunctionField.placeInfty_toValuationSubring AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none AlgebraicCurve.Divisor.evalFun_zero AlgebraicCurve.Place.evalAt_one AlgebraicGeometry.SmoothProperCurve.sectionBaseChange_coe_snd AlgebraicGeometry.SmoothProperCurve.sectionBaseChange_coe_fst AlgebraicGeometry.prodKerGraph_one AlgebraicGeometry.fibrePowOver.proj_comp AlgebraicGeometry.prodKerGraph_zero AlgebraicGeometry.RelEffCartierDiv.empty_I AlgebraicGeometry.fibrePowOver.proj_comp_assoc AlgebraicCurve.SymmetricPowerPackage.mk.sizeOf_spec AlgebraicCurve.SymmetricPowerPackage.mk.injEq AlgebraicGeometry.Scheme.TwoAffineOpenCover.mk.injEq AlgebraicGeometry.Scheme.TwoAffineOpenCover.mk.sizeOf_spec AlgebraicGeometry.Scheme.TwoAffineOpenCover.pullback_U1 AlgebraicGeometry.Scheme.TwoAffineOpenCover.pullback_U0 AlgebraicGeometry.RelPicard.fst_toProdSpec AlgebraicGeometry.RelPicard.toProdSpec_fst_assoc AlgebraicGeometry.RelPicard.pointsSubBasepointModule_cons AlgebraicGeometry.RelPicard.pointsSubBasepointModule_nil AlgebraicGeometry.RelPicard.fst_toProdSpec_assoc AlgebraicGeometry.RelPicard.toProdSpec_fst AlgebraicCurve.Place.differentialCoeff_zero AlgebraicCurve.Place.differentialCoeff_dCoord AlgebraicCurve.TranscendenceTower.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.injEq AlgebraicCurve.TranscendenceTower.mk.injEq AlgebraicCurve.PoleDivisorPackage.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.sizeOf_spec AlgebraicCurve.PoleDivisorPackage.mk.injEq AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.sizeOf_spec AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.injEq AlgebraicCurve.adeleSingle_coe AlgebraicCurve.kaehlerResidueTermKFam_apply AlgebraicCurve.Place.LocalResidueData.mk.injEq AlgebraicCurve.Place.LocalResidueData.mk.sizeOf_spec"
p2m_attr_erase "simp" "AlgebraicCurve.Place.kw_ffgc_adicCompletionComapIntegers_coe AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.sizeOf_spec AlgebraicCurve.Place.mem_simplePoleSubmodule AlgebraicCurve.Place.coe_uniformizerSubring ModularCurve.Lg37.Lg37CompletionSection.mk.injEq AlgebraicCurve.Place.CoefficientFieldSection.mk.injEq AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.injEq ModularCurve.Lg37.Lg37CompletionSection.mk.sizeOf_spec AlgebraicCurve.Place.CoefficientFieldSection.mk.sizeOf_spec AlgebraicCurve.Place.poleSubmodule_one AlgebraicCurve.Place.mem_poleSubmodule AlgebraicGeometry.Scheme.OrderedAffineCover.mk.injEq AlgebraicGeometry.OModulePresheaf.mk.sizeOf_spec AlgebraicGeometry.Scheme.OrderedAffineCover.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.mk.injEq AlgebraicGeometry.Scheme.OrderedAffineCover.toCoverOf_U AlgebraicGeometry.Scheme.OrderedAffineCoverOf.mk.sizeOf_spec AlgebraicGeometry.Scheme.OrderedAffineCoverOf.mk.injEq AlgebraicGeometry.Scheme.OrderedAffineCover.restrict_U AlgebraicGeometry.OModulePresheaf.Hom.mk.injEq AlgebraicGeometry.OModulePresheaf.Hom.id_app AlgebraicGeometry.OModulePresheaf.AffHom.appSections_apply AlgebraicGeometry.OModulePresheaf.AffHom.comp_app AlgebraicGeometry.OModulePresheaf.AffSES.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.AffHom.kerMap_coe AlgebraicGeometry.OModulePresheaf.AffHom.id_app AlgebraicGeometry.OModulePresheaf.Hom.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.Hom.toAffHom_app AlgebraicGeometry.OModulePresheaf.SES.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.AffHom.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.Hom.comp_app AlgebraicGeometry.OModulePresheaf.SES.mk.injEq AlgebraicGeometry.OModulePresheaf.AffHom.mk.injEq AlgebraicGeometry.OModulePresheaf.Hom.appSections_apply AlgebraicGeometry.OModulePresheaf.AffSES.mk.injEq AlgebraicGeometry.OModulePresheaf.prod_obj AlgebraicGeometry.OModulePresheaf.restrOpen_obj AlgebraicGeometry.OModulePresheaf.DevissageStep.mk.injEq AlgebraicGeometry.OModulePresheaf.pushforward_obj AlgebraicGeometry.OModulePresheaf.im_obj"
p2m_attr_erase "simp" "AlgebraicGeometry.OModulePresheaf.pow_obj AlgebraicGeometry.OModulePresheaf.fstHom_app AlgebraicGeometry.OModulePresheaf.ker_obj AlgebraicGeometry.OModulePresheaf.coker_obj AlgebraicGeometry.OModulePresheaf.DevissageStep.mk.sizeOf_spec AlgebraicGeometry.Scheme.OrderedAffineCover.preimage_U AlgebraicGeometry.OModulePresheaf.sndHom_app AlgebraicGeometry.OModulePresheaf.Leray.restrictToPreimage_U DoubleComplex.Bounded.mk.injEq DoubleComplex.Bounded.mk.sizeOf_spec DoubleComplex.Convergence.mk.injEq DoubleComplex.Convergence.mk.sizeOf_spec DoubleComplex.SubQuot.mk.sizeOf_spec DoubleComplex.SubQuot.mk.injEq ProjSpaceCech.GradedModule.mk.injEq ProjSpaceCech.GradedModule.mk.sizeOf_spec ProjSpaceCech.GradedModule.Frac.mk.sizeOf_spec ProjSpaceCech.GradedModule.Presentation.mk.injEq ProjSpaceCech.GradedModule.Frac.mk.injEq ProjSpaceCech.GradedModule.Presentation.mk.sizeOf_spec ProjSpaceCech.GradedModule.Hom.shift_toLinearMap ProjSpaceCech.GradedModule.Hom.mk.sizeOf_spec ProjSpaceCech.GradedModule.Hom.mk.injEq TwoChartCech.Mumford.dK_apply TwoChartCech.Mumford.ι0_apply TwoChartCech.Mumford.ι1_apply TwoChartCech.KerCoprod.dK_apply TwoChartCech.KerCoprod.ι1_apply TwoChartCech.KerCoprod.ι0_apply AlgebraicGeometry.tilde.functorCompPullbackSpecIso_app"
set_option autoImplicit false

universe u

p2m_open "CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory AlgebraicGeometry NeronModelInfra GoodReductionJacobian AlgebraicGeometry.RelPicard AlgebraicGeometry.TwoGluedCurves AlgebraicCurve"

namespace PhiHomAux

theorem surjective_algebraMap_residueField {K : Type u} [Field K] [IsAlgClosed K] {L : Type u} [Field L] [Algebra K L]
    (M : CurveModel K L) (v : Place K L) : Function.Surjective (algebraMap K v.ResidueField) := by
  classical
  obtain ⟨x, rfl⟩ := M.placeOfPoint_bijective.2 v
  let A : ValuationSubring L := (M.placeOfPoint x).toValuationSubring
  let S : CommRingCat := M.C.presheaf.stalk x.1

  let ρ : CommRingCat.of K ⟶ M.C.residueField x.1 :=
    (Scheme.ΓSpecIso (CommRingCat.of K)).inv ≫ M.toBase.appTop ≫ M.C.Γevaluation x.1
  have hA : M.C.fromSpecResidueField x.1 ≫ M.toBase = Spec.map ρ := by
    rw [← Scheme.Hom.SpecMap_residueFieldMap_fromSpecResidueField,
      ← Scheme.Spec.map_residueFieldIso_inv_eq_fromSpecResidueField]
    simp only [← Spec.map_comp]
    congr 1
    rw [Scheme.Spec.algebraMap_residueFieldIso_inv (CommRingCat.of K) (M.toBase.base x.1)]
    simp only [ρ, Category.assoc, Scheme.residue_residueFieldMap, Scheme.Hom.germ_stalkMap_assoc]
    rfl

  have hρ : ρ = (residueFieldIsoBase M.toBase x.1 x.2).inv :=
    Spec.map_injective (by rw [← hA, SpecMap_residueFieldIsoBase_inv])
  have hρsurj : Function.Surjective ρ.hom := by
    rw [hρ]
    exact (ConcreteCategory.bijective_of_isIso ((residueFieldIsoBase M.toBase x.1 x.2).inv)).2

  let φ : S →+* L :=
    (M.ffEquiv.symm : M.C.functionField ≃+* L).toRingHom.comp (algebraMap S M.C.functionField)
  have hφrange : φ.range = A.toSubring := M.range_stalk_eq x
  have hφmem : ∀ s : S, φ s ∈ A := fun s => by
    have h : φ s ∈ φ.range := ⟨s, rfl⟩
    rw [hφrange] at h
    exact h
  let ψ : S →+* A := φ.codRestrict A hφmem
  have hψ : ∀ s : S, (ψ s : L) = φ s := fun _ => rfl
  have hψinj : Function.Injective ψ := by
    intro a b h
    have h' : φ a = φ b := by rw [← hψ, ← hψ, h]
    exact IsFractionRing.injective S M.C.functionField (M.ffEquiv.symm.injective h')
  have hψsurj : Function.Surjective ψ := by
    intro a
    have ha : (a : L) ∈ φ.range := by rw [hφrange]; exact a.2
    obtain ⟨s, hs⟩ := ha
    exact ⟨s, Subtype.ext hs⟩
  let e : S ≃+* A := RingEquiv.ofBijective ψ ⟨hψinj, hψsurj⟩

  let c : K → S := fun a =>
    M.C.presheaf.germ ⊤ x.1 trivial (M.toBase.appTop ((Scheme.ΓSpecIso (CommRingCat.of K)).inv a))
  have hρc : ∀ a : K, ρ.hom a = IsLocalRing.residue S (c a) := fun _ => rfl
  have hgerm : ∀ t : Γ(M.C, ⊤), algebraMap S M.C.functionField (M.C.presheaf.germ ⊤ x.1 trivial t)
      = M.C.presheaf.germ ⊤ (genericPoint M.C) trivial t := by
    intro t
    change (M.C.presheaf.germ ⊤ x.1 trivial ≫ M.C.presheaf.stalkSpecializes
      ((genericPoint_spec M.C).specializes trivial)) t = _
    rw [TopCat.Presheaf.germ_stalkSpecializes]
  have hφc : ∀ a : K, φ (c a) = algebraMap K L a := by
    intro a
    have h1 : algebraMap S M.C.functionField (c a) = baseToFunctionField M.toBase a := hgerm _
    simp only [φ, RingHom.coe_comp, Function.comp_apply, h1, ← M.ffEquiv_algebraMap]
    exact M.ffEquiv.symm_apply_apply _
  have hψc : ∀ a : K, ψ (c a) = algebraMap K A a := fun a =>
    Subtype.ext (by rw [hψ, hφc]; rfl)

  intro r
  obtain ⟨g, rfl⟩ := IsLocalRing.residue_surjective (R := A) r
  obtain ⟨s, rfl⟩ := hψsurj g
  obtain ⟨a, ha⟩ := hρsurj (IsLocalRing.residue S s)
  refine ⟨a, ?_⟩
  rw [hρc] at ha
  have hm : c a - s ∈ IsLocalRing.maximalIdeal S := by
    rw [← Ideal.Quotient.eq]
    exact ha
  have hm' : ψ (c a - s) ∈ IsLocalRing.maximalIdeal A := by
    rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
    intro hu
    have hu' : IsUnit (c a - s) := by simpa using (show IsUnit (e (c a - s)) from hu).map e.symm
    exact ((IsLocalRing.mem_maximalIdeal _).mp hm) hu'
  have hres : IsLocalRing.residue A (ψ (c a)) = IsLocalRing.residue A (ψ s) := by
    rw [← sub_eq_zero, ← map_sub, ← map_sub, IsLocalRing.residue_eq_zero_iff]
    exact hm'
  change algebraMap K (IsLocalRing.ResidueField A) a = IsLocalRing.residue A (ψ s)
  rw [← hres, hψc]
  rfl

theorem isNodeUnitModule_of_iso {κ : Type u} [Field κ]
    {X C₁ C₂ : Scheme.{u}} {x : X ⟶ Spec (.of κ)}
    {c₁ : C₁ ⟶ Spec (.of κ)} {c₂ : C₂ ⟶ Spec (.of κ)}
    {i₁ : SchemeHomOver c₁ x} {i₂ : SchemeHomOver c₂ x}
    {ι : Type u} {p₁ : ι → SchemeHomOver (𝟙 (Spec (.of κ))) c₁} {p₂ : ι → SchemeHomOver (𝟙 (Spec (.of κ))) c₂}
    {T : Scheme.{u}} {h : T ⟶ Spec (.of κ)} {u : ι → Γ(T, ⊤)ˣ} {M M' : (pullback x h).Modules}
    (e : M ≅ M') (hM : IsNodeUnitModule x i₁ i₂ p₁ p₂ h u M) : IsNodeUnitModule x i₁ i₂ p₁ p₂ h u M' := by
  obtain ⟨j₁, j₂, hj⟩ := hM
  refine ⟨e.inv ≫ j₁, e.inv ≫ j₂, fun W => ?_⟩
  have hsurj : Function.Surjective (e.inv.app W) := fun m => ⟨e.hom.app W m, by
    change (e.hom ≫ e.inv).app W m = m
    rw [e.hom_inv_id]; rfl⟩
  have hinjE : Function.Injective (e.inv.app W) := fun m n hmn => by
    have h2 : (e.inv ≫ e.hom).app W m = (e.inv ≫ e.hom).app W n := by
      change e.hom.app W (e.inv.app W m) = e.hom.app W (e.inv.app W n)
      rw [hmn]
    rw [e.inv_hom_id] at h2
    exact h2
  have hcomp : (fun m : Γ(M', W) => ((e.inv ≫ j₁).app W m, (e.inv ≫ j₂).app W m)) =
      (fun m : Γ(M, W) => (j₁.app W m, j₂.app W m)) ∘ (e.inv.app W) := rfl
  rw [hcomp, Set.range_comp, hsurj.range_eq, Set.image_univ]
  exact ⟨(hj W).1.comp hinjE, (hj W).2⟩

theorem classify_tensor {R : Type u} [CommRing R] {C : Scheme.{u}} {c : C ⟶ Spec (CommRingCat.of R)}
    {ε : SchemeHomOver (𝟙 (Spec (CommRingCat.of R))) c}
    {P : SubPicGroupCondition c ε} {D : RelativePic0Designation R c}
    (h : RepresentsRelSubPic c ε P.toSubPicCondition D)
    {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) (L M : RigidifiedLineBundle c ε t)
    (hL : P.P t L) (hM : P.P t M) :
    h.classify t (L.tensor M) (P.tensor_mem t L M hL hM) = h.relativeGroupLaw.mul t (h.classify t L hL) (h.classify t M hM) := by
  symm
  apply h.classify_unique
  letI := h.grpObj
  letI := h.relativeGroupLaw.pointGroup t
  have hmul : h.relativeGroupLaw.mul t (h.classify t L hL) (h.classify t M hM) = h.classify t L hL * h.classify t M hM := rfl
  obtain ⟨e⟩ : Nonempty ((h.poincare.pullbackAlong (h.classify t L hL * h.classify t M hM)).L ≅
      (h.poincare.pullbackAlong (h.classify t L hL)).L ⊗ (h.poincare.pullbackAlong (h.classify t M hM)).L) := by
    have := RepresentsRelSubPic.nonempty_poincare_pullbackAlong_mul_iso h (T := Over.mk t)
      (schemeHomOverToOverHom (h.classify t L hL)) (schemeHomOverToOverHom (h.classify t M hM))
    exact this
  rw [hmul]
  exact ⟨e ≪≫ ((h.classify_spec t L hL).some ⊗ᵢ (h.classify_spec t M hM).some)⟩

theorem classify_congr {R : Type u} [CommRing R] {C : Scheme.{u}} {c : C ⟶ Spec (CommRingCat.of R)}
    {ε : SchemeHomOver (𝟙 (Spec (CommRingCat.of R))) c}
    {P : SubPicCondition c ε} {D : RelativePic0Designation R c}
    (h : RepresentsRelSubPic c ε P D)
    {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) (L M : RigidifiedLineBundle c ε t)
    (hL : P.P t L) (hM : P.P t M) (e : Nonempty (L.L ≅ M.L)) :
    h.classify t L hL = h.classify t M hM :=
  h.classify_unique t M hM _ ⟨(h.classify_spec t L hL).some ≪≫ e.some⟩

def rlbOfInvertible {κ : Type u} [Field κ] {X : Scheme.{u}} {x : X ⟶ Spec (CommRingCat.of κ)}
    (ε : SchemeHomOver (𝟙 (Spec (CommRingCat.of κ))) x)
    (L : (pullback x (𝟙 (Spec (CommRingCat.of κ)))).Modules) (hL : Scheme.Modules.IsInvertible L) :
    RigidifiedLineBundle x ε (𝟙 (Spec (CommRingCat.of κ))) :=
  ⟨L, hL, Scheme.Modules.IsInvertible.nonempty_iso_tensorUnit_of_isLocalRing (hL.pullback _)⟩

@[scoped simp] theorem rlbOfInvertible_L {κ : Type u} [Field κ] {X : Scheme.{u}} {x : X ⟶ Spec (CommRingCat.of κ)}
    (ε : SchemeHomOver (𝟙 (Spec (CommRingCat.of κ))) x)
    (L : (pullback x (𝟙 (Spec (CommRingCat.of κ)))).Modules) (hL : Scheme.Modules.IsInvertible L) :
    (rlbOfInvertible ε L hL).L = L := rfl

theorem nonempty_rigidify_iso {κ : Type u} [Field κ] {P : Scheme.{u}} (σ : Spec (CommRingCat.of κ) ⟶ P)
    (q : P ⟶ Spec (CommRingCat.of κ)) (L : P.Modules) (hL : Scheme.Modules.IsInvertible L) :
    Nonempty (Scheme.Modules.rigidify σ q L ≅ L) := by

  obtain ⟨e1⟩ := Scheme.Modules.IsInvertible.nonempty_iso_tensorUnit_of_isLocalRing (hL.pullback σ)
  have e2 : Scheme.Modules.dual ((Scheme.Modules.pullback σ).obj L) ≅ 𝟙_ _ :=
    Scheme.Modules.dualMapIso e1 ≪≫ (Scheme.Modules.nonempty_dual_tensorUnit_iso _).some
  exact ⟨whiskerLeftIso L ((Scheme.Modules.pullback q).mapIso e2 ≪≫ Scheme.Modules.pullbackTensorUnitObjIso q) ≪≫ ρ_ L⟩

end PhiHomAux
p2m_reactivate "P2MW.S_AlgebraicGeometry_RelPicard_exists_hom_admissible_of_twoGluedSmoothCurves.PhiHomAux"

namespace PhiHomAux

theorem isAlgEquivZero_foldr_support {k : Type u} [Field k] [IsAlgClosed k] {C : Scheme.{u}} (c : C ⟶ Spec (CommRingCat.of k))
    [IsProper c] [SmoothOfRelativeDimension 1 c] [GeometricallyIntegral c]
    {F : Type u} [Field F] [Algebra k F] (Mdl : CurveModel k F)
    (pt : Place k F → (Spec (CommRingCat.of k) ⟶ C)) (hpt : ∀ v, pt v ≫ c = 𝟙 _)
    (Dv : Divisor k F) (hDv : Dv ∈ Divisor.degZero (K := k) (F := F)) :
    IsAlgEquivZero (pullback.snd c (𝟙 (Spec (CommRingCat.of k))))
      ((Dv.support.toList).foldr
        (fun v M => ((RelEffCartierDiv.ofPoint c (pt v) (hpt v)).I ^ (Dv v).toNat).invModule ⊗
          ((RelEffCartierDiv.ofPoint c (pt v) (hpt v)).I ^ (-(Dv v)).toNat).module ⊗ M)
        (𝟙_ (pullback c (𝟙 (Spec (CommRingCat.of k)))).Modules)) := by
  classical
  set l := Dv.support.toList with hl

  have hdeg1 : ∀ v : Place k F, v.deg = 1 := fun v =>
    (Place.deg_eq_one_iff_surjective_algebraMap_residueField v).2 (surjective_algebraMap_residueField Mdl v)
  have hsum : (∑ v ∈ Dv.support, Dv v) = 0 := by
    have h0 : Divisor.degree Dv = 0 := hDv
    rw [Divisor.degree, Finsupp.liftAddHom_apply, Finsupp.sum] at h0
    simpa [hdeg1] using h0

  have key := AlgebraicGeometry.RelPicard.isAlgEquivZero_foldr_ofPoint_of_sum_filter_eq_zero c
    (fun i : Fin l.length => pt (l.get i)) (fun i => hpt _) (fun _ => True)
    (fun i => (Dv (l.get i)).toNat) (fun i => (-(Dv (l.get i))).toNat) (by
      have h1 : ∀ n : ℤ, ((n.toNat : ℤ) - ((-n).toNat : ℤ)) = n := fun n => Int.toNat_sub_toNat_neg n
      rw [Finset.filter_true]
      simp only [h1]
      rw [Fin.sum_univ_def]
      have h2 : (List.finRange l.length).map (fun i => Dv (l.get i)) = l.map Dv := by
        conv_rhs => rw [← List.map_get_finRange l]
        rw [List.map_map]
        rfl
      rw [h2, hl, Finset.sum_map_toList]
      exact hsum)
  have hfold : (List.finRange l.length).foldr
      (fun i M => if True then
        ((RelEffCartierDiv.ofPoint c (pt (l.get i)) (hpt _)).I ^ (Dv (l.get i)).toNat).invModule ⊗
          ((RelEffCartierDiv.ofPoint c (pt (l.get i)) (hpt _)).I ^ (-(Dv (l.get i))).toNat).module ⊗ M
        else M)
      (𝟙_ (pullback c (𝟙 (Spec (CommRingCat.of k)))).Modules) =
      l.foldr (fun v M => ((RelEffCartierDiv.ofPoint c (pt v) (hpt v)).I ^ (Dv v).toNat).invModule ⊗
          ((RelEffCartierDiv.ofPoint c (pt v) (hpt v)).I ^ (-(Dv v)).toNat).module ⊗ M)
        (𝟙_ (pullback c (𝟙 (Spec (CommRingCat.of k)))).Modules) := by
    conv_rhs => rw [← List.map_get_finRange l, List.foldr_map]
    try simp only [if_true]
    try rfl
  rw [hfold] at key
  exact key

end PhiHomAux
p2m_reactivate "P2MW.S_AlgebraicGeometry_RelPicard_exists_hom_admissible_of_twoGluedSmoothCurves.PhiHomAux"

open PhiHomAux in

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
        (RelEffCartierDiv.ofPoint c₂ P.1 P.2).lineBundle ⊗ (RelEffCartierDiv.ofPoint c₂ ε₂.1 ε₂.2).idealModule))

    (S : Finset (Place k F × Place k F))
    (nd : ↥S ≃ SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) (pullback.fst i₁.1 i₂.1 ≫ c₁))
    (hS : ∀ σ : ↥S,
        (σ : Place k F × Place k F).1 = Mdl₁.pointEquivPlace ⟨((nd σ).1 ≫ pullback.fst i₁.1 i₂.1) ≫ e₁.inv,
            by rw [← he₁, Category.assoc, e₁.inv_hom_id_assoc, Category.assoc]; exact (nd σ).2⟩ ∧
        (σ : Place k F × Place k F).2 = Mdl₂.pointEquivPlace ⟨((nd σ).1 ≫ pullback.snd i₁.1 i₂.1) ≫ e₂.inv,
            by rw [← he₂, Category.assoc, e₂.inv_hom_id_assoc, Category.assoc, hc]; exact (nd σ).2⟩) :
    ∃ φ : ↥(GluingData.admissible S) → SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) D.toBase,

      (∀ a b, φ (a + b) = (RepresentsRelSubPic.relativeGroupLaw (P := algEquivZeroGroupCut x ε) hD).mul _ (φ a) (φ b)) ∧

      (∀ a : ↥(GluingData.admissible S), GluingData.IsGluedPrincipal S (a : GluingData k F S) →
        φ a = (RepresentsRelSubPic.relativeGroupLaw (P := algEquivZeroGroupCut x ε) hD).one _) ∧

      (∀ a : ↥(GluingData.admissible S), postComp ν₁ (φ a) = Φ₁ (Pic0.mk ⟨(a : GluingData k F S).1, a.2.1⟩) ∧
        postComp ν₂ (φ a) = Φ₂ (Pic0.mk ⟨(a : GluingData k F S).2.1, a.2.2.1⟩)) ∧

      (∀ w : ↥S → Additive kˣ,
        IsNodeUnitModule x i₁ i₂
          (fun σ => ⟨(nd σ).1 ≫ pullback.fst i₁.1 i₂.1, by rw [Category.assoc]; exact (nd σ).2⟩)
          (fun σ => ⟨(nd σ).1 ≫ pullback.snd i₁.1 i₂.1, by rw [Category.assoc, hc]; exact (nd σ).2⟩)
          (𝟙 (Spec (CommRingCat.of k)))
          (fun σ => Units.map (Scheme.ΓSpecIso (CommRingCat.of k)).inv.hom.toMonoidHom (Additive.toMul (w σ))⁻¹)
          (hD.poincare.pullbackAlong (φ ⟨(0, 0, w), GluingData.zero_zero_mem_admissible S w⟩)).L) ∧

      (∀ (P Q : SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) c₁)
        (_ : (P.1 ≫ i₁.1).base (IsLocalRing.closedPoint k) ∉ Set.range i₂.1.base)
        (_ : (Q.1 ≫ i₁.1).base (IsLocalRing.closedPoint k) ∉ Set.range i₂.1.base)
        (a : ↥(GluingData.admissible S))
        (_ : (a : GluingData k F S).1 =
          Finsupp.single (Mdl₁.pointEquivPlace ⟨P.1 ≫ e₁.inv, by rw [← he₁, Category.assoc, e₁.inv_hom_id_assoc]; exact P.2⟩) 1 -
            Finsupp.single (Mdl₁.pointEquivPlace ⟨Q.1 ≫ e₁.inv, by rw [← he₁, Category.assoc, e₁.inv_hom_id_assoc]; exact Q.2⟩) 1)
        (_ : (a : GluingData k F S).2.1 = 0) (_ : (a : GluingData k F S).2.2 = 0),
        Nonempty ((hD.poincare.pullbackAlong (φ a)).L ≅
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
        Nonempty ((hD.poincare.pullbackAlong (φ a)).L ≅
          (RelEffCartierDiv.ofPoint x (P.1 ≫ i₂.1) (by rw [Category.assoc, i₂.2]; exact P.2)).lineBundle ⊗
            (RelEffCartierDiv.ofPoint x (Q.1 ≫ i₂.1) (by rw [Category.assoc, i₂.2]; exact Q.2)).idealModule)) := by
  classical
  haveI : IsReduced X := hXred

  let pt₁ : Place k F → (Spec (CommRingCat.of k) ⟶ C₁) := fun v => (Mdl₁.pointEquivPlace.symm v).1 ≫ e₁.hom
  have hpt₁ : ∀ v, pt₁ v ≫ c₁ = 𝟙 _ := fun v => by
    simp only [pt₁, Category.assoc, he₁]; exact (Mdl₁.pointEquivPlace.symm v).2
  have hpt₁' : ∀ v, pt₁ v = (Mdl₁.pointEquivPlace.symm v).1 ≫ e₁.hom := fun v => rfl
  let pt₂ : Place k F → (Spec (CommRingCat.of k) ⟶ C₂) := fun v => (Mdl₂.pointEquivPlace.symm v).1 ≫ e₂.hom
  have hpt₂ : ∀ v, pt₂ v ≫ c₂ = 𝟙 _ := fun v => by
    simp only [pt₂, Category.assoc, he₂]; exact (Mdl₂.pointEquivPlace.symm v).2
  have hpt₂' : ∀ v, pt₂ v = (Mdl₂.pointEquivPlace.symm v).1 ≫ e₂.hom := fun v => rfl

  obtain ⟨E, hE_inv, hE_mul, hE_zero, hE_res, hE_princ, hE_pin₁, hE_pin₂⟩ :=
    AlgebraicGeometry.RelPicard.exists_gluedTwist_admissible_of_twoGluedSmoothCurves x hXred c₁ c₂ i₁ i₂ hjs hcr s hs hs0 hc
      F hCB Mdl₁ e₁ he₁ Mdl₂ e₂ he₂ pt₁ hpt₁ hpt₁' pt₂ hpt₂ hpt₂' S nd hS

  let p₁ : ↥S → SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) c₁ :=
    fun σ => ⟨(nd σ).1 ≫ pullback.fst i₁.1 i₂.1, by rw [Category.assoc]; exact (nd σ).2⟩
  let p₂ : ↥S → SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) c₂ :=
    fun σ => ⟨(nd σ).1 ≫ pullback.snd i₁.1 i₂.1, by rw [Category.assoc, hc]; exact (nd σ).2⟩
  have hnode : ∀ σ, (p₁ σ).1 ≫ i₁.1 = (p₂ σ).1 ≫ i₂.1 := fun σ => by
    simp only [p₁, p₂, Category.assoc, pullback.condition]
  have hinj : Function.Injective fun σ => (p₁ σ).1.base (IsLocalRing.closedPoint k) := by
    intro σ τ h
    apply nd.injective
    apply Subtype.ext
    have h' : (nd σ).1.base (IsLocalRing.closedPoint k) = (nd τ).1.base (IsLocalRing.closedPoint k) := by
      apply (pullback.fst i₁.1 i₂.1).isClosedEmbedding.injective
      simp only [Scheme.Hom.comp_base, TopCat.coe_comp, Function.comp_apply] at h
      exact h
    exact ext_of_apply_closedPoint_eq (pullback.fst i₁.1 i₂.1 ≫ c₁) (nd σ).2 (nd τ).2 h'
  have hinter : ∀ (q₁ : C₁) (q₂ : C₂), i₁.1.base q₁ = i₂.1.base q₂ →
      ∃ σ, q₁ = (p₁ σ).1.base (IsLocalRing.closedPoint k) ∧ q₂ = (p₂ σ).1.base (IsLocalRing.closedPoint k) := by
    obtain ⟨q₁', q₂', -, hnode', hinter'⟩ :=
      AlgebraicGeometry.exists_rationalPoint_enumeration_of_natCard_pullback_eq k x i₁ i₂ s hs hs0
    intro q₁ q₂ hq
    obtain ⟨j, hq₁, hq₂⟩ := hinter' q₁ q₂ hq
    let z : SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) (pullback.fst i₁.1 i₂.1 ≫ c₁) :=
      ⟨pullback.lift (q₁' j).1 (q₂' j).1 (hnode' j), by rw [pullback.lift_fst_assoc]; exact (q₁' j).2⟩
    refine ⟨nd.symm z, ?_, ?_⟩
    · rw [hq₁]
      show _ = ((nd (nd.symm z)).1 ≫ pullback.fst i₁.1 i₂.1).base _
      rw [Equiv.apply_symm_apply]
      simp only [z, pullback.lift_fst]
    · rw [hq₂]
      show _ = ((nd (nd.symm z)).1 ≫ pullback.snd i₁.1 i₂.1).base _
      rw [Equiv.apply_symm_apply]
      simp only [z, pullback.lift_snd]

  have hN := fun (u : ↥S → Γ(Spec (CommRingCat.of k), ⊤)ˣ) =>
    AlgebraicGeometry.TwoGluedCurves.exists_isInvertible_isNodeUnitModule k x i₁ i₂ hjs p₁ p₂ hinj hnode hinter hcr
      (𝟙 (Spec (CommRingCat.of k))) u
  let N : (↥S → Γ(Spec (CommRingCat.of k), ⊤)ˣ) → (pullback x (𝟙 (Spec (CommRingCat.of k)))).Modules :=
    fun u => (hN u).choose
  have hN_inv : ∀ u, Scheme.Modules.IsInvertible (N u) := fun u => (hN u).choose_spec.1
  have hN_nu : ∀ u, IsNodeUnitModule x i₁ i₂ p₁ p₂ (𝟙 (Spec (CommRingCat.of k))) u (N u) := fun u => (hN u).choose_spec.2

  have hN_mul : ∀ u u', Nonempty (N (u * u') ≅ N u ⊗ N u') := fun u u' =>
    AlgebraicGeometry.TwoGluedCurves.IsNodeUnitModule.nonempty_iso (hN_nu (u * u'))
      (AlgebraicGeometry.TwoGluedCurves.IsNodeUnitModule.tensor k x i₁ i₂ hjs p₁ p₂ hinj hnode hinter hcr
        (hN_inv u) (hN_nu u) (hN_inv u') (hN_nu u'))
  have hN_one : Nonempty (N 1 ≅ 𝟙_ (pullback x (𝟙 (Spec (CommRingCat.of k)))).Modules) :=
    AlgebraicGeometry.TwoGluedCurves.IsNodeUnitModule.nonempty_iso (hN_nu 1)
      (AlgebraicGeometry.TwoGluedCurves.isNodeUnitModule_one_unit k x i₁ i₂ hjs p₁ p₂ hinj hnode hinter hcr (𝟙 _))

  have hN_res := fun u => AlgebraicGeometry.TwoGluedCurves.IsNodeUnitModule.nonempty_pullback_curveChange_iso_unit k x i₁ i₂ hjs
    p₁ p₂ hinj hnode hinter hcr (hN_inv u) (hN_nu u)

  let un : (↥S → Additive kˣ) → (↥S → Γ(Spec (CommRingCat.of k), ⊤)ˣ) :=
    fun w σ => Units.map (Scheme.ΓSpecIso (CommRingCat.of k)).inv.hom.toMonoidHom (Additive.toMul (w σ))⁻¹
  have hun_add : ∀ w w', un (w + w') = un w * un w' := fun w w' => by
    funext σ
    simp only [un, Pi.add_apply, Pi.mul_apply, toMul_add, mul_inv, map_mul]
  have hun_zero : un 0 = 1 := by
    funext σ
    simp only [un, Pi.zero_apply, Pi.one_apply, toMul_zero, inv_one, map_one]

  let RN : (↥S → Additive kˣ) → RigidifiedLineBundle x ε (𝟙 (Spec (CommRingCat.of k))) :=
    fun w => rlbOfInvertible ε (N (un w)) (hN_inv _)
  have hRN_cut : ∀ w, FibrewiseAlgEquivZero (RN w) := fun w =>
    AlgebraicGeometry.TwoGluedCurves.IsNodeUnitModule.fibrewiseAlgEquivZero k x i₁ i₂ hjs p₁ p₂ hinj hnode hinter hcr ε
      (RN w) (hN_nu _)

  let RE : ↥(GluingData.admissible S) → RigidifiedLineBundle x ε (𝟙 (Spec (CommRingCat.of k))) :=
    fun a => rlbOfInvertible ε (E a) (hE_inv a)
  have hRE_cut : ∀ a, FibrewiseAlgEquivZero (RE a) := by
    intro a
    have key : IsAlgEquivZero (pullback.snd x (𝟙 (Spec (CommRingCat.of k)))) (E a) := by
      refine AlgebraicGeometry.RelPicard.isAlgEquivZero_of_isAlgEquivZero_pullback_curveChange_of_twoGluedSmoothCurves x hXred
        c₁ c₂ i₁ i₂ hjs hcr s hs hs0 k (𝟙 _) (E a) (hE_inv a) ?_ ?_
      · exact (isAlgEquivZero_foldr_support c₁ Mdl₁ pt₁ hpt₁ _ a.2.1).of_iso (hE_res a).1.some.symm
      · exact (isAlgEquivZero_foldr_support c₂ Mdl₂ pt₂ hpt₂ _ a.2.2.1).of_iso (hE_res a).2.some.symm
    intro K _ _ σK
    obtain ⟨φK, rfl⟩ := Spec.map_surjective σK
    letI : Algebra k K := φK.hom.toAlgebra
    exact key.baseChange K

  let RLB : ↥(GluingData.admissible S) → RigidifiedLineBundle x ε (𝟙 (Spec (CommRingCat.of k))) :=
    fun a => (RN (a : GluingData k F S).2.2).tensor (RE a)
  have hcut : ∀ a, (algEquivZeroCut x ε).P (𝟙 _) (RLB a) := fun a =>
    (algEquivZeroGroupCut x ε).tensor_mem _ _ _ (hRN_cut _) (hRE_cut a)
  have hRLB_L : ∀ a, (RLB a).L = N (un (a : GluingData k F S).2.2) ⊗ E a := fun a => rfl
  set law := RepresentsRelSubPic.relativeGroupLaw (P := algEquivZeroGroupCut x ε) hD with hlaw
  let φ : ↥(GluingData.admissible S) → SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) D.toBase :=
    fun a => hD.classify (𝟙 _) (RLB a) (hcut a)
  have hφ_spec : ∀ a, Nonempty ((hD.poincare.pullbackAlong (φ a)).L ≅ N (un (a : GluingData k F S).2.2) ⊗ E a) :=
    fun a => hD.classify_spec (𝟙 _) (RLB a) (hcut a)

  have hone : law.one (𝟙 (Spec (CommRingCat.of k))) = ⟨D.zeroSection, D.zeroSection_toBase⟩ :=
    Subtype.ext (RepresentsRelSubPic.relativeGroupLaw_one (P := algEquivZeroGroupCut x ε) hD)
  have htriv : Nonempty ((hD.poincare.pullbackAlong (law.one (𝟙 (Spec (CommRingCat.of k))))).L ≅
      SheafOfModules.unit (pullback x (𝟙 (Spec (CommRingCat.of k)))).ringCatSheaf) := by
    rw [hone]; exact hD.zero
  refine ⟨φ, ?_, ?_, ?_, ?_, ?_, ?_⟩
  ·
    intro a b
    have e1 : Nonempty ((RLB (a + b)).L ≅ ((RLB a).tensor (RLB b)).L) := by
      obtain ⟨eN⟩ := hN_mul (un (a : GluingData k F S).2.2) (un (b : GluingData k F S).2.2)
      obtain ⟨eE⟩ := hE_mul a b
      refine ⟨?_⟩
      change N (un ((a : GluingData k F S) + (b : GluingData k F S)).2.2) ⊗ E (a + b) ≅
        (N (un (a : GluingData k F S).2.2) ⊗ E a) ⊗ (N (un (b : GluingData k F S).2.2) ⊗ E b)
      rw [Prod.snd_add, Prod.snd_add, hun_add]
      exact (eN ⊗ᵢ eE) ≪≫ Scheme.Modules.tensorTensorTensorComm _ _ _ _
    show hD.classify (𝟙 _) (RLB (a + b)) (hcut (a + b)) = law.mul _ (hD.classify (𝟙 _) (RLB a) (hcut a)) (hD.classify (𝟙 _) (RLB b) (hcut b))
    rw [classify_congr hD (𝟙 _) (RLB (a + b)) ((RLB a).tensor (RLB b)) (hcut (a + b))
      ((algEquivZeroGroupCut x ε).tensor_mem _ _ _ (hcut a) (hcut b)) e1]
    exact classify_tensor (P := algEquivZeroGroupCut x ε) hD (𝟙 _) (RLB a) (RLB b) (hcut a) (hcut b)
  ·
    intro a ha
    obtain ⟨g₁, g₂, va, vb, hg₁, hg₂, ha₁, ha₂, hv, hw⟩ := ha

    have hEnu := hE_princ a g₁ g₂ va vb hg₁ hg₂ ha₁ ha₂ hv
    have hu : un (a : GluingData k F S).2.2 =
        (fun σ => Units.map (Scheme.ΓSpecIso (CommRingCat.of k)).inv.hom.toMonoidHom (va σ / vb σ))⁻¹ := by
      funext σ
      simp only [un, hw, Pi.inv_apply, toMul_ofMul, map_inv]
    have hM1 : IsNodeUnitModule x i₁ i₂ p₁ p₂ (𝟙 (Spec (CommRingCat.of k))) 1 (N (un (a : GluingData k F S).2.2) ⊗ E a) := by
      have h := AlgebraicGeometry.TwoGluedCurves.IsNodeUnitModule.tensor k x i₁ i₂ hjs p₁ p₂ hinj hnode hinter hcr
        (hN_inv _) (hN_nu (un (a : GluingData k F S).2.2)) (hE_inv a) hEnu
      have h1u : un (a : GluingData k F S).2.2 *
          (fun σ => Units.map (Scheme.ΓSpecIso (CommRingCat.of k)).inv.hom.toMonoidHom (va σ / vb σ)) = 1 := by
        rw [hu]; exact inv_mul_cancel _
      rwa [h1u] at h
    obtain ⟨eM⟩ := AlgebraicGeometry.TwoGluedCurves.IsNodeUnitModule.nonempty_iso hM1
      (AlgebraicGeometry.TwoGluedCurves.isNodeUnitModule_one_unit k x i₁ i₂ hjs p₁ p₂ hinj hnode hinter hcr (𝟙 _))
    exact hD.ext_of_iso (𝟙 _) (φ a) (law.one _) ⟨(hφ_spec a).some ≪≫ eM ≪≫ htriv.some.symm⟩
  ·
    intro a
    constructor
    ·
      have h1 := RepresentsRelSubPic.postComp_pullbackHom_classify i₁.1 i₁.2 hε hD hD₁ (𝟙 _) (RLB a) (hcut a)
      rw [hν₁]

      obtain ⟨eN⟩ := (hN_res (un (a : GluingData k F S).2.2)).1
      obtain ⟨eE⟩ := (hE_res a).1
      obtain ⟨eR⟩ := AlgebraicGeometry.RelPicard.nonempty_poincare_pullbackAlong_iso_foldr_ofPoint_of_additive_of_pinned c₁ ε₁ D₁ hD₁
        F Mdl₁ e₁ he₁ pt₁ hpt₁ hpt₁' Φ₁ hΦ₁_add hΦ₁ ⟨(a : GluingData k F S).1, a.2.1⟩
      refine h1.trans (hD₁.ext_of_iso (𝟙 _) _ _ ⟨?_⟩)
      refine (hD₁.classify_spec (𝟙 _) _ _).some ≪≫ ?_ ≪≫ eR.symm
      change (Scheme.Modules.pullback (curveChange i₁.1 i₁.2 (𝟙 (Spec (CommRingCat.of k))))).obj (N (un (a : GluingData k F S).2.2) ⊗ E a) ≅ _
      exact Scheme.Modules.pullbackTensorObjIso _ _ _ ≪≫ (eN ⊗ᵢ eE) ≪≫ λ_ _
    ·
      obtain ⟨e2⟩ := hν₂ (𝟙 _) (φ a)
      obtain ⟨eN⟩ := (hN_res (un (a : GluingData k F S).2.2)).2
      obtain ⟨eE⟩ := (hE_res a).2
      obtain ⟨eR⟩ := AlgebraicGeometry.RelPicard.nonempty_poincare_pullbackAlong_iso_foldr_ofPoint_of_additive_of_pinned c₂ ε₂ D₂ hD₂
        F Mdl₂ e₂ he₂ pt₂ hpt₂ hpt₂' Φ₂ hΦ₂_add hΦ₂ ⟨(a : GluingData k F S).2.1, a.2.2.1⟩
      have hinvres : Scheme.Modules.IsInvertible
          ((Scheme.Modules.pullback (curveChange i₂.1 i₂.2 (𝟙 (Spec (CommRingCat.of k))))).obj (hD.poincare.pullbackAlong (φ a)).L) :=
        (hD.poincare.pullbackAlong (φ a)).isInvertible.pullback _
      obtain ⟨erig⟩ := nonempty_rigidify_iso (rigSection c₂ (𝟙 _) ε₂) (pullback.snd c₂ (𝟙 _)) _ hinvres
      refine hD₂.ext_of_iso (𝟙 _) _ _ ⟨?_⟩
      refine e2 ≪≫ erig ≪≫ (Scheme.Modules.pullback _).mapIso (hφ_spec a).some ≪≫ ?_ ≪≫ eR.symm
      exact Scheme.Modules.pullbackTensorObjIso _ _ _ ≪≫ (eN ⊗ᵢ eE) ≪≫ λ_ _
  ·
    intro w
    set a0 : ↥(GluingData.admissible S) := ⟨(0, 0, w), GluingData.zero_zero_mem_admissible S w⟩ with ha0
    obtain ⟨eE⟩ := hE_zero a0 rfl rfl
    have e : N (un w) ≅ (hD.poincare.pullbackAlong (φ a0)).L :=
      (ρ_ _).symm ≪≫ (Iso.refl _ ⊗ᵢ eE.symm) ≪≫ (hφ_spec a0).some.symm
    exact isNodeUnitModule_of_iso e (hN_nu (un w))
  ·
    intro P Q hP hQ a ha1 ha2 ha3
    obtain ⟨eE⟩ := hE_pin₁ P Q hP hQ a ha1 ha2
    obtain ⟨e1⟩ := hN_one
    have hu : un (a : GluingData k F S).2.2 = 1 := by rw [ha3]; exact hun_zero
    refine ⟨(hφ_spec a).some ≪≫ ?_ ≪≫ eE⟩
    rw [hu]
    exact (e1 ⊗ᵢ Iso.refl _) ≪≫ λ_ _
  ·
    intro P Q hP hQ a ha1 ha2 ha3
    obtain ⟨eE⟩ := hE_pin₂ P Q hP hQ a ha1 ha2
    obtain ⟨e1⟩ := hN_one
    have hu : un (a : GluingData k F S).2.2 = 1 := by rw [ha3]; exact hun_zero
    refine ⟨(hφ_spec a).some ≪≫ ?_ ≪≫ eE⟩
    rw [hu]
    exact (e1 ⊗ᵢ Iso.refl _) ≪≫ λ_ _

end S_AlgebraicGeometry_RelPicard_exists_hom_admissible_of_twoGluedSmoothCurves
end P2MW
export P2MW.S_AlgebraicGeometry_RelPicard_exists_hom_admissible_of_twoGluedSmoothCurves (solution)
