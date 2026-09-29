-- Prove2me | solution 1 for AlgebraicGeometry.RelPicard.exists_isOpen_inter_preimage_eq_setOf_isAlgEquivZero_fibre_of_smoothLocus_of_twoLineDegenerations
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:03.589526+00:00
-- url     : https://prove2.me/submissions/5bbe3074-3595-508d-afa0-58a0e5ef3957

import Mathlib
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import Definitions.Def_AlgebraicGeometry_RelPicardAlgEquivZeroCut
import Definitions.Def_AlgebraicGeometry_RelPicardThetaBundle
import Definitions.Def_AlgebraicGeometry_TwoAffineOpenCover
import Definitions.Def_AlgebraicGeometry_TwoChartCechSectionsOf
import Definitions.Def_SheafOfModules_Monoidal
import Definitions.Def_AlgebraicCurve_RelCartier

import Theorems.Thm_AlgebraicGeometry_RelPicard_isClosed_setOf_forall_fibre_le_finrank_H0_of_twoAffineOpenCover
import Theorems.Thm_AlgebraicGeometry_RelPicard_exists_twoAffineOpenCover_fibre_finrank_eq_finrank_cechDiff_baseChange_residueField
import Theorems.Thm_AlgebraicGeometry_Scheme_TwoAffineOpenCover_exists_linearEquiv_sectionsOf_H0
import Theorems.Thm_AlgebraicGeometry_Scheme_TwoAffineOpenCover_exists_isPullback_snd_specMap_algebraOfHom
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_IsInvertible_tensor
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_IsInvertible_dual
import Theorems.Thm_AlgebraicGeometry_RelPicard_isInvertible_sectionIdeal_of_range_subset
import Theorems.Thm_AlgebraicGeometry_Scheme_IdealSheafData_IsInvertible_pow
import Theorems.Thm_AlgebraicGeometry_Scheme_IdealSheafData_IsInvertible_isInvertible_invModule

import Theorems.Thm_AlgebraicGeometry_RelPicard_forall_exists_twoAffineOpenCover_linearEquiv_sectionsOf_fibreModule
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_exists_iso_pullback_of_isPullback
import Theorems.Thm_AlgebraicGeometry_Scheme_TwoAffineOpenCover_exists_linearEquiv_sectionsOf_of_iso
import Theorems.Thm_AlgebraicGeometry_RelPicard_nonempty_pullback_sectionTwist_iso_of_range_subset
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_IsInvertible_pullback_dual
import Definitions.Def_AlgebraicGeometry_ModulesPullbackMonoidal

import Theorems.Thm_AlgebraicGeometry_Scheme_TwoAffineOpenCover_finrank_H0_unit_fibre_eq_one_of_bijective_sections
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_nonempty_pullback_tensor_invModule_pow_tensor_module_iso_of_forall_notMem_support
import Theorems.Thm_AlgebraicCurve_CurveModel_finrank_H1_sectionsOf_unit_eq_zero_and_finrank_H0_eq_one_of_ratFunc
import Theorems.Thm_AlgebraicGeometry_Scheme_IdealSheafData_IsInvertible_isInvertible_module
import Theorems.Thm_AlgebraicGeometry_RelPicard_eulerChar_pullback_firstLine_sectionTwist_tensor_idealModule_eq
import Definitions.Def_AlgebraicGeometry_RelEffCartierDivSum
import Definitions.Def_AlgebraicGeometry_RelEffCartierDivSupportedIn
import Definitions.Def_AlgebraicGeometry_RelEffCartierDivOfPoint
import Definitions.Def_AlgebraicGeometry_RelPicardChartSections
import Definitions.Def_AlgebraicCurve_CurveModel
import Definitions.Def_AlgebraicCurve_RatFuncPlaces
import Definitions.Def_AlgebraicCurve_RatFuncPlaceInfty
import Definitions.Def_AlgebraicGeometry_NeronModelPropertyBundleCarrier
import Definitions.Def_AlgebraicGeometry_RepresentsRelSubPic
import Definitions.Def_AlgebraicGeometry_SmoothProperCurveBase
import Definitions.Def_JacJ1Iface
import Theorems.Thm_AlgebraicGeometry_TwoGluedProjectiveLines_isAlgEquivZero_of_pullback_iso_unit
import Theorems.Thm_AlgebraicGeometry_RelPicard_IsAlgEquivZero_nonempty_pullback_iso_pullback_unit_and_eulerChar_eq_one_of_curveModel_ratFunc
import Theorems.Thm_AlgebraicGeometry_TwoGluedProjectiveLines_nonempty_pullback_iso_unit_of_finrank_H0_twists_lt_two
import Theorems.Thm_AlgebraicGeometry_TwoGluedProjectiveLines_finrank_H0_twists_lt_two_of_nonempty_pullback_iso_unit
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_IsInvertible_eulerChar_sectionsOf_tensor_eq_add_sub
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_IsInvertible_eulerChar_sectionsOf_dual_eq
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_RelPicard_exists_isOpen_inter_preimage_eq_setOf_isAlgEquivZero_fibre_of_smoothLocus_of_twoLineDegenerations
p2m_attr_erase "instance" "AlgebraicGeometry.OModulePresheaf.isScalarTower AlgebraicGeometry.Scheme.OrderedAffineCover.instLinearOrder AlgebraicGeometry.OModulePresheaf.module AlgebraicGeometry.Scheme.OrderedAffineCover.instFintype AlgebraicGeometry.Scheme.OrderedAffineCover.instFintypeIdx AlgebraicGeometry.OModulePresheaf.addCommGroup AlgebraicGeometry.Scheme.OrderedAffineCover.instDecidableEqIdx AlgebraicGeometry.OModulePresheaf.moduleSections AlgebraicGeometry.OModulePresheaf.instSubsingletonObjZero AlgebraicGeometry.OModulePresheaf.Leray.relAltC_scalarTower AlgebraicGeometry.OModulePresheaf.Leray.ker_relAltd_modΓ AlgebraicGeometry.OModulePresheaf.Leray.relAltC_modΓ AlgebraicGeometry.OModulePresheaf.Leray.biC_abGrp AlgebraicGeometry.OModulePresheaf.Leray.relAltH_modΓ AlgebraicGeometry.OModulePresheaf.Leray.ker_relAltd_smul AlgebraicGeometry.OModulePresheaf.Leray.relAltH_scalarTower AlgebraicGeometry.OModulePresheaf.Leray.relAltH_smul AlgebraicGeometry.OModulePresheaf.Leray.biC_module AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instDecidableEqIdx AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instFintype AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instLinearOrder AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instFintypeIdx DoubleComplex.instModuleE₂I DoubleComplex.Bounded.modR DoubleComplex.instModuleE₂II DoubleComplex.instAddCommGroupE₂II DoubleComplex.Bounded.abGrp DoubleComplex.instAddCommGroupE₂I AlgebraicGeometry.ChowDatum.hι_closed AlgebraicGeometry.ChowDatumProj.hιN_closed AlgebraicGeometry.ChowDatumProj.hp_proper AlgebraicGeometry.ChowDatum.hp_isoU AlgebraicGeometry.ChowDatum.hp_proper AlgebraicGeometry.ProjSpace.algebraAway AlgebraicGeometry.ProjSpace.instIsProperProdOverπ AlgebraicGeometry.ChowDatumProj.hp_isoU AlgebraicGeometry.ProjSpace.isProper_π AlgebraicGeometry.ProjSpace.finiteType_mvPolynomial ProjSpaceCech.GradedModule.H.module ProjSpaceCech.GradedModule.H.addCommGroup"
p2m_attr_erase "instance" "ProjSpaceCech.GradedModule.sec.instAdd ProjSpaceCech.GradedModule.sec.instNeg ProjSpaceCech.GradedModule.acg ProjSpaceCech.GradedModule.Frac.setoid ProjSpaceCech.GradedModule.modR ProjSpaceCech.GradedModule.sec.instModule ProjSpaceCech.GradedModule.sec.instAddCommGroup ProjSpaceCech.GradedModule.sec.instZero ProjSpaceCech.GradedModule.Presentation.fJ ProjSpaceCech.GradedModule.sec.instSMul ProjSpaceCech.Twist.H.module ProjSpaceCech.Idx.instFintype ProjSpaceCech.Twist.H.addCommGroup ProjSpaceCech.Idx.instDecidableEq ProjSpaceCech.Twist.Mon.instDecidableEq ProjSpaceCech.Twist.cochain.instAddCommGroup ProjSpaceCech.Twist.cochain.instModule SheafOfModules.isIso_ihomModelToIhom AlgebraicCurve.IsCurveOver.instNontrivialKaehler AlgebraicCurve.IsCurveOver.instFreeKaehler AlgebraicCurve.IsCurveOver.toHasPrincipalDivisors AlgebraicCurve.IsCurveOver.instFiniteResidue AlgebraicCurve.instFundamentalIdentityOfSumRamificationInertia AlgebraicCurve.Place.instIsScalarTowerResidueFieldRestrictPushforward AlgebraicCurve.Place.instAlgebraResidueFieldRestrictPushforward AlgebraicCurve.Place.instIsLocalHomRestrictInclusion AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.SemilinearAut.instDistribMulActionSubtypeProdRingAutMemSubgroupPic0 AlgebraicCurve.SemilinearAut.instDistribMulActionSubtypeProdRingAutMemSubgroupDivisor AlgebraicCurve.Pic0.instModuleZModTorsion AlgebraicCurve.SemilinearAut.instSMulSubtypeProdRingAutMemSubgroupPlace AlgebraicCurve.SemilinearAut.instDistribMulActionTorsion AlgebraicCurve.SemilinearAut.instSMulSubtypeProdRingAutMemSubgroupPic0 AlgebraicCurve.SemilinearAut.instSMulTorsion AlgebraicCurve.SemilinearAut.instMulActionSubtypeProdRingAutMemSubgroupPlace AlgebraicCurve.SemilinearAut.instSMulCommClassZModTorsion"
p2m_attr_erase "instance" "AlgebraicCurve.SemilinearAut.instMulSemiringActionSubtypeProdRingAutMemSubgroup instDecEqAlgebraicClosureRat WeierstrassCurve.Affine.Point.instDistribMulActionAlgEquiv WeierstrassCurve.Affine.Point.instModuleZModTorsionBy WeierstrassCurve.Affine.Point.instSMulTorsionBy WeierstrassCurve.Affine.Point.instDistribMulActionTorsionBy WeierstrassCurve.Affine.Point.instSMulAlgEquiv WeierstrassCurve.Affine.Point.instSMulCommClassAlgEquivZModTorsionBy AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions AlgebraicCurve.instHasLocalResidue_of_hasCanonicalLocalResidueK AlgebraicCurve.instHasCanonicalLocalResidueK_of_hasCanonicalLocalResidueKStar AlgebraicCurve.Place.kw_ffgc_finiteDimensional_adicCompletion instAlgebraSubtypeMemValuationSubring_definitions AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersIntegersCompletion ModularCurve.KwF4gRRTate.instAlgebraKAdicCompletionIntegers AlgebraicCurve.Place.kw_ffgc_continuousSMul_adicCompletionComap AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersCompletionCompletion IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions AlgebraicCurve.instHasCanonicalLocalResidueK AlgebraicCurve.Place.instAlgebra_restrictResidueField AlgebraicCurve.Place.instIsScalarTower_restrictResidueField AlgebraicCurve.instHasLocalResidue AlgebraicCurve.HasSeparableResidue.of_perfectField_of_isCurveOver AlgebraicCurve.HasSeparableResidue.of_perfectField AlgebraicCurve.Place.instIsLocalHom_restrictSubringHom AlgebraicCurve.instHasCanonicalLocalResidueKStar ModularCurve.KwNo6Pin.isLocalRing_completion AlgebraicGeometry.RelEffCartierDiv.isClosedImmersion_subschemeι_resProdMap AlgebraicGeometry.RelEffCartierDiv.isOpenImmersion_resProdMap"
p2m_attr_erase "simp" "AlgebraicGeometry.Scheme.OrderedAffineCover.mk.injEq AlgebraicGeometry.OModulePresheaf.mk.sizeOf_spec AlgebraicGeometry.Scheme.OrderedAffineCover.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.mk.injEq CoherentBaseChange.FibreH0Family.mk.sizeOf_spec CoherentBaseChange.FibreH0Family.mk.injEq AlgebraicGeometry.OModulePresheaf.prod_obj AlgebraicGeometry.OModulePresheaf.restrOpen_obj AlgebraicGeometry.OModulePresheaf.DevissageStep.mk.injEq AlgebraicGeometry.OModulePresheaf.pushforward_obj AlgebraicGeometry.OModulePresheaf.im_obj AlgebraicGeometry.OModulePresheaf.pow_obj AlgebraicGeometry.OModulePresheaf.fstHom_app AlgebraicGeometry.OModulePresheaf.ker_obj AlgebraicGeometry.OModulePresheaf.coker_obj AlgebraicGeometry.OModulePresheaf.DevissageStep.mk.sizeOf_spec AlgebraicGeometry.Scheme.OrderedAffineCover.preimage_U AlgebraicGeometry.OModulePresheaf.sndHom_app AlgebraicGeometry.OModulePresheaf.Hom.mk.injEq AlgebraicGeometry.OModulePresheaf.Hom.id_app AlgebraicGeometry.OModulePresheaf.AffHom.appSections_apply AlgebraicGeometry.OModulePresheaf.AffHom.comp_app AlgebraicGeometry.OModulePresheaf.AffSES.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.AffHom.kerMap_coe AlgebraicGeometry.OModulePresheaf.AffHom.id_app AlgebraicGeometry.OModulePresheaf.Hom.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.Hom.toAffHom_app AlgebraicGeometry.OModulePresheaf.SES.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.AffHom.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.Hom.comp_app AlgebraicGeometry.OModulePresheaf.SES.mk.injEq AlgebraicGeometry.OModulePresheaf.AffHom.mk.injEq AlgebraicGeometry.OModulePresheaf.Hom.appSections_apply AlgebraicGeometry.OModulePresheaf.AffSES.mk.injEq AlgebraicGeometry.OModulePresheaf.Leray.restrictToPreimage_U AlgebraicGeometry.Scheme.OrderedAffineCover.toCoverOf_U AlgebraicGeometry.Scheme.OrderedAffineCoverOf.mk.sizeOf_spec AlgebraicGeometry.Scheme.OrderedAffineCoverOf.mk.injEq AlgebraicGeometry.Scheme.OrderedAffineCover.restrict_U DoubleComplex.Bounded.mk.injEq"
p2m_attr_erase "simp" "DoubleComplex.Bounded.mk.sizeOf_spec DoubleComplex.Convergence.mk.injEq DoubleComplex.Convergence.mk.sizeOf_spec DoubleComplex.SubQuot.mk.sizeOf_spec DoubleComplex.SubQuot.mk.injEq AlgebraicGeometry.ChowDatumProj.mk.sizeOf_spec AlgebraicGeometry.ChowDatum.mk.sizeOf_spec AlgebraicGeometry.ChowDatumProj.mk.injEq AlgebraicGeometry.ChowDatum.mk.injEq ProjSpaceCech.GradedModule.mk.injEq ProjSpaceCech.GradedModule.mk.sizeOf_spec ProjSpaceCech.GradedModule.Frac.mk.sizeOf_spec ProjSpaceCech.GradedModule.Presentation.mk.injEq ProjSpaceCech.GradedModule.Frac.mk.injEq ProjSpaceCech.GradedModule.Presentation.mk.sizeOf_spec ProjSpaceCech.GradedModule.Hom.shift_toLinearMap ProjSpaceCech.GradedModule.Hom.mk.sizeOf_spec ProjSpaceCech.GradedModule.Hom.mk.injEq AlgebraicGeometry.tilde.functorCompPullbackSpecIso_app AlgebraicGeometry.Scheme.Modules.ProjPresentation.mk.injEq AlgebraicGeometry.Scheme.Modules.ProjPresentation.mk.sizeOf_spec PresheafOfModules.InternalHom.IsSheafAux.appAt_toPresheafHom SheafOfModules.ihomSectionsEquivFamily_unit AlgebraicGeometry.Scheme.Modules.restrictHomEquivFamily_apply SheafOfModules.ihomEval_unit_app AlgebraicGeometry.Scheme.Modules.ihomEval_zero_right AlgebraicGeometry.Scheme.Modules.ihomEval_zero_left AlgebraicGeometry.Scheme.Modules.homOfFamily_app_apply SheafOfModules.unit_ihomSectionsEquivFamily AlgebraicGeometry.Scheme.Modules.familyOfHom_app AlgebraicGeometry.Scheme.Modules.restrictUnitIso_hom_app_apply AlgebraicGeometry.Scheme.Modules.restrictUnitIso_inv_app_apply AlgebraicGeometry.Scheme.Modules.restrictHomOfFamily_app_apply AlgebraicGeometry.Scheme.Modules.restrictHomEquivFamily_symm_apply AlgebraicCurve.GluedPic0.toPic0Pair_mk AlgebraicCurve.GluedPic0.toPic0Pair_nodeUnit AlgebraicCurve.coe_cechH0Equiv_apply AlgebraicCurve.cechH1ToH1_mk AlgebraicCurve.lSpaceOn_univ AlgebraicCurve.lSpaceOn_empty"
p2m_attr_erase "simp" "AlgebraicCurve.Divisor.mapRestrict_single AlgebraicCurve.Divisor.pushforward_single AlgebraicCurve.Place.coe_restrictInclusion AlgebraicCurve.Place.mem_fiber AlgebraicCurve.Place.restrict_toValuationSubring AlgebraicCurve.Divisor.degree_pushforward AlgebraicCurve.Place.restrictResidueMap_residue AlgebraicCurve.Pic0.coe_pushforwardDegZeroHom AlgebraicCurve.Pic0.coe_pullbackDegZeroHom AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal AlgebraicCurve.IsFrobeniusEndo.frobNormRingHom_apply ModularCurve.frobeniusPushforwardGeomLevelPic0_mk ModularCurve.coe_frobeniusGeomLevelEquiv_apply ModularCurve.coe_frobeniusPushforwardGeomLevelDegZero ModularCurve.heckeFibreGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusGeomLevel_apply_coe ModularCurve.frobeniusPullbackGeomLevelPic0OfIsCurveOver_mk ModularCurve.coe_heckeFibreGeomLevelDegZero ModularCurve.coe_frobeniusPullbackGeomLevelDegZero ModularCurve.frobeniusPullbackGeomLevelPic0_mk ModularCurve.frobeniusPullbackGeomLevel_single ModularCurve.heckeFibreGeomLevelPic0_mk ModularCurve.frobeniusPushforwardGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusPushforwardGeomLevel_single ModularCurve.qExpandAlgC_apply AlgebraicCurve.Divisor.degree_pushforwardAlong AlgebraicCurve.Pic0.coe_degZeroCorrespondence AlgebraicCurve.Place.mem_fiberAlong AlgebraicCurve.SemilinearAut.toRingAut_inv AlgebraicCurve.SemilinearAut.smul_def AlgebraicCurve.SemilinearAut.smul_single AlgebraicCurve.SemilinearAut.smul_toValuationSubring AlgebraicCurve.SemilinearAut.baseAut_inv AlgebraicCurve.SemilinearAut.baseAut_ofAlgAut AlgebraicCurve.SemilinearAut.toRingAut_ofAlgAut AlgebraicCurve.SemilinearAut.torsionRep_apply"
p2m_attr_erase "simp" "AlgebraicCurve.SemilinearAut.toRingAut_one AlgebraicCurve.SemilinearAut.deg_smul AlgebraicCurve.SemilinearAut.degree_smul AlgebraicCurve.SemilinearAut.coe_degZeroSMulHom AlgebraicCurve.SemilinearAut.baseAut_mul AlgebraicCurve.SemilinearAut.coe_smulValuationSubringEquiv_apply AlgebraicCurve.SemilinearAut.baseAut_one AlgebraicCurve.SemilinearAut.ofAlgAut_smul AlgebraicCurve.SemilinearAut.coe_torsion_smul AlgebraicCurve.SemilinearAut.toRingAut_mul AlgebraicCurve.coe_frobeniusPushforwardDegZero AlgebraicCurve.IsFrobeniusEndo.coe_frobeniusPullbackDegZero ModularCurve.jqNModC_one ModularCurve.qExpand_coeff_mul ModularCurve.qExpandₐ_apply ModularCurve.jqN_one ModularCurve.qExpand_single ModularCurve.dedekindPsi_one ModularCurve.ModularPolynomialData.mk.sizeOf_spec ModularCurve.evalAtJ_X ModularCurve.ModularPolynomialData.mk.injEq ModularCurve.constantCoeff_jNum ModularCurve.constantCoeff_eisenstein4 ModularCurve.qExpand_C ModularCurve.coeff_jq_neg_one ModularCurve.constantCoeff_jNumQ ModularCurve.reduceModBivar_C_X ModularCurve.laurentMap_coeff ModularCurve.reduceModBivar_X ModularCurve.laurentMap_single ModularCurve.evalAtJInt_X ModularCurve.evalAtJMod_X ModularCurve.jqNMod_one ModularCurve.aeval_heckeGen ModularCurve.coe_mTorsionGaloisRep_apply ModularCurve.eisensteinSystem_of_dvd ModularCurve.eisensteinSystem_of_not_dvd FreyPackage.mk.sizeOf_spec FreyPackage.mk.injEq WeierstrassCurve.Affine.Point.galoisRepModuleEnd_apply"
p2m_attr_erase "simp" "AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none AlgebraicCurve.Divisor.evalFun_zero AlgebraicCurve.Place.evalAt_one AlgebraicCurve.Place.differentialCoeff_zero AlgebraicCurve.Place.differentialCoeff_dCoord AlgebraicCurve.TranscendenceTower.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.injEq AlgebraicCurve.TranscendenceTower.mk.injEq AlgebraicCurve.PoleDivisorPackage.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.sizeOf_spec AlgebraicCurve.PoleDivisorPackage.mk.injEq AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.sizeOf_spec AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.injEq AlgebraicCurve.adeleSingle_coe AlgebraicCurve.kaehlerResidueTermKFam_apply AlgebraicCurve.Place.LocalResidueData.mk.injEq AlgebraicCurve.Place.LocalResidueData.mk.sizeOf_spec AlgebraicCurve.Place.kw_ffgc_adicCompletionComapIntegers_coe AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.sizeOf_spec AlgebraicCurve.Place.mem_simplePoleSubmodule AlgebraicCurve.Place.coe_uniformizerSubring ModularCurve.Lg37.Lg37CompletionSection.mk.injEq AlgebraicCurve.Place.CoefficientFieldSection.mk.injEq AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.injEq ModularCurve.Lg37.Lg37CompletionSection.mk.sizeOf_spec AlgebraicCurve.Place.CoefficientFieldSection.mk.sizeOf_spec AlgebraicCurve.Place.poleSubmodule_one AlgebraicCurve.Place.mem_poleSubmodule AlgebraicGeometry.RelPicard.fst_toProdSpec AlgebraicGeometry.RelPicard.toProdSpec_fst_assoc AlgebraicGeometry.RelPicard.pointsSubBasepointModule_cons AlgebraicGeometry.RelPicard.pointsSubBasepointModule_nil AlgebraicGeometry.RelPicard.fst_toProdSpec_assoc AlgebraicGeometry.RelPicard.toProdSpec_fst AlgebraicGeometry.RelEffCartierDiv.restrictAlong_extendAlong AlgebraicGeometry.RelEffCartierDiv.extendAlong_I AlgebraicGeometry.RelEffCartierDiv.resProdMap_snd"
p2m_attr_erase "simp" "AlgebraicGeometry.RelEffCartierDiv.restrictAlong_I AlgebraicGeometry.RelEffCartierDiv.extendAlong_restrictAlong AlgebraicGeometry.RelEffCartierDiv.resProdMap_fst_assoc AlgebraicGeometry.RelEffCartierDiv.resProdMap_snd_assoc AlgebraicGeometry.RelEffCartierDiv.resProdMap_fst TwoChartCech.Mumford.dK_apply TwoChartCech.Mumford.ι0_apply TwoChartCech.Mumford.ι1_apply TwoChartCech.KerCoprod.dK_apply TwoChartCech.KerCoprod.ι1_apply TwoChartCech.KerCoprod.ι0_apply AlgebraicGeometry.RelPicard.algEquivZeroGroupCut_toSubPicCondition AlgebraicGeometry.RelPicard.SubPicGroupCondition.mk.injEq AlgebraicGeometry.RelPicard.SubPicGroupCondition.mk.sizeOf_spec AlgebraicGeometry.RelPicard.SubPicCondition.onClasses_mk AlgebraicGeometry.RelPicard.relSubPicPresheaf_map_coe GoodReductionJacobian.relativeGroupLawOfGrpObj_inv GoodReductionJacobian.relativeGroupLawOfGrpObj_mul GoodReductionJacobian.overHomEquivSchemeHomOver_apply_coe GoodReductionJacobian.relativeGroupLawOfGrpObj_one GoodReductionJacobian.overHomEquivSchemeHomOver_symm_apply_left"

set_option autoImplicit false

universe u

p2m_open "CategoryTheory CategoryTheory.Limits Opposite CategoryTheory.MonoidalCategory AlgebraicGeometry P2MW.S_AlgebraicGeometry_RelPicard_exists_isOpen_inter_preimage_eq_setOf_isAlgEquivZero_fibre_of_smoothLocus_of_twoLineDegenerations.AlgebraicGeometry AlgebraicGeometry.RelPicard P2MW.S_AlgebraicGeometry_RelPicard_exists_isOpen_inter_preimage_eq_setOf_isAlgEquivZero_fibre_of_smoothLocus_of_twoLineDegenerations.AlgebraicGeometry.RelPicard NeronModelInfra AlgebraicCurve~genus TensorProduct"

noncomputable section

namespace AlgebraicGeometry
p2m_export "AlgebraicGeometry" "SmoothOfRelativeDimension IsProper Scheme.Modules.pullback Scheme.Hom Scheme.Hom.preimage_inf Scheme.Hom.support_ker LocallyOfFiniteType Spec Scheme.IdealSheafData.range_subschemeι Spec.map Scheme Smooth IsOpenImmersion Scheme.IdealSheafData.support_top Flat IsClosedImmersion IsReduced IsSeparated Scheme.Modules.pullbackCongr Scheme.fromSpecResidueField_apply Scheme.Modules.pullbackId Scheme.Hom.preimage_sup Scheme.Modules IsAffineHom Scheme.Hom.comp_apply Scheme.IdealSheafData Scheme.Modules.pullbackComp Scheme.Modules.IsInvertible Scheme.Modules.isInvertible_unit RelPicard.IsAlgEquivZero Scheme.Modules.dual Scheme.IdealSheafData.module RelEffCartierDiv Scheme.TwoAffineOpenCover Scheme.TwoAffineOpenCover.specMap Scheme.TwoAffineOpenCover.algebraOfHom Scheme.TwoAffineOpenCover.moduleSectionsOfHom Scheme.IdealSheafData.isInvertible_top Scheme.TwoAffineOpenCover.exists_linearEquiv_sectionsOf_H0 Scheme.TwoAffineOpenCover.exists_isPullback_snd_specMap_algebraOfHom Scheme.Modules.exists_iso_pullback_of_isPullback Scheme.TwoAffineOpenCover.exists_linearEquiv_sectionsOf_of_iso Scheme.Modules.pullbackTensorObjIso Scheme.Modules.pullbackTensorUnitObjIso Scheme.TwoAffineOpenCover.finrank_H0_unit_fibre_eq_one_of_bijective_sections Scheme.Modules.nonempty_pullback_tensor_invModule_pow_tensor_module_iso_of_forall_notMem_support RelEffCartierDiv.empty RelEffCartierDiv.empty_I RelEffCartierDiv.I_eq_top_of_degree_zero graphOver TwoGluedProjectiveLines.isAlgEquivZero_of_pullback_iso_unit RelPicard.IsAlgEquivZero.nonempty_pullback_iso_pullback_unit_and_eulerChar_eq_one_of_curveModel_ratFunc TwoGluedProjectiveLines.nonempty_pullback_iso_unit_of_finrank_H0_twists_lt_two TwoGluedProjectiveLines.finrank_H0_twists_lt_two_of_nonempty_pullback_iso_unit Scheme.Modules.IsInvertible.eulerChar_sectionsOf_tensor_eq_add_sub Scheme.Modules.IsInvertible.eulerChar_sectionsOf_dual_eq Scheme.TwoAffineOpenCover.ext' Scheme.TwoAffineOpenCover.comapOfIsAffineHom'"
namespace RelPicard
p2m_export "AlgebraicGeometry.RelPicard" "baseChangeSnd rigSection RigidifiedLineBundle fibreAt IsAlgEquivZero sectionIdeal sectionTwist fibreModule isClosed_setOf_forall_fibre_le_finrank_H0_of_twoAffineOpenCover exists_twoAffineOpenCover_fibre_finrank_eq_finrank_cechDiff_baseChange_residueField isInvertible_sectionIdeal_of_range_subset forall_exists_twoAffineOpenCover_linearEquiv_sectionsOf_fibreModule nonempty_pullback_sectionTwist_iso_of_range_subset eulerChar_pullback_firstLine_sectionTwist_tensor_idealModule_eq sectionFibrePoint IsAlgEquivZero.nonempty_pullback_iso_pullback_unit_and_eulerChar_eq_one_of_curveModel_ratFunc"
namespace HCutDR
p2m_open "AlgebraicGeometry.RelPicard AlgebraicGeometry"

theorem eq_closedPoint {k : Type u} [Field k] (y : ↥(Spec (CommRingCat.of k))) : y = IsLocalRing.closedPoint k := by
  apply PrimeSpectrum.ext
  have h1 : (y : PrimeSpectrum k).asIdeal = ⊥ := Ideal.eq_bot_of_prime _
  have h2 : (IsLocalRing.closedPoint k).asIdeal = ⊥ := by
    change IsLocalRing.maximalIdeal _ = ⊥
    exact IsLocalRing.maximalIdeal_eq_bot
  rw [h1, h2]

theorem range_subset_singleton_iff {k : Type u} [Field k] {T : Scheme.{u}} (s : Spec (CommRingCat.of k) ⟶ T) (x : T) :
    Set.range ⇑s ⊆ {x} ↔ s.base (IsLocalRing.closedPoint k) = x := by
  constructor
  · intro h
    exact h ⟨IsLocalRing.closedPoint k, rfl⟩
  · rintro h _ ⟨y, rfl⟩
    rw [eq_closedPoint y]
    exact h

theorem exists_geometricPoint (T : Scheme.{u}) (x : T) :
    ∃ (k : Type u) (_ : Field k) (_ : IsAlgClosed k) (s : Spec (CommRingCat.of k) ⟶ T),
      s.base (IsLocalRing.closedPoint k) = x := by
  refine ⟨AlgebraicClosure (T.residueField x), inferInstance, inferInstance,
    Spec.map (CommRingCat.ofHom (algebraMap (T.residueField x) (AlgebraicClosure (T.residueField x)))) ≫
      T.fromSpecResidueField x, ?_⟩
  exact Scheme.fromSpecResidueField_apply x _

theorem finrank_H0_sectionsOf_eq {k : Type u} [Field k] {X : Scheme.{u}} (x : X ⟶ Spec (CommRingCat.of k))
    (M : X.Modules) (𝒲 𝒲' : X.TwoAffineOpenCover) :
    Module.finrank k (𝒲.sectionsOf x M).H0 = Module.finrank k (𝒲'.sectionsOf x M).H0 := by
  letI := Scheme.TwoAffineOpenCover.moduleSectionsOfHom x M ⊤
  obtain ⟨e, -⟩ := Scheme.TwoAffineOpenCover.exists_linearEquiv_sectionsOf_H0 𝒲 x M
  obtain ⟨e', -⟩ := Scheme.TwoAffineOpenCover.exists_linearEquiv_sectionsOf_H0 𝒲' x M
  exact (e.symm.trans e').finrank_eq

variable {R : Type u} [CommRing R] {C : Scheme.{u}} (c : C ⟶ Spec (CommRingCat.of R))
  {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R))

theorem finrank_H0_fibre_eq_of_base_eq (𝒱 : C.TwoAffineOpenCover) (M : (pullback c t).Modules) (hM : Scheme.Modules.IsInvertible M)
    {k : Type u} [Field k] (s : Spec (CommRingCat.of k) ⟶ T)
    {k' : Type u} [Field k'] (s' : Spec (CommRingCat.of k') ⟶ T)
    (h : s.base (IsLocalRing.closedPoint k) = s'.base (IsLocalRing.closedPoint k'))
    (𝒲 : (pullback (pullback.snd c t) s).TwoAffineOpenCover) (𝒲' : (pullback (pullback.snd c t) s').TwoAffineOpenCover) :
    Module.finrank k (𝒲.sectionsOf (fibreAt c t s) (fibreModule c t s M)).H0 =
      Module.finrank k' (𝒲'.sectionsOf (fibreAt c t s') (fibreModule c t s' M)).H0 := by
  classical
  set x := s.base (IsLocalRing.closedPoint k) with hx
  obtain ⟨W, hW, hxW, -⟩ := TopologicalSpace.Opens.isBasis_iff_nbhd.mp T.isBasis_affineOpens
    (show x ∈ (⊤ : T.Opens) from trivial)
  letI := Scheme.TwoAffineOpenCover.algebraOfHom t W
  obtain ⟨g', hcart, -⟩ := Scheme.TwoAffineOpenCover.exists_isPullback_snd_specMap_algebraOfHom c t W hW
  haveI : IsOpenImmersion hW.fromSpec := hW.isOpenImmersion_fromSpec
  have hxr : x ∈ Set.range hW.fromSpec.base := by rw [hW.range_fromSpec]; exact hxW
  obtain ⟨𝔭, h𝔭⟩ := hxr
  obtain ⟨𝒲₀, h𝒲₀⟩ := exists_twoAffineOpenCover_fibre_finrank_eq_finrank_cechDiff_baseChange_residueField
    c t hW.fromSpec (pullback.snd c (Scheme.TwoAffineOpenCover.specMap R Γ(T, W))) g' hcart (𝒱.pullback c Γ(T, W)) 𝔭
    s h𝔭.symm
  obtain ⟨𝒲₀', h𝒲₀'⟩ := exists_twoAffineOpenCover_fibre_finrank_eq_finrank_cechDiff_baseChange_residueField
    c t hW.fromSpec (pullback.snd c (Scheme.TwoAffineOpenCover.specMap R Γ(T, W))) g' hcart (𝒱.pullback c Γ(T, W)) 𝔭
    s' (h ▸ h𝔭).symm
  rw [finrank_H0_sectionsOf_eq (fibreAt c t s) (fibreModule c t s M) 𝒲 𝒲₀, (h𝒲₀ M hM).1,
    finrank_H0_sectionsOf_eq (fibreAt c t s') (fibreModule c t s' M) 𝒲' 𝒲₀', (h𝒲₀' M hM).1]

theorem nonempty_twoAffineOpenCover_fibre (𝒱 : C.TwoAffineOpenCover) {k : Type u} [Field k] (s : Spec (CommRingCat.of k) ⟶ T) :
    Nonempty (pullback (pullback.snd c t) s).TwoAffineOpenCover := by
  classical
  set x := s.base (IsLocalRing.closedPoint k) with hx
  obtain ⟨W, hW, hxW, -⟩ := TopologicalSpace.Opens.isBasis_iff_nbhd.mp T.isBasis_affineOpens
    (show x ∈ (⊤ : T.Opens) from trivial)
  letI := Scheme.TwoAffineOpenCover.algebraOfHom t W
  obtain ⟨g', hcart, -⟩ := Scheme.TwoAffineOpenCover.exists_isPullback_snd_specMap_algebraOfHom c t W hW
  haveI : IsOpenImmersion hW.fromSpec := hW.isOpenImmersion_fromSpec
  have hxr : x ∈ Set.range hW.fromSpec.base := by rw [hW.range_fromSpec]; exact hxW
  obtain ⟨𝔭, h𝔭⟩ := hxr
  obtain ⟨𝒲₀, -⟩ := exists_twoAffineOpenCover_fibre_finrank_eq_finrank_cechDiff_baseChange_residueField
    c t hW.fromSpec (pullback.snd c (Scheme.TwoAffineOpenCover.specMap R Γ(T, W))) g' hcart (𝒱.pullback c Γ(T, W)) 𝔭
    s h𝔭.symm
  exact ⟨𝒲₀⟩

theorem exists_isOpen_inter_eq_of_fibrewise_finrank_H0_lt
    [IsNoetherianRing R] [IsProper c] [Flat c] (𝒱 : C.TwoAffineOpenCover) [LocallyOfFiniteType t]
    (Z : Set T) {ι : Type} [Finite ι]
    (M : ι → (pullback c t).Modules) (hM : ∀ i, Scheme.Modules.IsInvertible (M i)) (N : ι → ℕ)
    (P : ∀ (k : Type u) [Field k] [IsAlgClosed k], (Spec (CommRingCat.of k) ⟶ T) → Prop)
    (hA₁ : ∀ (k : Type u) [Field k] [IsAlgClosed k] (s : Spec (CommRingCat.of k) ⟶ T),
      s.base (IsLocalRing.closedPoint k) ∈ Z → P k s →
        ∃ 𝒲 : (pullback (pullback.snd c t) s).TwoAffineOpenCover,
          ∀ i, Module.finrank k (𝒲.sectionsOf (fibreAt c t s) (fibreModule c t s (M i))).H0 < N i)
    (hA₂ : ∀ (k : Type u) [Field k] [IsAlgClosed k] (s : Spec (CommRingCat.of k) ⟶ T),
      s.base (IsLocalRing.closedPoint k) ∈ Z →
        (∀ (𝒲 : (pullback (pullback.snd c t) s).TwoAffineOpenCover) (i : ι),
          Module.finrank k (𝒲.sectionsOf (fibreAt c t s) (fibreModule c t s (M i))).H0 < N i) → P k s) :
    ∃ W : Set T, IsOpen W ∧
      W ∩ Z = {x : T | x ∈ Z ∧ ∀ (k : Type u) [Field k] [IsAlgClosed k] (s : Spec (CommRingCat.of k) ⟶ T),
        Set.range ⇑s ⊆ {x} → P k s} := by
  classical
  let Zc : ι → Set T := fun i => {x : T | ∀ (k : Type u) [Field k] (s : Spec (CommRingCat.of k) ⟶ T),
      s.base (IsLocalRing.closedPoint k) = x →
        ∀ 𝒲 : (pullback (pullback.snd c t) s).TwoAffineOpenCover,
          N i ≤ Module.finrank k (𝒲.sectionsOf (fibreAt c t s) (fibreModule c t s (M i))).H0}
  have hZc : ∀ i, IsClosed (Zc i) := fun i =>
    isClosed_setOf_forall_fibre_le_finrank_H0_of_twoAffineOpenCover R c 𝒱 t (M i) (hM i) (N i)
  refine ⟨⋂ i, (Zc i)ᶜ, isOpen_iInter_of_finite (fun i => (hZc i).isOpen_compl), ?_⟩
  ext x
  simp only [Set.mem_inter_iff, Set.mem_iInter, Set.mem_compl_iff, Set.mem_setOf_eq]
  constructor
  · rintro ⟨hW, hxZ⟩
    refine ⟨hxZ, fun k _ _ s hs => ?_⟩
    have hsx : s.base (IsLocalRing.closedPoint k) = x := (range_subset_singleton_iff s x).mp hs
    refine hA₂ k s (by rw [hsx]; exact hxZ) (fun 𝒲 i => ?_)
    have hi := hW i
    simp only [Zc, Set.mem_setOf_eq, not_forall, not_le] at hi
    obtain ⟨k₁, _, s₁, hs₁, 𝒲₁, hlt⟩ := hi
    rw [finrank_H0_fibre_eq_of_base_eq c t 𝒱 (M i) (hM i) s s₁ (hsx.trans hs₁.symm) 𝒲 𝒲₁]
    exact hlt
  · rintro ⟨hxZ, hP⟩
    refine ⟨fun i hi => ?_, hxZ⟩
    obtain ⟨k, _, _, s, hs⟩ := exists_geometricPoint T x
    obtain ⟨𝒲, h𝒲⟩ := hA₁ k s (by rw [hs]; exact hxZ) (hP k s ((range_subset_singleton_iff s x).mpr hs))
    exact absurd (h𝒲 i) (not_lt.mpr (hi k s hs 𝒲))

variable (ε : SchemeHomOver (𝟙 (Spec (CommRingCat.of R))) c)

theorem isInvertible_sectionTwist [IsSeparated c] (U : C.Opens) [SmoothOfRelativeDimension 1 (U.ι ≫ c)]
    (hε : Set.range ε.1.base ⊆ (U : Set C)) (r : ℕ) : Scheme.Modules.IsInvertible (sectionTwist c ε t r) :=
  ((isInvertible_sectionIdeal_of_range_subset c ε U hε t).pow r).isInvertible_invModule

abbrev Mplus (L : RigidifiedLineBundle c ε t) (d : ℕ) : (pullback c t).Modules := (L.L ⊗ L.L) ⊗ sectionTwist c ε t d

abbrev Mminus (L : RigidifiedLineBundle c ε t) (d : ℕ) : (pullback c t).Modules :=
  (Scheme.Modules.dual L.L ⊗ Scheme.Modules.dual L.L) ⊗ sectionTwist c ε t d

theorem isInvertible_Mplus [IsSeparated c] (U : C.Opens) [SmoothOfRelativeDimension 1 (U.ι ≫ c)]
    (hε : Set.range ε.1.base ⊆ (U : Set C)) (L : RigidifiedLineBundle c ε t) (d : ℕ) :
    Scheme.Modules.IsInvertible (Mplus c t ε L d) :=
  (L.isInvertible.tensor L.isInvertible).tensor (isInvertible_sectionTwist c t ε U hε d)

theorem isInvertible_Mminus [IsSeparated c] (U : C.Opens) [SmoothOfRelativeDimension 1 (U.ι ≫ c)]
    (hε : Set.range ε.1.base ⊆ (U : Set C)) (L : RigidifiedLineBundle c ε t) (d : ℕ) :
    Scheme.Modules.IsInvertible (Mminus c t ε L d) :=
  (L.isInvertible.dual.1.tensor L.isInvertible.dual.1).tensor (isInvertible_sectionTwist c t ε U hε d)

theorem exists_isOpen_inter_preimage_eq_setOf_isAlgEquivZero_of_handA
    [IsNoetherianRing R] [IsProper c] [Flat c] (𝒱 : C.TwoAffineOpenCover)
    (U : C.Opens) [SmoothOfRelativeDimension 1 (U.ι ≫ c)] (hε : Set.range ε.1.base ⊆ (U : Set C))
    [LocallyOfFiniteType t] (L : RigidifiedLineBundle c ε t) (Z₀ : Set ↥(Spec (CommRingCat.of R))) (d N : ℕ)
    (hA₁ : ∀ (k : Type u) [Field k] [IsAlgClosed k] (s : Spec (CommRingCat.of k) ⟶ T),
      t (s.base (IsLocalRing.closedPoint k)) ∈ Z₀ → IsAlgEquivZero (fibreAt c t s) (fibreModule c t s L.L) →
        ∃ 𝒲 : (pullback (pullback.snd c t) s).TwoAffineOpenCover,
          Module.finrank k (𝒲.sectionsOf (fibreAt c t s) (fibreModule c t s (Mplus c t ε L d))).H0 < N ∧
          Module.finrank k (𝒲.sectionsOf (fibreAt c t s) (fibreModule c t s (Mminus c t ε L d))).H0 < N)
    (hA₂ : ∀ (k : Type u) [Field k] [IsAlgClosed k] (s : Spec (CommRingCat.of k) ⟶ T),
      t (s.base (IsLocalRing.closedPoint k)) ∈ Z₀ →
        (∀ 𝒲 : (pullback (pullback.snd c t) s).TwoAffineOpenCover,
          Module.finrank k (𝒲.sectionsOf (fibreAt c t s) (fibreModule c t s (Mplus c t ε L d))).H0 < N ∧
          Module.finrank k (𝒲.sectionsOf (fibreAt c t s) (fibreModule c t s (Mminus c t ε L d))).H0 < N) →
        IsAlgEquivZero (fibreAt c t s) (fibreModule c t s L.L)) :
    ∃ W : Set ↥T, IsOpen W ∧
      W ∩ (⇑t) ⁻¹' Z₀ = {x : ↥T | t x ∈ Z₀ ∧ ∀ (k : Type u) [Field k] [IsAlgClosed k] (s : Spec (CommRingCat.of k) ⟶ T),
        Set.range ⇑s ⊆ {x} → IsAlgEquivZero (fibreAt c t s) (fibreModule c t s L.L)} := by
  refine exists_isOpen_inter_eq_of_fibrewise_finrank_H0_lt c t 𝒱 ((⇑t) ⁻¹' Z₀)
    (![Mplus c t ε L d, Mminus c t ε L d]) ?_ (fun _ => N)
    (fun k _ _ s => IsAlgEquivZero (fibreAt c t s) (fibreModule c t s L.L)) ?_ ?_
  · intro i
    fin_cases i
    · exact isInvertible_Mplus c t ε U hε L d
    · exact isInvertible_Mminus c t ε U hε L d
  · intro k _ _ s hs hP
    obtain ⟨𝒲, h₁, h₂⟩ := hA₁ k s hs hP
    refine ⟨𝒲, fun i => ?_⟩
    fin_cases i
    · exact h₁
    · exact h₂
  · intro k _ _ s hs h𝒲
    exact hA₂ k s hs (fun 𝒲 => ⟨h𝒲 𝒲 0, h𝒲 𝒲 1⟩)

theorem finrank_H0_sectionsOf_eq_of_iso {k : Type u} [Field k] {X : Scheme.{u}} (x : X ⟶ Spec (CommRingCat.of k))
    {M M' : X.Modules} (e : M ≅ M') (𝒱 : X.TwoAffineOpenCover) :
    Module.finrank k (𝒱.sectionsOf x M).H0 = Module.finrank k (𝒱.sectionsOf x M').H0 := by
  obtain ⟨𝒱₁, -, -, ⟨e0⟩, -⟩ := Scheme.TwoAffineOpenCover.exists_linearEquiv_sectionsOf_of_iso x x (Iso.refl X)
    (Category.id_comp x) 𝒱 M' M (e ≪≫ ((Scheme.Modules.pullbackId X).app M').symm)
  rw [finrank_H0_sectionsOf_eq x M 𝒱 𝒱₁]
  exact e0.finrank_eq

section BaseChange

variable {k : Type u} [Field k] (s : Spec (CommRingCat.of k) ⟶ T)

abbrev pointOver : SchemeHomOver (s ≫ t) t := ⟨s, rfl⟩

theorem finrank_H0_fibreModule_eq_finrank_H0_baseChangeSnd (M : (pullback c t).Modules)
    (𝒱 : (pullback c (s ≫ t)).TwoAffineOpenCover) (𝒲 : (pullback (pullback.snd c t) s).TwoAffineOpenCover) :
    Module.finrank k (𝒲.sectionsOf (fibreAt c t s) (fibreModule c t s M)).H0 =
      Module.finrank k (𝒱.sectionsOf (pullback.snd c (s ≫ t))
        ((Scheme.Modules.pullback (baseChangeSnd c (pointOver t s))).obj M)).H0 := by
  obtain ⟨𝒲₁, ⟨e0⟩, -⟩ :=
    (forall_exists_twoAffineOpenCover_linearEquiv_sectionsOf_fibreModule c t s (s ≫ t) rfl M).1 𝒱
  rw [finrank_H0_sectionsOf_eq (fibreAt c t s) (fibreModule c t s M) 𝒲 𝒲₁]
  exact e0.finrank_eq

theorem isAlgEquivZero_fibreModule_iff (M : (pullback c t).Modules) :
    IsAlgEquivZero (fibreAt c t s) (fibreModule c t s M) ↔
      IsAlgEquivZero (pullback.snd c (s ≫ t)) ((Scheme.Modules.pullback (baseChangeSnd c (pointOver t s))).obj M) := by
  obtain ⟨φ, h1, h2, -⟩ := Scheme.Modules.exists_iso_pullback_of_isPullback c (pullback.snd c t) (pullback.fst c t) t
    (IsPullback.of_hasPullback c t) s

  have hbc1 : baseChangeSnd c (pointOver t s) ≫ pullback.fst c t = pullback.fst c (s ≫ t) ≫ 𝟙 C :=
    pullback.lift_fst _ _ _
  have hbc2 : baseChangeSnd c (pointOver t s) ≫ pullback.snd c t = pullback.snd c (s ≫ t) ≫ s :=
    pullback.lift_snd _ _ _
  have key : φ.hom ≫ pullback.fst (pullback.snd c t) s = baseChangeSnd c (pointOver t s) := by
    apply pullback.hom_ext
    · rw [Category.assoc, h2, hbc1, Category.comp_id]
    · rw [Category.assoc, pullback.condition, ← Category.assoc, h1, hbc2]
  have h1' : φ.inv ≫ pullback.snd c (s ≫ t) = fibreAt c t s := by
    rw [← h1, Iso.inv_hom_id_assoc]; rfl
  constructor
  · intro h
    have h' := h.pullback φ.hom (a' := pullback.snd c (s ≫ t)) h1
    refine h'.of_iso ?_
    exact (Scheme.Modules.pullbackComp _ _).app M ≪≫ (Scheme.Modules.pullbackCongr key).app M
  · intro h
    have h' := h.pullback φ.inv (a' := fibreAt c t s) h1'
    refine h'.of_iso ?_
    have key' : φ.inv ≫ baseChangeSnd c (pointOver t s) = pullback.fst (pullback.snd c t) s := by
      rw [← key, Iso.inv_hom_id_assoc]
    exact (Scheme.Modules.pullbackComp _ _).app M ≪≫ (Scheme.Modules.pullbackCongr key').app M

theorem nonempty_pullback_Mplus_iso [IsSeparated c] (U : C.Opens) [SmoothOfRelativeDimension 1 (U.ι ≫ c)]
    (hε : Set.range ε.1.base ⊆ (U : Set C)) (L : RigidifiedLineBundle c ε t) (d : ℕ) :
    Nonempty ((Scheme.Modules.pullback (baseChangeSnd c (pointOver t s))).obj (Mplus c t ε L d) ≅
      Mplus c (s ≫ t) ε (L.pullbackAlong (pointOver t s)) d) := by
  obtain ⟨eT⟩ := nonempty_pullback_sectionTwist_iso_of_range_subset R c ε U hε (pointOver t s) d
  exact ⟨Scheme.Modules.pullbackTensorObjIso _ _ _ ≪≫
    tensorIso (Scheme.Modules.pullbackTensorObjIso _ _ _) eT⟩

theorem nonempty_pullback_Mminus_iso [IsSeparated c] (U : C.Opens) [SmoothOfRelativeDimension 1 (U.ι ≫ c)]
    (hε : Set.range ε.1.base ⊆ (U : Set C)) (L : RigidifiedLineBundle c ε t) (d : ℕ) :
    Nonempty ((Scheme.Modules.pullback (baseChangeSnd c (pointOver t s))).obj (Mminus c t ε L d) ≅
      Mminus c (s ≫ t) ε (L.pullbackAlong (pointOver t s)) d) := by
  obtain ⟨eT⟩ := nonempty_pullback_sectionTwist_iso_of_range_subset R c ε U hε (pointOver t s) d
  obtain ⟨eD⟩ := L.isInvertible.pullback_dual (baseChangeSnd c (pointOver t s))
  exact ⟨Scheme.Modules.pullbackTensorObjIso _ _ _ ≪≫
    tensorIso (Scheme.Modules.pullbackTensorObjIso _ _ _ ≪≫ tensorIso eD eD) eT⟩

end BaseChange

theorem exists_isOpen_inter_preimage_eq_setOf_isAlgEquivZero_of_handA_baseChange
    [IsNoetherianRing R] [IsProper c] [Flat c] (𝒱 : C.TwoAffineOpenCover)
    (U : C.Opens) [SmoothOfRelativeDimension 1 (U.ι ≫ c)] (hε : Set.range ε.1.base ⊆ (U : Set C))
    [LocallyOfFiniteType t] (L : RigidifiedLineBundle c ε t) (Z₀ : Set ↥(Spec (CommRingCat.of R))) (d N : ℕ)
    (hA₁ : ∀ (k : Type u) [Field k] [IsAlgClosed k] (x : Spec (CommRingCat.of k) ⟶ Spec (CommRingCat.of R)),
      x.base (IsLocalRing.closedPoint k) ∈ Z₀ → ∀ (L' : RigidifiedLineBundle c ε x),
        IsAlgEquivZero (pullback.snd c x) L'.L →
        ∃ 𝒲 : (pullback c x).TwoAffineOpenCover,
          Module.finrank k (𝒲.sectionsOf (pullback.snd c x) (Mplus c x ε L' d)).H0 < N ∧
          Module.finrank k (𝒲.sectionsOf (pullback.snd c x) (Mminus c x ε L' d)).H0 < N)
    (hA₂ : ∀ (k : Type u) [Field k] [IsAlgClosed k] (x : Spec (CommRingCat.of k) ⟶ Spec (CommRingCat.of R)),
      x.base (IsLocalRing.closedPoint k) ∈ Z₀ → ∀ (L' : RigidifiedLineBundle c ε x),
        (∀ 𝒲 : (pullback c x).TwoAffineOpenCover,
          Module.finrank k (𝒲.sectionsOf (pullback.snd c x) (Mplus c x ε L' d)).H0 < N ∧
          Module.finrank k (𝒲.sectionsOf (pullback.snd c x) (Mminus c x ε L' d)).H0 < N) →
        IsAlgEquivZero (pullback.snd c x) L'.L) :
    ∃ W : Set ↥T, IsOpen W ∧
      W ∩ (⇑t) ⁻¹' Z₀ = {x : ↥T | t x ∈ Z₀ ∧ ∀ (k : Type u) [Field k] [IsAlgClosed k] (s : Spec (CommRingCat.of k) ⟶ T),
        Set.range ⇑s ⊆ {x} → IsAlgEquivZero (fibreAt c t s) (fibreModule c t s L.L)} := by
  haveI : IsSeparated c := inferInstance
  refine exists_isOpen_inter_preimage_eq_setOf_isAlgEquivZero_of_handA c t ε 𝒱 U hε L Z₀ d N ?_ ?_
  · intro k _ _ s hs h0
    obtain ⟨eP⟩ := nonempty_pullback_Mplus_iso c t ε s U hε L d
    obtain ⟨eM⟩ := nonempty_pullback_Mminus_iso c t ε s U hε L d
    obtain ⟨𝒱₁, h₁, h₂⟩ := hA₁ k (s ≫ t) hs (L.pullbackAlong (pointOver t s))
      ((isAlgEquivZero_fibreModule_iff c t s L.L).mp h0)
    obtain ⟨𝒲⟩ := nonempty_twoAffineOpenCover_fibre c t 𝒱 s
    refine ⟨𝒲, ?_, ?_⟩
    · rwa [finrank_H0_fibreModule_eq_finrank_H0_baseChangeSnd c t s _ 𝒱₁ 𝒲, finrank_H0_sectionsOf_eq_of_iso _ eP]
    · rwa [finrank_H0_fibreModule_eq_finrank_H0_baseChangeSnd c t s _ 𝒱₁ 𝒲, finrank_H0_sectionsOf_eq_of_iso _ eM]
  · intro k _ _ s hs hnum
    obtain ⟨eP⟩ := nonempty_pullback_Mplus_iso c t ε s U hε L d
    obtain ⟨eM⟩ := nonempty_pullback_Mminus_iso c t ε s U hε L d
    refine (isAlgEquivZero_fibreModule_iff c t s L.L).mpr (hA₂ k (s ≫ t) hs (L.pullbackAlong (pointOver t s)) ?_)
    intro 𝒱₁
    obtain ⟨𝒲⟩ := nonempty_twoAffineOpenCover_fibre c t 𝒱 s
    obtain ⟨h₁, h₂⟩ := hnum 𝒲
    refine ⟨?_, ?_⟩
    · rwa [← finrank_H0_sectionsOf_eq_of_iso _ eP, ← finrank_H0_fibreModule_eq_finrank_H0_baseChangeSnd c t s _ 𝒱₁ 𝒲]
    · rwa [← finrank_H0_sectionsOf_eq_of_iso _ eM, ← finrank_H0_fibreModule_eq_finrank_H0_baseChangeSnd c t s _ 𝒱₁ 𝒲]

private theorem _root_.AlgebraicGeometry.Scheme.TwoAffineOpenCover.ext' {X : Scheme.{u}} {𝒱 𝒱' : X.TwoAffineOpenCover}
    (h0 : 𝒱.U0 = 𝒱'.U0) (h1 : 𝒱.U1 = 𝒱'.U1) : 𝒱 = 𝒱' := by
  cases 𝒱; cases 𝒱'; cases h0; cases h1; rfl

p2m_alias "P2MW.S_AlgebraicGeometry_RelPicard_exists_isOpen_inter_preimage_eq_setOf_isAlgEquivZero_fibre_of_smoothLocus_of_twoLineDegenerations.AlgebraicGeometry.Scheme.TwoAffineOpenCover.ext'" "AlgebraicGeometry.Scheme.TwoAffineOpenCover.ext'"

theorem finrank_H0_H1_sectionsOf_eq_of_iso {k : Type u} [Field k] {X : Scheme.{u}} (x : X ⟶ Spec (CommRingCat.of k))
    {M M' : X.Modules} (e : M ≅ M') (𝒱 : X.TwoAffineOpenCover) :
    Module.finrank k (𝒱.sectionsOf x M).H0 = Module.finrank k (𝒱.sectionsOf x M').H0 ∧
      Module.finrank k (𝒱.sectionsOf x M).H1 = Module.finrank k (𝒱.sectionsOf x M').H1 := by
  obtain ⟨𝒱₁, h0, h1, ⟨e0⟩, ⟨e1⟩⟩ := Scheme.TwoAffineOpenCover.exists_linearEquiv_sectionsOf_of_iso x x (Iso.refl X)
    (Category.id_comp x) 𝒱 M' M (e ≪≫ ((Scheme.Modules.pullbackId X).app M').symm)
  have h0' : 𝒱₁.U0 = 𝒱.U0 := h0
  have h1' : 𝒱₁.U1 = 𝒱.U1 := h1
  obtain rfl : 𝒱₁ = 𝒱 := Scheme.TwoAffineOpenCover.ext' h0' h1'
  exact ⟨e0.finrank_eq, e1.finrank_eq⟩

theorem eulerChar_eq_of_iso {k : Type u} [Field k] {X : Scheme.{u}} (x : X ⟶ Spec (CommRingCat.of k))
    {M M' : X.Modules} (e : M ≅ M') (𝒱 : X.TwoAffineOpenCover) :
    (Module.finrank k (𝒱.sectionsOf x M).H0 : ℤ) - Module.finrank k (𝒱.sectionsOf x M).H1 =
      (Module.finrank k (𝒱.sectionsOf x M').H0 : ℤ) - Module.finrank k (𝒱.sectionsOf x M').H1 := by
  obtain ⟨h0, h1⟩ := finrank_H0_H1_sectionsOf_eq_of_iso x e 𝒱
  rw [h0, h1]

def dualIso {X : Scheme.{u}} {L L' : X.Modules} (e : L ≅ L') : Scheme.Modules.dual L ≅ Scheme.Modules.dual L' :=
  (MonoidalClosed.internalHom.mapIso e.symm.op).app (𝟙_ X.Modules)

theorem nonempty_top_module_iso_unit (X : Scheme.{u}) :
    Nonempty ((⊤ : X.IdealSheafData).module ≅ 𝟙_ X.Modules) := by
  classical
  set E := (⊤ : X.IdealSheafData).subscheme with hE
  set ι := (⊤ : X.IdealSheafData).subschemeι with hι
  have hempty : IsEmpty ↥E := by
    refine ⟨fun e => ?_⟩
    have hmem : ι.base e ∈ Set.range ⇑ι := ⟨e, rfl⟩
    rw [Scheme.IdealSheafData.range_subschemeι, Scheme.IdealSheafData.support_top] at hmem
    exact hmem
  have hbot : ∀ V : E.Opens, V = ⊥ := fun V => by
    ext y; exact (hempty.false y).elim

  let P : SheafOfModules X.ringCatSheaf :=
    (SheafOfModules.pushforward ι.toRingCatSheafHom).obj (SheafOfModules.unit E.ringCatSheaf)
  have hsub : ∀ U, Subsingleton (P.val.obj U) := fun U => by
    change Subsingleton Γ(E, ι ⁻¹ᵁ U.unop)
    rw [hbot (ι ⁻¹ᵁ U.unop)]
    infer_instance
  have hP : IsZero P := by
    rw [IsZero.iff_id_eq_zero]
    ext U : 2
    haveI := hsub U
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro y
    exact Subsingleton.elim _ _
  have hf : ι.unitToPushforwardUnit = 0 := hP.eq_of_tgt _ _
  exact ⟨(kernelIsoOfEq hf ≪≫ kernelZeroIsoSource : _)⟩

theorem nonempty_top_invModule_iso_unit (X : Scheme.{u}) :
    Nonempty ((⊤ : X.IdealSheafData).invModule ≅ 𝟙_ X.Modules) := by
  obtain ⟨e⟩ := nonempty_top_module_iso_unit X
  obtain ⟨-, ⟨eD⟩⟩ := (Scheme.Modules.isInvertible_unit X).dual
  exact ⟨dualIso e ≪≫ (λ_ _).symm ≪≫ eD⟩

section GenusTransport

variable {k : Type u} [Field k] (x : Spec (CommRingCat.of k) ⟶ Spec (CommRingCat.of R))

theorem exists_twoAffineOpenCover_fibreAt_id_finrank_unit_eq (𝒱 : (pullback c x).TwoAffineOpenCover) :
    ∃ 𝒲 : (pullback (pullback.snd c (𝟙 (Spec (CommRingCat.of R)))) x).TwoAffineOpenCover,
      Module.finrank k (𝒱.sectionsOf (pullback.snd c x) (SheafOfModules.unit (pullback c x).ringCatSheaf)).H0 =
        Module.finrank k (𝒲.sectionsOf (fibreAt c (𝟙 _) x)
          (SheafOfModules.unit (pullback (pullback.snd c (𝟙 (Spec (CommRingCat.of R)))) x).ringCatSheaf)).H0 ∧
      Module.finrank k (𝒱.sectionsOf (pullback.snd c x) (SheafOfModules.unit (pullback c x).ringCatSheaf)).H1 =
        Module.finrank k (𝒲.sectionsOf (fibreAt c (𝟙 _) x)
          (SheafOfModules.unit (pullback (pullback.snd c (𝟙 (Spec (CommRingCat.of R)))) x).ringCatSheaf)).H1 := by
  have hx : x ≫ 𝟙 (Spec (CommRingCat.of R)) = x := Category.comp_id x
  obtain ⟨𝒲, ⟨e0⟩, ⟨e1⟩⟩ := (forall_exists_twoAffineOpenCover_linearEquiv_sectionsOf_fibreModule c (𝟙 _) x x hx
    (𝟙_ (pullback c (𝟙 (Spec (CommRingCat.of R)))).Modules)).1 𝒱

  obtain ⟨a0, a1⟩ := finrank_H0_H1_sectionsOf_eq_of_iso (fibreAt c (𝟙 _) x)
    (Scheme.Modules.pullbackTensorUnitObjIso (pullback.fst (pullback.snd c (𝟙 (Spec (CommRingCat.of R)))) x)) 𝒲
  obtain ⟨b0, b1⟩ := finrank_H0_H1_sectionsOf_eq_of_iso (pullback.snd c x)
    (Scheme.Modules.pullbackTensorUnitObjIso (baseChangeSnd c (⟨x, hx⟩ : SchemeHomOver x (𝟙 _)))) 𝒱
  refine ⟨𝒲, ?_, ?_⟩
  · change Module.finrank k (𝒱.sectionsOf (pullback.snd c x) (𝟙_ _)).H0 = Module.finrank k (𝒲.sectionsOf (fibreAt c (𝟙 _) x) (𝟙_ _)).H0
    rw [← b0, ← a0, e0.finrank_eq]
  · change Module.finrank k (𝒱.sectionsOf (pullback.snd c x) (𝟙_ _)).H1 = Module.finrank k (𝒲.sectionsOf (fibreAt c (𝟙 _) x) (𝟙_ _)).H1
    rw [← b1, ← a1, e1.finrank_eq]

theorem finrank_H1_unit_eq_of_fibreAt_id (g : ℕ)
    (hg : ∀ 𝒲 : (pullback (pullback.snd c (𝟙 (Spec (CommRingCat.of R)))) x).TwoAffineOpenCover,
      Module.finrank k (𝒲.sectionsOf (fibreAt c (𝟙 _) x)
        (SheafOfModules.unit (pullback (pullback.snd c (𝟙 (Spec (CommRingCat.of R)))) x).ringCatSheaf)).H1 = g)
    (𝒱 : (pullback c x).TwoAffineOpenCover) :
    Module.finrank k (𝒱.sectionsOf (pullback.snd c x) (SheafOfModules.unit (pullback c x).ringCatSheaf)).H1 = g := by
  obtain ⟨𝒲, -, h1⟩ := exists_twoAffineOpenCover_fibreAt_id_finrank_unit_eq c x 𝒱
  rw [h1, hg 𝒲]

theorem finrank_H0_unit_eq_one_of_bijective_sections
    (hH0 : ∀ (A : Type u) [CommRing A] [Algebra R A],
      letI := Scheme.TwoAffineOpenCover.algebraOfHom
        (Limits.pullback.snd c (Scheme.TwoAffineOpenCover.specMap R A)) ⊤
      Function.Bijective (algebraMap A Γ(Limits.pullback c (Scheme.TwoAffineOpenCover.specMap R A), ⊤)))
    (𝒱 : (pullback c x).TwoAffineOpenCover) :
    Module.finrank k (𝒱.sectionsOf (pullback.snd c x) (SheafOfModules.unit (pullback c x).ringCatSheaf)).H0 = 1 := by
  obtain ⟨𝒲, h0, -⟩ := exists_twoAffineOpenCover_fibreAt_id_finrank_unit_eq c x 𝒱
  rw [h0]
  exact Scheme.TwoAffineOpenCover.finrank_H0_unit_fibre_eq_one_of_bijective_sections c hH0 (𝟙 _) k x 𝒲

end GenusTransport

end AlgebraicGeometry.RelPicard.HCutDR

namespace AlgebraicGeometry
p2m_export "AlgebraicGeometry" "SmoothOfRelativeDimension IsProper Scheme.Modules.pullback Scheme.Hom Scheme.Hom.preimage_inf Scheme.Hom.support_ker LocallyOfFiniteType Spec Scheme.IdealSheafData.range_subschemeι Spec.map Scheme Smooth IsOpenImmersion Scheme.IdealSheafData.support_top Flat IsClosedImmersion IsReduced IsSeparated Scheme.Modules.pullbackCongr Scheme.fromSpecResidueField_apply Scheme.Modules.pullbackId Scheme.Hom.preimage_sup Scheme.Modules IsAffineHom Scheme.Hom.comp_apply Scheme.IdealSheafData Scheme.Modules.pullbackComp Scheme.Modules.IsInvertible Scheme.Modules.isInvertible_unit RelPicard.IsAlgEquivZero Scheme.Modules.dual Scheme.IdealSheafData.module RelEffCartierDiv Scheme.TwoAffineOpenCover Scheme.TwoAffineOpenCover.specMap Scheme.TwoAffineOpenCover.algebraOfHom Scheme.TwoAffineOpenCover.moduleSectionsOfHom Scheme.IdealSheafData.isInvertible_top Scheme.TwoAffineOpenCover.exists_linearEquiv_sectionsOf_H0 Scheme.TwoAffineOpenCover.exists_isPullback_snd_specMap_algebraOfHom Scheme.Modules.exists_iso_pullback_of_isPullback Scheme.TwoAffineOpenCover.exists_linearEquiv_sectionsOf_of_iso Scheme.Modules.pullbackTensorObjIso Scheme.Modules.pullbackTensorUnitObjIso Scheme.TwoAffineOpenCover.finrank_H0_unit_fibre_eq_one_of_bijective_sections Scheme.Modules.nonempty_pullback_tensor_invModule_pow_tensor_module_iso_of_forall_notMem_support RelEffCartierDiv.empty RelEffCartierDiv.empty_I RelEffCartierDiv.I_eq_top_of_degree_zero graphOver TwoGluedProjectiveLines.isAlgEquivZero_of_pullback_iso_unit RelPicard.IsAlgEquivZero.nonempty_pullback_iso_pullback_unit_and_eulerChar_eq_one_of_curveModel_ratFunc TwoGluedProjectiveLines.nonempty_pullback_iso_unit_of_finrank_H0_twists_lt_two TwoGluedProjectiveLines.finrank_H0_twists_lt_two_of_nonempty_pullback_iso_unit Scheme.Modules.IsInvertible.eulerChar_sectionsOf_tensor_eq_add_sub Scheme.Modules.IsInvertible.eulerChar_sectionsOf_dual_eq Scheme.TwoAffineOpenCover.ext' Scheme.TwoAffineOpenCover.comapOfIsAffineHom'"
namespace RelPicard
p2m_export "AlgebraicGeometry.RelPicard" "baseChangeSnd rigSection RigidifiedLineBundle fibreAt IsAlgEquivZero sectionIdeal sectionTwist fibreModule isClosed_setOf_forall_fibre_le_finrank_H0_of_twoAffineOpenCover exists_twoAffineOpenCover_fibre_finrank_eq_finrank_cechDiff_baseChange_residueField isInvertible_sectionIdeal_of_range_subset forall_exists_twoAffineOpenCover_linearEquiv_sectionsOf_fibreModule nonempty_pullback_sectionTwist_iso_of_range_subset eulerChar_pullback_firstLine_sectionTwist_tensor_idealModule_eq sectionFibrePoint IsAlgEquivZero.nonempty_pullback_iso_pullback_unit_and_eulerChar_eq_one_of_curveModel_ratFunc"
namespace HCutDR
p2m_open "AlgebraicGeometry.RelPicard AlgebraicGeometry"

variable {R : Type u} [CommRing R] {C : Scheme.{u}} (c : C ⟶ Spec (CommRingCat.of R))
  (ε : SchemeHomOver (𝟙 (Spec (CommRingCat.of R))) c)

section Lines

variable {k : Type u} [Field k] (x : Spec (CommRingCat.of k) ⟶ Spec (CommRingCat.of R))

theorem isClosedImmersion_rigSection [IsSeparated c] : IsClosedImmersion (rigSection c x ε) := by
  have h : (x ≫ ε.1) ≫ c = x := by rw [Category.assoc, ε.2, Category.comp_id]
  show IsClosedImmersion (graphOver c (x ≫ ε.1) h)
  infer_instance

theorem nonempty_pullback_Mplus_iso_line (L' : RigidifiedLineBundle c ε x) (d : ℕ) {Y : Scheme.{u}} (i : Y ⟶ pullback c x) :
    Nonempty ((Scheme.Modules.pullback i).obj (Mplus c x ε L' d) ≅
      (((Scheme.Modules.pullback i).obj L'.L) ⊗ ((Scheme.Modules.pullback i).obj L'.L)) ⊗
        (Scheme.Modules.pullback i).obj (sectionTwist c ε x d)) :=
  ⟨Scheme.Modules.pullbackTensorObjIso _ _ _ ≪≫ tensorIso (Scheme.Modules.pullbackTensorObjIso _ _ _) (Iso.refl _)⟩

theorem nonempty_pullback_Mminus_iso_line (L' : RigidifiedLineBundle c ε x) (d : ℕ) {Y : Scheme.{u}} (i : Y ⟶ pullback c x) :
    Nonempty ((Scheme.Modules.pullback i).obj (Mminus c x ε L' d) ≅
      ((Scheme.Modules.dual ((Scheme.Modules.pullback i).obj L'.L)) ⊗ (Scheme.Modules.dual ((Scheme.Modules.pullback i).obj L'.L))) ⊗
        (Scheme.Modules.pullback i).obj (sectionTwist c ε x d)) := by
  obtain ⟨eD⟩ := L'.isInvertible.pullback_dual i
  exact ⟨Scheme.Modules.pullbackTensorObjIso _ _ _ ≪≫
    tensorIso (Scheme.Modules.pullbackTensorObjIso _ _ _ ≪≫ tensorIso eD eD) (Iso.refl _)⟩

theorem rigSection_closedPoint_notMem_range (U : C.Opens) (hε : Set.range ε.1.base ⊆ (U : Set C))
    {Y₁ Y₂ : Scheme.{u}} (i₁ : Y₁ ⟶ pullback c x) (i₂ : Y₂ ⟶ pullback c x) {ι : Type*} (node : ι → Y₁) (P : Y₁)
    (hεP : i₁.base P = (rigSection c x ε).base (IsLocalRing.closedPoint k))
    (hinter : ∀ (p : Y₁) (q : Y₂), i₁.base p = i₂.base q → ∃ i, p = node i)
    (hnodesU : ∀ i, i₁.base (node i) ∉ (pullback.fst c x ⁻¹ᵁ U : (pullback c x).Opens)) :
    (rigSection c x ε).base (IsLocalRing.closedPoint k) ∉ Set.range i₂.base := by
  rintro ⟨q, hq⟩
  obtain ⟨i, rfl⟩ := hinter P q (hεP.trans hq.symm)
  apply hnodesU i
  change (pullback.fst c x) (i₁.base (node i)) ∈ U
  rw [hεP]
  change (rigSection c x ε ≫ pullback.fst c x) (IsLocalRing.closedPoint k) ∈ U
  rw [rigSection, pullback.lift_fst, Scheme.Hom.comp_apply]
  exact hε ⟨_, rfl⟩

theorem nonempty_pullback_sectionTwist_iso_unit_of_notMem [IsSeparated c]
    (U : C.Opens) [SmoothOfRelativeDimension 1 (U.ι ≫ c)] (hε : Set.range ε.1.base ⊆ (U : Set C))
    {Y : Scheme.{u}} (i₂ : Y ⟶ pullback c x)
    (hε₂ : (rigSection c x ε).base (IsLocalRing.closedPoint k) ∉ Set.range i₂.base) (d : ℕ) :
    Nonempty ((Scheme.Modules.pullback i₂).obj (sectionTwist c ε x d) ≅ 𝟙_ Y.Modules) := by
  haveI := isClosedImmersion_rigSection c ε x
  have hJ : (sectionIdeal c ε x).IsInvertible := isInvertible_sectionIdeal_of_range_subset c ε U hε x
  have hJsupp : ∀ y : Y, i₂.base y ∉ ((sectionIdeal c ε x).support : Set ↥(pullback c x)) := by
    intro y hy
    change i₂.base y ∈ ((rigSection c x ε).ker.support : Set ↥(pullback c x)) at hy
    rw [Scheme.Hom.support_ker, (rigSection c x ε).isClosedEmbedding.isClosed_range.closure_eq] at hy
    obtain ⟨z, hz⟩ := hy
    rw [eq_closedPoint z] at hz
    exact hε₂ ⟨y, hz.symm⟩
  have hNsupp : ∀ y : Y, i₂.base y ∉ ((⊤ : (pullback c x).IdealSheafData).support : Set ↥(pullback c x)) := by
    intro y hy
    rw [Scheme.IdealSheafData.support_top] at hy
    exact hy
  obtain ⟨e⟩ := Scheme.Modules.nonempty_pullback_tensor_invModule_pow_tensor_module_iso_of_forall_notMem_support i₂
    (sectionIdeal c ε x) hJ ⊤ Scheme.IdealSheafData.isInvertible_top d hJsupp hNsupp (𝟙_ _) ⟨Iso.refl _⟩
  obtain ⟨eTop⟩ := nonempty_top_module_iso_unit (pullback c x)

  let e₀ : sectionTwist c ε x d ≅ 𝟙_ _ ⊗ (((sectionIdeal c ε x) ^ d).invModule ⊗ (⊤ : (pullback c x).IdealSheafData).module) :=
    (ρ_ _).symm ≪≫ whiskerLeftIso _ eTop.symm ≪≫ (λ_ _).symm
  exact ⟨(Scheme.Modules.pullback i₂).mapIso e₀ ≪≫ e ≪≫ Scheme.Modules.pullbackTensorUnitObjIso i₂⟩

theorem eulerChar_pullback_secondLine_sectionTwist_eq_one [IsSeparated c] [IsAlgClosed k]
    (U : C.Opens) [SmoothOfRelativeDimension 1 (U.ι ≫ c)] (hε : Set.range ε.1.base ⊆ (U : Set C))
    (M₂ : CurveModel k (RatFunc k)) (i₂ : M₂.C ⟶ pullback c x)
    (hε₂ : (rigSection c x ε).base (IsLocalRing.closedPoint k) ∉ Set.range i₂.base) (d : ℕ) :
    ∀ 𝒲' : M₂.C.TwoAffineOpenCover,
      ((Module.finrank k ↥(𝒲'.sectionsOf M₂.toBase ((Scheme.Modules.pullback i₂).obj (sectionTwist c ε x d))).H0 : ℤ) - Module.finrank k (𝒲'.sectionsOf M₂.toBase ((Scheme.Modules.pullback i₂).obj (sectionTwist c ε x d))).H1) = 1 := by
  intro 𝒲'
  obtain ⟨e⟩ := nonempty_pullback_sectionTwist_iso_unit_of_notMem c ε x U hε i₂ hε₂ d
  obtain ⟨h1, h0⟩ := CurveModel.finrank_H1_sectionsOf_unit_eq_zero_and_finrank_H0_eq_one_of_ratFunc k M₂ 𝒲'
  rw [eulerChar_eq_of_iso M₂.toBase e 𝒲']
  change (Module.finrank k ↥(𝒲'.sectionsOf M₂.toBase (SheafOfModules.unit M₂.C.ringCatSheaf : M₂.C.Modules)).H0 : ℤ) -
    Module.finrank k (𝒲'.sectionsOf M₂.toBase (SheafOfModules.unit M₂.C.ringCatSheaf : M₂.C.Modules)).H1 = 1
  rw [h1, h0]; norm_num

theorem eulerChar_pullback_Mplus_Mminus [IsSeparated c]
    (U : C.Opens) [SmoothOfRelativeDimension 1 (U.ι ≫ c)] (hε : Set.range ε.1.base ⊆ (U : Set C))
    (L' : RigidifiedLineBundle c ε x) (d : ℕ)
    (M : CurveModel k (RatFunc k)) (i : M.C ⟶ pullback c x)
    (hDA : (∀ (A B : M.C.Modules), Scheme.Modules.IsInvertible A → Scheme.Modules.IsInvertible B →
      ∀ 𝒲 : M.C.TwoAffineOpenCover,
        ((Module.finrank k ↥(𝒲.sectionsOf M.toBase (A ⊗ B)).H0 : ℤ) - Module.finrank k (𝒲.sectionsOf M.toBase (A ⊗ B)).H1) = ((Module.finrank k ↥(𝒲.sectionsOf M.toBase A).H0 : ℤ) - Module.finrank k (𝒲.sectionsOf M.toBase A).H1) + ((Module.finrank k ↥(𝒲.sectionsOf M.toBase B).H0 : ℤ) - Module.finrank k (𝒲.sectionsOf M.toBase B).H1) - 1 ∧
        ((Module.finrank k ↥(𝒲.sectionsOf M.toBase (Scheme.Modules.dual A)).H0 : ℤ) - Module.finrank k (𝒲.sectionsOf M.toBase (Scheme.Modules.dual A)).H1) = 2 - ((Module.finrank k ↥(𝒲.sectionsOf M.toBase A).H0 : ℤ) - Module.finrank k (𝒲.sectionsOf M.toBase A).H1)))
    (τ : ℤ) (htw : ∀ 𝒲' : M.C.TwoAffineOpenCover, ((Module.finrank k ↥(𝒲'.sectionsOf M.toBase ((Scheme.Modules.pullback i).obj (sectionTwist c ε x d))).H0 : ℤ) - Module.finrank k (𝒲'.sectionsOf M.toBase ((Scheme.Modules.pullback i).obj (sectionTwist c ε x d))).H1) = τ) :
    (∀ 𝒲' : M.C.TwoAffineOpenCover,
      ((Module.finrank k ↥(𝒲'.sectionsOf M.toBase ((Scheme.Modules.pullback i).obj (Mplus c x ε L' d))).H0 : ℤ) - Module.finrank k (𝒲'.sectionsOf M.toBase ((Scheme.Modules.pullback i).obj (Mplus c x ε L' d))).H1) =
        2 * ((Module.finrank k ↥(𝒲'.sectionsOf M.toBase ((Scheme.Modules.pullback i).obj L'.L)).H0 : ℤ) - Module.finrank k (𝒲'.sectionsOf M.toBase ((Scheme.Modules.pullback i).obj L'.L)).H1) - 1 + (τ - 1)) ∧
    (∀ 𝒲' : M.C.TwoAffineOpenCover,
      ((Module.finrank k ↥(𝒲'.sectionsOf M.toBase ((Scheme.Modules.pullback i).obj (Mminus c x ε L' d))).H0 : ℤ) - Module.finrank k (𝒲'.sectionsOf M.toBase ((Scheme.Modules.pullback i).obj (Mminus c x ε L' d))).H1) =
        3 - 2 * ((Module.finrank k ↥(𝒲'.sectionsOf M.toBase ((Scheme.Modules.pullback i).obj L'.L)).H0 : ℤ) - Module.finrank k (𝒲'.sectionsOf M.toBase ((Scheme.Modules.pullback i).obj L'.L)).H1) + (τ - 1)) := by
  have hA : Scheme.Modules.IsInvertible ((Scheme.Modules.pullback i).obj L'.L) := L'.isInvertible.pullback i
  have hS : Scheme.Modules.IsInvertible ((Scheme.Modules.pullback i).obj (sectionTwist c ε x d)) :=
    (isInvertible_sectionTwist c x ε U hε d).pullback i
  have hAd : Scheme.Modules.IsInvertible (Scheme.Modules.dual ((Scheme.Modules.pullback i).obj L'.L)) := hA.dual.1
  obtain ⟨eP⟩ := nonempty_pullback_Mplus_iso_line c ε x L' d i
  obtain ⟨eM⟩ := nonempty_pullback_Mminus_iso_line c ε x L' d i
  refine ⟨fun 𝒲' => ?_, fun 𝒲' => ?_⟩
  · rw [eulerChar_eq_of_iso M.toBase eP 𝒲', (hDA _ _ (hA.tensor hA) hS 𝒲').1, (hDA _ _ hA hA 𝒲').1, htw 𝒲']
    ring
  · rw [eulerChar_eq_of_iso M.toBase eM 𝒲', (hDA _ _ (hAd.tensor hAd) hS 𝒲').1, (hDA _ _ hAd hAd 𝒲').1,
      (hDA _ _ hA hA 𝒲').2, htw 𝒲']
    ring

end Lines

end AlgebraicGeometry.RelPicard.HCutDR

namespace AlgebraicGeometry
p2m_export "AlgebraicGeometry" "SmoothOfRelativeDimension IsProper Scheme.Modules.pullback Scheme.Hom Scheme.Hom.preimage_inf Scheme.Hom.support_ker LocallyOfFiniteType Spec Scheme.IdealSheafData.range_subschemeι Spec.map Scheme Smooth IsOpenImmersion Scheme.IdealSheafData.support_top Flat IsClosedImmersion IsReduced IsSeparated Scheme.Modules.pullbackCongr Scheme.fromSpecResidueField_apply Scheme.Modules.pullbackId Scheme.Hom.preimage_sup Scheme.Modules IsAffineHom Scheme.Hom.comp_apply Scheme.IdealSheafData Scheme.Modules.pullbackComp Scheme.Modules.IsInvertible Scheme.Modules.isInvertible_unit RelPicard.IsAlgEquivZero Scheme.Modules.dual Scheme.IdealSheafData.module RelEffCartierDiv Scheme.TwoAffineOpenCover Scheme.TwoAffineOpenCover.specMap Scheme.TwoAffineOpenCover.algebraOfHom Scheme.TwoAffineOpenCover.moduleSectionsOfHom Scheme.IdealSheafData.isInvertible_top Scheme.TwoAffineOpenCover.exists_linearEquiv_sectionsOf_H0 Scheme.TwoAffineOpenCover.exists_isPullback_snd_specMap_algebraOfHom Scheme.Modules.exists_iso_pullback_of_isPullback Scheme.TwoAffineOpenCover.exists_linearEquiv_sectionsOf_of_iso Scheme.Modules.pullbackTensorObjIso Scheme.Modules.pullbackTensorUnitObjIso Scheme.TwoAffineOpenCover.finrank_H0_unit_fibre_eq_one_of_bijective_sections Scheme.Modules.nonempty_pullback_tensor_invModule_pow_tensor_module_iso_of_forall_notMem_support RelEffCartierDiv.empty RelEffCartierDiv.empty_I RelEffCartierDiv.I_eq_top_of_degree_zero graphOver TwoGluedProjectiveLines.isAlgEquivZero_of_pullback_iso_unit RelPicard.IsAlgEquivZero.nonempty_pullback_iso_pullback_unit_and_eulerChar_eq_one_of_curveModel_ratFunc TwoGluedProjectiveLines.nonempty_pullback_iso_unit_of_finrank_H0_twists_lt_two TwoGluedProjectiveLines.finrank_H0_twists_lt_two_of_nonempty_pullback_iso_unit Scheme.Modules.IsInvertible.eulerChar_sectionsOf_tensor_eq_add_sub Scheme.Modules.IsInvertible.eulerChar_sectionsOf_dual_eq Scheme.TwoAffineOpenCover.ext' Scheme.TwoAffineOpenCover.comapOfIsAffineHom'"
namespace RelPicard
p2m_export "AlgebraicGeometry.RelPicard" "baseChangeSnd rigSection RigidifiedLineBundle fibreAt IsAlgEquivZero sectionIdeal sectionTwist fibreModule isClosed_setOf_forall_fibre_le_finrank_H0_of_twoAffineOpenCover exists_twoAffineOpenCover_fibre_finrank_eq_finrank_cechDiff_baseChange_residueField isInvertible_sectionIdeal_of_range_subset forall_exists_twoAffineOpenCover_linearEquiv_sectionsOf_fibreModule nonempty_pullback_sectionTwist_iso_of_range_subset eulerChar_pullback_firstLine_sectionTwist_tensor_idealModule_eq sectionFibrePoint IsAlgEquivZero.nonempty_pullback_iso_pullback_unit_and_eulerChar_eq_one_of_curveModel_ratFunc"
namespace HCutDR
p2m_open "AlgebraicGeometry.RelPicard AlgebraicGeometry"

variable {R : Type u} [CommRing R] {C : Scheme.{u}} (c : C ⟶ Spec (CommRingCat.of R))
  (ε : SchemeHomOver (𝟙 (Spec (CommRingCat.of R))) c)

theorem eulerChar_pullback_firstLine_sectionTwist_eq [IsProper c]
    (U : C.Opens) [SmoothOfRelativeDimension 1 (U.ι ≫ c)] (hεU : Set.range ε.1.base ⊆ (U : Set C)) (g : ℕ)
    (k : Type u) [Field k] [IsAlgClosed k] [DecidableEq (RatFunc k)]
    (s : Spec (CommRingCat.of k) ⟶ Spec (CommRingCat.of R)) [IsReduced (pullback c s)]
    (M₁ M₂ : CurveModel k (RatFunc k)) (i₁ : M₁.C ⟶ pullback c s) (i₂ : M₂.C ⟶ pullback c s)
    [IsClosedImmersion i₁] [IsClosedImmersion i₂]
    (n : ℕ) (a b : Fin n → kˣ) (𝒲₀ : (pullback c s).TwoAffineOpenCover)
    (hi₁ : i₁ ≫ pullback.snd c s = M₁.toBase)
    (hi₂ : i₂ ≫ pullback.snd c s = M₂.toBase)
    (hcover : Set.range i₁.base ∪ Set.range i₂.base = Set.univ)
    (ha : Function.Injective a)
    (hnode : ∀ i, i₁.base (M₁.placeEquiv.symm (RationalFunctionField.placeOfPoint k (a i : k))).1 =
          i₂.base (M₂.placeEquiv.symm (RationalFunctionField.placeOfPoint k (b i : k))).1)
    (hinter : ∀ (p : M₁.C) (q : M₂.C), i₁.base p = i₂.base q →
          ∃ i, p = (M₁.placeEquiv.symm (RationalFunctionField.placeOfPoint k (a i : k))).1 ∧
          q = (M₂.placeEquiv.symm (RationalFunctionField.placeOfPoint k (b i : k))).1)
    (htrans : IsReduced (pullback i₁ i₂))
    (hU0₁ : ((i₁ ⁻¹ᵁ 𝒲₀.U0 : M₁.C.Opens) : Set M₁.C) =
          {(M₁.placeEquiv.symm (RationalFunctionField.placeInfty k)).1}ᶜ)
    (hU0₂ : ((i₂ ⁻¹ᵁ 𝒲₀.U0 : M₂.C.Opens) : Set M₂.C) =
          {(M₂.placeEquiv.symm (RationalFunctionField.placeInfty k)).1}ᶜ)
    (hU1₁ : ((i₁ ⁻¹ᵁ 𝒲₀.U1 : M₁.C.Opens) : Set M₁.C) =
          {(M₁.placeEquiv.symm (RationalFunctionField.placeOfPoint k 0)).1}ᶜ)
    (hU1₂ : ((i₂ ⁻¹ᵁ 𝒲₀.U1 : M₂.C.Opens) : Set M₂.C) =
          {(M₂.placeEquiv.symm (RationalFunctionField.placeOfPoint k 0)).1}ᶜ)
    (hεinf : i₁.base (M₁.placeEquiv.symm (RationalFunctionField.placeInfty k)).1 = ((sectionFibrePoint ε s).1).base (IsLocalRing.closedPoint k))
    (hcomp : Set.range i₁.base ∩ ((pullback.fst c s ⁻¹ᵁ U : (pullback c s).Opens) : Set ↥(pullback c s)) =
          connectedComponentIn ((pullback.fst c s ⁻¹ᵁ U : (pullback c s).Opens) : Set ↥(pullback c s)) (((sectionFibrePoint ε s).1).base (IsLocalRing.closedPoint k)))
    (hnodesU : ∀ i, i₁.base (M₁.placeEquiv.symm (RationalFunctionField.placeOfPoint k (a i : k))).1 ∉
          (pullback.fst c s ⁻¹ᵁ U : (pullback c s).Opens))
    (hnonnodes : ∀ y : ↥(pullback c s),
          (∀ i, y ≠ i₁.base (M₁.placeEquiv.symm (RationalFunctionField.placeOfPoint k (a i : k))).1) →
            y ∈ (pullback.fst c s ⁻¹ᵁ U : (pullback c s).Opens))
    (hW₁ : ∃ W₁ : (pullback c s).Opens, (W₁ : Set ↥(pullback c s)) = (Set.range i₂.base)ᶜ ∧
          IsOpenImmersion ((i₁ ⁻¹ᵁ W₁).ι ≫ i₁))
    :
    ∀ 𝒲' : M₁.C.TwoAffineOpenCover,
      ((Module.finrank k ↥(𝒲'.sectionsOf M₁.toBase ((Scheme.Modules.pullback i₁).obj (sectionTwist c ε s g))).H0 : ℤ) - Module.finrank k (𝒲'.sectionsOf M₁.toBase ((Scheme.Modules.pullback i₁).obj (sectionTwist c ε s g))).H1) = g + 1 := by
  intro 𝒲'
  have hDγU : (RelEffCartierDiv.empty c (𝟙 (Spec (CommRingCat.of R)))).SupportedIn U := by
    intro y hy
    exfalso
    rw [RelEffCartierDiv.empty_I, Scheme.IdealSheafData.support_top] at hy
    exact hy
  have hDγcomp : (pullback.fst c s).base ⁻¹'
      (((RelEffCartierDiv.empty c (𝟙 (Spec (CommRingCat.of R)))).I.subschemeι ≫ pullback.fst c (𝟙 _)).base '' Set.univ) ⊆
        connectedComponentIn ((pullback.fst c s ⁻¹ᵁ U : (pullback c s).Opens) : Set ↥(pullback c s))
          (((sectionFibrePoint ε s).1).base (IsLocalRing.closedPoint k)) := by
    rintro y ⟨z, -, -⟩
    exfalso
    have hz : ((RelEffCartierDiv.empty c (𝟙 (Spec (CommRingCat.of R)))).I.subschemeι).base z ∈
        Set.range ⇑(RelEffCartierDiv.empty c (𝟙 (Spec (CommRingCat.of R)))).I.subschemeι := ⟨z, rfl⟩
    rw [Scheme.IdealSheafData.range_subschemeι] at hz
    obtain ⟨w, hw⟩ : ∃ w : ↥(pullback c (𝟙 (Spec (CommRingCat.of R)))),
        w ∈ ((RelEffCartierDiv.empty c (𝟙 (Spec (CommRingCat.of R)))).I.support : Set _) := ⟨_, hz⟩
    rw [RelEffCartierDiv.empty_I, Scheme.IdealSheafData.support_top] at hw
    exact hw
  have h := eulerChar_pullback_firstLine_sectionTwist_tensor_idealModule_eq R c U ε hεU 0 g g (Nat.add_zero g)
    (RelEffCartierDiv.empty c (𝟙 _)) hDγU k s M₁ M₂ i₁ i₂ n a b 𝒲₀ hi₁ hi₂ hcover ha hnode hinter htrans
    hU0₁ hU0₂ hU1₁ hU1₂ hεinf hcomp hnodesU hnonnodes hW₁ hDγcomp 𝒲'

  have hI : ((RelEffCartierDiv.empty c (𝟙 (Spec (CommRingCat.of R)))).pullbackAlong s (Category.comp_id s)).I = ⊤ :=
    RelEffCartierDiv.I_eq_top_of_degree_zero _
  obtain ⟨eTop⟩ := nonempty_top_module_iso_unit (pullback c s)
  have eI : ((RelEffCartierDiv.empty c (𝟙 (Spec (CommRingCat.of R)))).pullbackAlong s (Category.comp_id s)).idealModule ≅
      𝟙_ (pullback c s).Modules :=
    eqToIso (congrArg Scheme.IdealSheafData.module hI) ≪≫ eTop
  have e : sectionTwist c ε s g ⊗
      ((RelEffCartierDiv.empty c (𝟙 (Spec (CommRingCat.of R)))).pullbackAlong s (Category.comp_id s)).idealModule ≅
        sectionTwist c ε s g :=
    whiskerLeftIso _ eI ≪≫ ρ_ _
  rw [← h]
  exact (eulerChar_eq_of_iso M₁.toBase ((Scheme.Modules.pullback i₁).mapIso e) 𝒲').symm

theorem chi_bookkeeping [IsProper c]
    (U : C.Opens) [SmoothOfRelativeDimension 1 (U.ι ≫ c)] (hεU : Set.range ε.1.base ⊆ (U : Set C)) (g : ℕ)
    (k : Type u) [Field k] [IsAlgClosed k] [DecidableEq (RatFunc k)]
    (s : Spec (CommRingCat.of k) ⟶ Spec (CommRingCat.of R)) [IsReduced (pullback c s)]
    (M₁ M₂ : CurveModel k (RatFunc k)) (i₁ : M₁.C ⟶ pullback c s) (i₂ : M₂.C ⟶ pullback c s)
    [IsClosedImmersion i₁] [IsClosedImmersion i₂]
    (n : ℕ) (a b : Fin n → kˣ) (𝒲₀ : (pullback c s).TwoAffineOpenCover)
    (hi₁ : i₁ ≫ pullback.snd c s = M₁.toBase)
    (hi₂ : i₂ ≫ pullback.snd c s = M₂.toBase)
    (hcover : Set.range i₁.base ∪ Set.range i₂.base = Set.univ)
    (ha : Function.Injective a)
    (hnode : ∀ i, i₁.base (M₁.placeEquiv.symm (RationalFunctionField.placeOfPoint k (a i : k))).1 =
          i₂.base (M₂.placeEquiv.symm (RationalFunctionField.placeOfPoint k (b i : k))).1)
    (hinter : ∀ (p : M₁.C) (q : M₂.C), i₁.base p = i₂.base q →
          ∃ i, p = (M₁.placeEquiv.symm (RationalFunctionField.placeOfPoint k (a i : k))).1 ∧
          q = (M₂.placeEquiv.symm (RationalFunctionField.placeOfPoint k (b i : k))).1)
    (htrans : IsReduced (pullback i₁ i₂))
    (hU0₁ : ((i₁ ⁻¹ᵁ 𝒲₀.U0 : M₁.C.Opens) : Set M₁.C) =
          {(M₁.placeEquiv.symm (RationalFunctionField.placeInfty k)).1}ᶜ)
    (hU0₂ : ((i₂ ⁻¹ᵁ 𝒲₀.U0 : M₂.C.Opens) : Set M₂.C) =
          {(M₂.placeEquiv.symm (RationalFunctionField.placeInfty k)).1}ᶜ)
    (hU1₁ : ((i₁ ⁻¹ᵁ 𝒲₀.U1 : M₁.C.Opens) : Set M₁.C) =
          {(M₁.placeEquiv.symm (RationalFunctionField.placeOfPoint k 0)).1}ᶜ)
    (hU1₂ : ((i₂ ⁻¹ᵁ 𝒲₀.U1 : M₂.C.Opens) : Set M₂.C) =
          {(M₂.placeEquiv.symm (RationalFunctionField.placeOfPoint k 0)).1}ᶜ)
    (hεinf : i₁.base (M₁.placeEquiv.symm (RationalFunctionField.placeInfty k)).1 = ((sectionFibrePoint ε s).1).base (IsLocalRing.closedPoint k))
    (hcomp : Set.range i₁.base ∩ ((pullback.fst c s ⁻¹ᵁ U : (pullback c s).Opens) : Set ↥(pullback c s)) =
          connectedComponentIn ((pullback.fst c s ⁻¹ᵁ U : (pullback c s).Opens) : Set ↥(pullback c s)) (((sectionFibrePoint ε s).1).base (IsLocalRing.closedPoint k)))
    (hnodesU : ∀ i, i₁.base (M₁.placeEquiv.symm (RationalFunctionField.placeOfPoint k (a i : k))).1 ∉
          (pullback.fst c s ⁻¹ᵁ U : (pullback c s).Opens))
    (hnonnodes : ∀ y : ↥(pullback c s),
          (∀ i, y ≠ i₁.base (M₁.placeEquiv.symm (RationalFunctionField.placeOfPoint k (a i : k))).1) →
            y ∈ (pullback.fst c s ⁻¹ᵁ U : (pullback c s).Opens))
    (hW₁ : ∃ W₁ : (pullback c s).Opens, (W₁ : Set ↥(pullback c s)) = (Set.range i₂.base)ᶜ ∧
          IsOpenImmersion ((i₁ ⁻¹ᵁ W₁).ι ≫ i₁))
    (L' : RigidifiedLineBundle c ε s)
    (hDA₁ : (∀ (A B : M₁.C.Modules), Scheme.Modules.IsInvertible A → Scheme.Modules.IsInvertible B →
      ∀ 𝒲 : M₁.C.TwoAffineOpenCover,
        ((Module.finrank k ↥(𝒲.sectionsOf M₁.toBase (A ⊗ B)).H0 : ℤ) - Module.finrank k (𝒲.sectionsOf M₁.toBase (A ⊗ B)).H1) = ((Module.finrank k ↥(𝒲.sectionsOf M₁.toBase A).H0 : ℤ) - Module.finrank k (𝒲.sectionsOf M₁.toBase A).H1) + ((Module.finrank k ↥(𝒲.sectionsOf M₁.toBase B).H0 : ℤ) - Module.finrank k (𝒲.sectionsOf M₁.toBase B).H1) - 1 ∧
        ((Module.finrank k ↥(𝒲.sectionsOf M₁.toBase (Scheme.Modules.dual A)).H0 : ℤ) - Module.finrank k (𝒲.sectionsOf M₁.toBase (Scheme.Modules.dual A)).H1) = 2 - ((Module.finrank k ↥(𝒲.sectionsOf M₁.toBase A).H0 : ℤ) - Module.finrank k (𝒲.sectionsOf M₁.toBase A).H1)))
    (hDA₂ : (∀ (A B : M₂.C.Modules), Scheme.Modules.IsInvertible A → Scheme.Modules.IsInvertible B →
      ∀ 𝒲 : M₂.C.TwoAffineOpenCover,
        ((Module.finrank k ↥(𝒲.sectionsOf M₂.toBase (A ⊗ B)).H0 : ℤ) - Module.finrank k (𝒲.sectionsOf M₂.toBase (A ⊗ B)).H1) = ((Module.finrank k ↥(𝒲.sectionsOf M₂.toBase A).H0 : ℤ) - Module.finrank k (𝒲.sectionsOf M₂.toBase A).H1) + ((Module.finrank k ↥(𝒲.sectionsOf M₂.toBase B).H0 : ℤ) - Module.finrank k (𝒲.sectionsOf M₂.toBase B).H1) - 1 ∧
        ((Module.finrank k ↥(𝒲.sectionsOf M₂.toBase (Scheme.Modules.dual A)).H0 : ℤ) - Module.finrank k (𝒲.sectionsOf M₂.toBase (Scheme.Modules.dual A)).H1) = 2 - ((Module.finrank k ↥(𝒲.sectionsOf M₂.toBase A).H0 : ℤ) - Module.finrank k (𝒲.sectionsOf M₂.toBase A).H1))) :
    (∀ 𝒲' : M₁.C.TwoAffineOpenCover, ((Module.finrank k ↥(𝒲'.sectionsOf M₁.toBase ((Scheme.Modules.pullback i₁).obj (Mplus c s ε L' g))).H0 : ℤ) - Module.finrank k (𝒲'.sectionsOf M₁.toBase ((Scheme.Modules.pullback i₁).obj (Mplus c s ε L' g))).H1) =
        2 * ((Module.finrank k ↥(𝒲'.sectionsOf M₁.toBase ((Scheme.Modules.pullback i₁).obj L'.L)).H0 : ℤ) - Module.finrank k (𝒲'.sectionsOf M₁.toBase ((Scheme.Modules.pullback i₁).obj L'.L)).H1) - 1 + g) ∧
    (∀ 𝒲' : M₂.C.TwoAffineOpenCover, ((Module.finrank k ↥(𝒲'.sectionsOf M₂.toBase ((Scheme.Modules.pullback i₂).obj (Mplus c s ε L' g))).H0 : ℤ) - Module.finrank k (𝒲'.sectionsOf M₂.toBase ((Scheme.Modules.pullback i₂).obj (Mplus c s ε L' g))).H1) =
        2 * ((Module.finrank k ↥(𝒲'.sectionsOf M₂.toBase ((Scheme.Modules.pullback i₂).obj L'.L)).H0 : ℤ) - Module.finrank k (𝒲'.sectionsOf M₂.toBase ((Scheme.Modules.pullback i₂).obj L'.L)).H1) - 1) ∧
    (∀ 𝒲' : M₁.C.TwoAffineOpenCover, ((Module.finrank k ↥(𝒲'.sectionsOf M₁.toBase ((Scheme.Modules.pullback i₁).obj (Mminus c s ε L' g))).H0 : ℤ) - Module.finrank k (𝒲'.sectionsOf M₁.toBase ((Scheme.Modules.pullback i₁).obj (Mminus c s ε L' g))).H1) =
        3 - 2 * ((Module.finrank k ↥(𝒲'.sectionsOf M₁.toBase ((Scheme.Modules.pullback i₁).obj L'.L)).H0 : ℤ) - Module.finrank k (𝒲'.sectionsOf M₁.toBase ((Scheme.Modules.pullback i₁).obj L'.L)).H1) + g) ∧
    (∀ 𝒲' : M₂.C.TwoAffineOpenCover, ((Module.finrank k ↥(𝒲'.sectionsOf M₂.toBase ((Scheme.Modules.pullback i₂).obj (Mminus c s ε L' g))).H0 : ℤ) - Module.finrank k (𝒲'.sectionsOf M₂.toBase ((Scheme.Modules.pullback i₂).obj (Mminus c s ε L' g))).H1) =
        3 - 2 * ((Module.finrank k ↥(𝒲'.sectionsOf M₂.toBase ((Scheme.Modules.pullback i₂).obj L'.L)).H0 : ℤ) - Module.finrank k (𝒲'.sectionsOf M₂.toBase ((Scheme.Modules.pullback i₂).obj L'.L)).H1)) := by

  have htw₁ := eulerChar_pullback_firstLine_sectionTwist_eq c ε U hεU g k s M₁ M₂ i₁ i₂ n a b 𝒲₀ hi₁ hi₂ hcover ha hnode
    hinter htrans hU0₁ hU0₂ hU1₁ hU1₂ hεinf hcomp hnodesU hnonnodes hW₁
  have hε₂ : (rigSection c s ε).base (IsLocalRing.closedPoint k) ∉ Set.range i₂.base :=
    rigSection_closedPoint_notMem_range c ε s U hεU i₁ i₂
      (fun i => (M₁.placeEquiv.symm (RationalFunctionField.placeOfPoint k (a i : k))).1)
      (M₁.placeEquiv.symm (RationalFunctionField.placeInfty k)).1 hεinf
      (fun p q h => (hinter p q h).imp fun _ hi => hi.1) hnodesU
  have htw₂ := eulerChar_pullback_secondLine_sectionTwist_eq_one c ε s U hεU M₂ i₂ hε₂ g
  obtain ⟨hp₁, hm₁⟩ := eulerChar_pullback_Mplus_Mminus c ε s U hεU L' g M₁ i₁ hDA₁ ((g : ℤ) + 1)
    (fun 𝒲' => by rw [htw₁ 𝒲'])
  obtain ⟨hp₂, hm₂⟩ := eulerChar_pullback_Mplus_Mminus c ε s U hεU L' g M₂ i₂ hDA₂ 1 htw₂
  refine ⟨fun 𝒲' => ?_, fun 𝒲' => ?_, fun 𝒲' => ?_, fun 𝒲' => ?_⟩
  · rw [hp₁ 𝒲']; ring
  · rw [hp₂ 𝒲']; ring
  · rw [hm₁ 𝒲']; ring
  · rw [hm₂ 𝒲']; ring

end AlgebraicGeometry.RelPicard.HCutDR

end

noncomputable section

namespace AlgebraicGeometry
p2m_export "AlgebraicGeometry" "SmoothOfRelativeDimension IsProper Scheme.Modules.pullback Scheme.Hom Scheme.Hom.preimage_inf Scheme.Hom.support_ker LocallyOfFiniteType Spec Scheme.IdealSheafData.range_subschemeι Spec.map Scheme Smooth IsOpenImmersion Scheme.IdealSheafData.support_top Flat IsClosedImmersion IsReduced IsSeparated Scheme.Modules.pullbackCongr Scheme.fromSpecResidueField_apply Scheme.Modules.pullbackId Scheme.Hom.preimage_sup Scheme.Modules IsAffineHom Scheme.Hom.comp_apply Scheme.IdealSheafData Scheme.Modules.pullbackComp Scheme.Modules.IsInvertible Scheme.Modules.isInvertible_unit RelPicard.IsAlgEquivZero Scheme.Modules.dual Scheme.IdealSheafData.module RelEffCartierDiv Scheme.TwoAffineOpenCover Scheme.TwoAffineOpenCover.specMap Scheme.TwoAffineOpenCover.algebraOfHom Scheme.TwoAffineOpenCover.moduleSectionsOfHom Scheme.IdealSheafData.isInvertible_top Scheme.TwoAffineOpenCover.exists_linearEquiv_sectionsOf_H0 Scheme.TwoAffineOpenCover.exists_isPullback_snd_specMap_algebraOfHom Scheme.Modules.exists_iso_pullback_of_isPullback Scheme.TwoAffineOpenCover.exists_linearEquiv_sectionsOf_of_iso Scheme.Modules.pullbackTensorObjIso Scheme.Modules.pullbackTensorUnitObjIso Scheme.TwoAffineOpenCover.finrank_H0_unit_fibre_eq_one_of_bijective_sections Scheme.Modules.nonempty_pullback_tensor_invModule_pow_tensor_module_iso_of_forall_notMem_support RelEffCartierDiv.empty RelEffCartierDiv.empty_I RelEffCartierDiv.I_eq_top_of_degree_zero graphOver TwoGluedProjectiveLines.isAlgEquivZero_of_pullback_iso_unit RelPicard.IsAlgEquivZero.nonempty_pullback_iso_pullback_unit_and_eulerChar_eq_one_of_curveModel_ratFunc TwoGluedProjectiveLines.nonempty_pullback_iso_unit_of_finrank_H0_twists_lt_two TwoGluedProjectiveLines.finrank_H0_twists_lt_two_of_nonempty_pullback_iso_unit Scheme.Modules.IsInvertible.eulerChar_sectionsOf_tensor_eq_add_sub Scheme.Modules.IsInvertible.eulerChar_sectionsOf_dual_eq Scheme.TwoAffineOpenCover.ext' Scheme.TwoAffineOpenCover.comapOfIsAffineHom'"
namespace RelPicard
p2m_export "AlgebraicGeometry.RelPicard" "baseChangeSnd rigSection RigidifiedLineBundle fibreAt IsAlgEquivZero sectionIdeal sectionTwist fibreModule isClosed_setOf_forall_fibre_le_finrank_H0_of_twoAffineOpenCover exists_twoAffineOpenCover_fibre_finrank_eq_finrank_cechDiff_baseChange_residueField isInvertible_sectionIdeal_of_range_subset forall_exists_twoAffineOpenCover_linearEquiv_sectionsOf_fibreModule nonempty_pullback_sectionTwist_iso_of_range_subset eulerChar_pullback_firstLine_sectionTwist_tensor_idealModule_eq sectionFibrePoint IsAlgEquivZero.nonempty_pullback_iso_pullback_unit_and_eulerChar_eq_one_of_curveModel_ratFunc"
namespace HCutDR
p2m_open "AlgebraicGeometry.RelPicard AlgebraicGeometry"

private def _root_.AlgebraicGeometry.Scheme.TwoAffineOpenCover.comapOfIsAffineHom'
    {X Y : Scheme.{u}} (𝒲 : Y.TwoAffineOpenCover) (f : X ⟶ Y) [IsAffineHom f] : X.TwoAffineOpenCover where
  U0 := f ⁻¹ᵁ 𝒲.U0
  U1 := f ⁻¹ᵁ 𝒲.U1
  isAffineOpen_U0 := 𝒲.isAffineOpen_U0.preimage f
  isAffineOpen_U1 := 𝒲.isAffineOpen_U1.preimage f
  sup_eq_top := by rw [← Scheme.Hom.preimage_sup, 𝒲.sup_eq_top]; rfl
  isAffineOpen_inf := by rw [← Scheme.Hom.preimage_inf]; exact 𝒲.isAffineOpen_inf.preimage f

p2m_alias "P2MW.S_AlgebraicGeometry_RelPicard_exists_isOpen_inter_preimage_eq_setOf_isAlgEquivZero_fibre_of_smoothLocus_of_twoLineDegenerations.AlgebraicGeometry.Scheme.TwoAffineOpenCover.comapOfIsAffineHom'" "AlgebraicGeometry.Scheme.TwoAffineOpenCover.comapOfIsAffineHom'"

theorem degAdd_ratFunc (k : Type u) [Field k] [IsAlgClosed k] (M : CurveModel k (RatFunc k)) :
    (∀ (A B : M.C.Modules), Scheme.Modules.IsInvertible A → Scheme.Modules.IsInvertible B →
      ∀ 𝒲 : M.C.TwoAffineOpenCover,
        ((Module.finrank k ↥(𝒲.sectionsOf M.toBase (A ⊗ B)).H0 : ℤ) - Module.finrank k (𝒲.sectionsOf M.toBase (A ⊗ B)).H1) = ((Module.finrank k ↥(𝒲.sectionsOf M.toBase A).H0 : ℤ) - Module.finrank k (𝒲.sectionsOf M.toBase A).H1) + ((Module.finrank k ↥(𝒲.sectionsOf M.toBase B).H0 : ℤ) - Module.finrank k (𝒲.sectionsOf M.toBase B).H1) - 1 ∧
        ((Module.finrank k ↥(𝒲.sectionsOf M.toBase (Scheme.Modules.dual A)).H0 : ℤ) - Module.finrank k (𝒲.sectionsOf M.toBase (Scheme.Modules.dual A)).H1) = 2 - ((Module.finrank k ↥(𝒲.sectionsOf M.toBase A).H0 : ℤ) - Module.finrank k (𝒲.sectionsOf M.toBase A).H1)) := by
  intro A B hA hB 𝒲
  obtain ⟨h1, h0⟩ := AlgebraicCurve.CurveModel.finrank_H1_sectionsOf_unit_eq_zero_and_finrank_H0_eq_one_of_ratFunc k M 𝒲
  have hT := AlgebraicGeometry.Scheme.Modules.IsInvertible.eulerChar_sectionsOf_tensor_eq_add_sub k M.toBase A B hA hB 𝒲
  have hD := AlgebraicGeometry.Scheme.Modules.IsInvertible.eulerChar_sectionsOf_dual_eq k M.toBase A hA 𝒲
  rw [h1, h0] at hT hD
  refine ⟨?_, ?_⟩
  · rw [hT]; push_cast; ring
  · rw [hD]; push_cast; ring

theorem handA_forward_X
    (R : Type u) [CommRing R] [IsNoetherianRing R]
    {C : Scheme.{u}} (c : C ⟶ Spec (CommRingCat.of R)) [IsProper c] [Flat c]
    (𝒱 : C.TwoAffineOpenCover)
    (hH0 : ∀ (A : Type u) [CommRing A] [Algebra R A],
      letI := Scheme.TwoAffineOpenCover.algebraOfHom
        (Limits.pullback.snd c (Scheme.TwoAffineOpenCover.specMap R A)) ⊤
      Function.Bijective (algebraMap A Γ(Limits.pullback c (Scheme.TwoAffineOpenCover.specMap R A), ⊤)))

    (U : C.Opens) [SmoothOfRelativeDimension 1 (U.ι ≫ c)]
    (ε : SchemeHomOver (𝟙 (Spec (CommRingCat.of R))) c) (hε : Set.range ε.1.base ⊆ (U : Set C))

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

    (hbad : ∀ (k : Type u) [Field k] [IsAlgClosed k] [DecidableEq (RatFunc k)]
      (s : Spec (CommRingCat.of k) ⟶ Spec (CommRingCat.of R)), ¬ Smooth (pullback.snd c s) →
      ∃ (M₁ M₂ : CurveModel k (RatFunc k)) (i₁ : M₁.C ⟶ pullback c s) (i₂ : M₂.C ⟶ pullback c s)
        (_ : IsClosedImmersion i₁) (_ : IsClosedImmersion i₂)
        (n : ℕ) (a b : Fin n → kˣ) (𝒲₀ : (pullback c s).TwoAffineOpenCover),
        i₁ ≫ pullback.snd c s = M₁.toBase ∧ i₂ ≫ pullback.snd c s = M₂.toBase ∧
        Set.range i₁.base ∪ Set.range i₂.base = Set.univ ∧
        Function.Injective a ∧
        (∀ i, i₁.base (M₁.placeEquiv.symm (RationalFunctionField.placeOfPoint k (a i : k))).1 =
          i₂.base (M₂.placeEquiv.symm (RationalFunctionField.placeOfPoint k (b i : k))).1) ∧
        (∀ (p : M₁.C) (q : M₂.C), i₁.base p = i₂.base q →
          ∃ i, p = (M₁.placeEquiv.symm (RationalFunctionField.placeOfPoint k (a i : k))).1 ∧
            q = (M₂.placeEquiv.symm (RationalFunctionField.placeOfPoint k (b i : k))).1) ∧
        IsReduced (pullback i₁ i₂) ∧
        ((i₁ ⁻¹ᵁ 𝒲₀.U0 : M₁.C.Opens) : Set M₁.C) =
          {(M₁.placeEquiv.symm (RationalFunctionField.placeInfty k)).1}ᶜ ∧
        ((i₂ ⁻¹ᵁ 𝒲₀.U0 : M₂.C.Opens) : Set M₂.C) =
          {(M₂.placeEquiv.symm (RationalFunctionField.placeInfty k)).1}ᶜ ∧
        ((i₁ ⁻¹ᵁ 𝒲₀.U1 : M₁.C.Opens) : Set M₁.C) =
          {(M₁.placeEquiv.symm (RationalFunctionField.placeOfPoint k 0)).1}ᶜ ∧
        ((i₂ ⁻¹ᵁ 𝒲₀.U1 : M₂.C.Opens) : Set M₂.C) =
          {(M₂.placeEquiv.symm (RationalFunctionField.placeOfPoint k 0)).1}ᶜ ∧
        i₁.base (M₁.placeEquiv.symm (RationalFunctionField.placeInfty k)).1 = ((sectionFibrePoint ε s).1).base (IsLocalRing.closedPoint k) ∧
        Set.range i₁.base ∩ ((pullback.fst c s ⁻¹ᵁ U : (pullback c s).Opens) : Set ↥(pullback c s)) =
          connectedComponentIn ((pullback.fst c s ⁻¹ᵁ U : (pullback c s).Opens) : Set ↥(pullback c s)) (((sectionFibrePoint ε s).1).base (IsLocalRing.closedPoint k)) ∧
        (∀ i, i₁.base (M₁.placeEquiv.symm (RationalFunctionField.placeOfPoint k (a i : k))).1 ∉
          (pullback.fst c s ⁻¹ᵁ U : (pullback c s).Opens)) ∧
        (∀ y : ↥(pullback c s),
          (∀ i, y ≠ i₁.base (M₁.placeEquiv.symm (RationalFunctionField.placeOfPoint k (a i : k))).1) →
            y ∈ (pullback.fst c s ⁻¹ᵁ U : (pullback c s).Opens)) ∧
        (∃ W₁ : (pullback c s).Opens, (W₁ : Set ↥(pullback c s)) = (Set.range i₂.base)ᶜ ∧
          IsOpenImmersion ((i₁ ⁻¹ᵁ W₁).ι ≫ i₁)))

    (Z₀ : Set ↥(Spec (CommRingCat.of R))) (hZ₀ : IsClosed Z₀)
    (hZ₀off : ∀ (k : Type u) [Field k] [IsAlgClosed k] (s : Spec (CommRingCat.of k) ⟶ Spec (CommRingCat.of R)),
      s.base (IsLocalRing.closedPoint k) ∉ Z₀ → Smooth (pullback.snd c s))
    (hZ₀on : ∀ (k : Type u) [Field k] [IsAlgClosed k] (s : Spec (CommRingCat.of k) ⟶ Spec (CommRingCat.of R)),
      s.base (IsLocalRing.closedPoint k) ∈ Z₀ → ¬ Smooth (pullback.snd c s))
    (k : Type u) [Field k] [IsAlgClosed k] (x : Spec (CommRingCat.of k) ⟶ Spec (CommRingCat.of R))
    (hxZ : x.base (IsLocalRing.closedPoint k) ∈ Z₀) (L' : RigidifiedLineBundle c ε x)
    (h0 : IsAlgEquivZero (pullback.snd c x) L'.L) :
    ∃ 𝒲 : (pullback c x).TwoAffineOpenCover,
      Module.finrank k (𝒲.sectionsOf (pullback.snd c x) (Mplus c x ε L' g)).H0 < 2 ∧
      Module.finrank k (𝒲.sectionsOf (pullback.snd c x) (Mminus c x ε L' g)).H0 < 2 := by
  classical
  have hns : ¬ Smooth (pullback.snd c x) := hZ₀on k x hxZ
  obtain ⟨M₁, M₂, i₁, i₂, hci₁, hci₂, n, a, b, 𝒲₀, hi₁, hi₂, hcover, ha, hnode, hinter, htrans, hU0₁, hU0₂, hU1₁, hU1₂, hεpt, hcomp, hnotU, hinU, hW₁⟩ := hbad k x hns
  haveI := hci₁
  haveI := hci₂
  haveI : IsReduced (pullback c x) := hgred k x
  have hLinv : Scheme.Modules.IsInvertible L'.L := L'.isInvertible
  have hH0X := finrank_H0_unit_eq_one_of_bijective_sections c x hH0 𝒲₀
  have hH1X := finrank_H1_unit_eq_of_fibreAt_id c x g (hg k x) 𝒲₀
  obtain ⟨hχp₁, hχp₂, hχm₁, hχm₂⟩ := chi_bookkeeping c ε U hε g k x M₁ M₂ i₁ i₂ n a b 𝒲₀ hi₁ hi₂ hcover ha hnode hinter htrans hU0₁ hU0₂ hU1₁ hU1₂ hεpt hcomp hnotU hinU hW₁ L' (degAdd_ratFunc k M₁) (degAdd_ratFunc k M₂)
  obtain ⟨h₁, -⟩ := AlgebraicGeometry.RelPicard.IsAlgEquivZero.nonempty_pullback_iso_pullback_unit_and_eulerChar_eq_one_of_curveModel_ratFunc
    k (pullback.snd c x) L'.L hLinv h0 M₁ i₁ hi₁ (𝒲₀.comapOfIsAffineHom' i₁)
    (fun 𝒲 => AlgebraicCurve.CurveModel.finrank_H1_sectionsOf_unit_eq_zero_and_finrank_H0_eq_one_of_ratFunc k M₁ 𝒲)
  obtain ⟨h₂, -⟩ := AlgebraicGeometry.RelPicard.IsAlgEquivZero.nonempty_pullback_iso_pullback_unit_and_eulerChar_eq_one_of_curveModel_ratFunc
    k (pullback.snd c x) L'.L hLinv h0 M₂ i₂ hi₂ (𝒲₀.comapOfIsAffineHom' i₂)
    (fun 𝒲 => AlgebraicCurve.CurveModel.finrank_H1_sectionsOf_unit_eq_zero_and_finrank_H0_eq_one_of_ratFunc k M₂ 𝒲)
  exact ⟨𝒲₀, AlgebraicGeometry.TwoGluedProjectiveLines.finrank_H0_twists_lt_two_of_nonempty_pullback_iso_unit k (pullback.snd c x) M₁ M₂ i₁ i₂ hi₁ hi₂ hcover a b ha hnode hinter htrans 𝒲₀
    hU0₁ hU0₂ hU1₁ hU1₂ g hH0X hH1X L'.L (Mplus c x ε L' g) (Mminus c x ε L' g) hLinv
    (isInvertible_Mplus c x ε U hε L' g) (isInvertible_Mminus c x ε U hε L' g) hχp₁ hχp₂ hχm₁ hχm₂ h₁ h₂⟩

theorem handA_backward_X
    (R : Type u) [CommRing R] [IsNoetherianRing R]
    {C : Scheme.{u}} (c : C ⟶ Spec (CommRingCat.of R)) [IsProper c] [Flat c]
    (𝒱 : C.TwoAffineOpenCover)
    (hH0 : ∀ (A : Type u) [CommRing A] [Algebra R A],
      letI := Scheme.TwoAffineOpenCover.algebraOfHom
        (Limits.pullback.snd c (Scheme.TwoAffineOpenCover.specMap R A)) ⊤
      Function.Bijective (algebraMap A Γ(Limits.pullback c (Scheme.TwoAffineOpenCover.specMap R A), ⊤)))

    (U : C.Opens) [SmoothOfRelativeDimension 1 (U.ι ≫ c)]
    (ε : SchemeHomOver (𝟙 (Spec (CommRingCat.of R))) c) (hε : Set.range ε.1.base ⊆ (U : Set C))

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

    (hbad : ∀ (k : Type u) [Field k] [IsAlgClosed k] [DecidableEq (RatFunc k)]
      (s : Spec (CommRingCat.of k) ⟶ Spec (CommRingCat.of R)), ¬ Smooth (pullback.snd c s) →
      ∃ (M₁ M₂ : CurveModel k (RatFunc k)) (i₁ : M₁.C ⟶ pullback c s) (i₂ : M₂.C ⟶ pullback c s)
        (_ : IsClosedImmersion i₁) (_ : IsClosedImmersion i₂)
        (n : ℕ) (a b : Fin n → kˣ) (𝒲₀ : (pullback c s).TwoAffineOpenCover),
        i₁ ≫ pullback.snd c s = M₁.toBase ∧ i₂ ≫ pullback.snd c s = M₂.toBase ∧
        Set.range i₁.base ∪ Set.range i₂.base = Set.univ ∧
        Function.Injective a ∧
        (∀ i, i₁.base (M₁.placeEquiv.symm (RationalFunctionField.placeOfPoint k (a i : k))).1 =
          i₂.base (M₂.placeEquiv.symm (RationalFunctionField.placeOfPoint k (b i : k))).1) ∧
        (∀ (p : M₁.C) (q : M₂.C), i₁.base p = i₂.base q →
          ∃ i, p = (M₁.placeEquiv.symm (RationalFunctionField.placeOfPoint k (a i : k))).1 ∧
            q = (M₂.placeEquiv.symm (RationalFunctionField.placeOfPoint k (b i : k))).1) ∧
        IsReduced (pullback i₁ i₂) ∧
        ((i₁ ⁻¹ᵁ 𝒲₀.U0 : M₁.C.Opens) : Set M₁.C) =
          {(M₁.placeEquiv.symm (RationalFunctionField.placeInfty k)).1}ᶜ ∧
        ((i₂ ⁻¹ᵁ 𝒲₀.U0 : M₂.C.Opens) : Set M₂.C) =
          {(M₂.placeEquiv.symm (RationalFunctionField.placeInfty k)).1}ᶜ ∧
        ((i₁ ⁻¹ᵁ 𝒲₀.U1 : M₁.C.Opens) : Set M₁.C) =
          {(M₁.placeEquiv.symm (RationalFunctionField.placeOfPoint k 0)).1}ᶜ ∧
        ((i₂ ⁻¹ᵁ 𝒲₀.U1 : M₂.C.Opens) : Set M₂.C) =
          {(M₂.placeEquiv.symm (RationalFunctionField.placeOfPoint k 0)).1}ᶜ ∧
        i₁.base (M₁.placeEquiv.symm (RationalFunctionField.placeInfty k)).1 = ((sectionFibrePoint ε s).1).base (IsLocalRing.closedPoint k) ∧
        Set.range i₁.base ∩ ((pullback.fst c s ⁻¹ᵁ U : (pullback c s).Opens) : Set ↥(pullback c s)) =
          connectedComponentIn ((pullback.fst c s ⁻¹ᵁ U : (pullback c s).Opens) : Set ↥(pullback c s)) (((sectionFibrePoint ε s).1).base (IsLocalRing.closedPoint k)) ∧
        (∀ i, i₁.base (M₁.placeEquiv.symm (RationalFunctionField.placeOfPoint k (a i : k))).1 ∉
          (pullback.fst c s ⁻¹ᵁ U : (pullback c s).Opens)) ∧
        (∀ y : ↥(pullback c s),
          (∀ i, y ≠ i₁.base (M₁.placeEquiv.symm (RationalFunctionField.placeOfPoint k (a i : k))).1) →
            y ∈ (pullback.fst c s ⁻¹ᵁ U : (pullback c s).Opens)) ∧
        (∃ W₁ : (pullback c s).Opens, (W₁ : Set ↥(pullback c s)) = (Set.range i₂.base)ᶜ ∧
          IsOpenImmersion ((i₁ ⁻¹ᵁ W₁).ι ≫ i₁)))

    (Z₀ : Set ↥(Spec (CommRingCat.of R))) (hZ₀ : IsClosed Z₀)
    (hZ₀off : ∀ (k : Type u) [Field k] [IsAlgClosed k] (s : Spec (CommRingCat.of k) ⟶ Spec (CommRingCat.of R)),
      s.base (IsLocalRing.closedPoint k) ∉ Z₀ → Smooth (pullback.snd c s))
    (hZ₀on : ∀ (k : Type u) [Field k] [IsAlgClosed k] (s : Spec (CommRingCat.of k) ⟶ Spec (CommRingCat.of R)),
      s.base (IsLocalRing.closedPoint k) ∈ Z₀ → ¬ Smooth (pullback.snd c s))
    (k : Type u) [Field k] [IsAlgClosed k] (x : Spec (CommRingCat.of k) ⟶ Spec (CommRingCat.of R))
    (hxZ : x.base (IsLocalRing.closedPoint k) ∈ Z₀) (L' : RigidifiedLineBundle c ε x)
    (hnum : ∀ 𝒲 : (pullback c x).TwoAffineOpenCover,
      Module.finrank k (𝒲.sectionsOf (pullback.snd c x) (Mplus c x ε L' g)).H0 < 2 ∧
      Module.finrank k (𝒲.sectionsOf (pullback.snd c x) (Mminus c x ε L' g)).H0 < 2) :
    IsAlgEquivZero (pullback.snd c x) L'.L := by
  classical
  have hns : ¬ Smooth (pullback.snd c x) := hZ₀on k x hxZ
  obtain ⟨M₁, M₂, i₁, i₂, hci₁, hci₂, n, a, b, 𝒲₀, hi₁, hi₂, hcover, ha, hnode, hinter, htrans, hU0₁, hU0₂, hU1₁, hU1₂, hεpt, hcomp, hnotU, hinU, hW₁⟩ := hbad k x hns
  haveI := hci₁
  haveI := hci₂
  haveI : IsReduced (pullback c x) := hgred k x
  have hLinv : Scheme.Modules.IsInvertible L'.L := L'.isInvertible
  have hH0X := finrank_H0_unit_eq_one_of_bijective_sections c x hH0 𝒲₀
  have hH1X := finrank_H1_unit_eq_of_fibreAt_id c x g (hg k x) 𝒲₀
  obtain ⟨hχp₁, hχp₂, hχm₁, hχm₂⟩ := chi_bookkeeping c ε U hε g k x M₁ M₂ i₁ i₂ n a b 𝒲₀ hi₁ hi₂ hcover ha hnode hinter htrans hU0₁ hU0₂ hU1₁ hU1₂ hεpt hcomp hnotU hinU hW₁ L' (degAdd_ratFunc k M₁) (degAdd_ratFunc k M₂)
  obtain ⟨h₁, h₂⟩ := AlgebraicGeometry.TwoGluedProjectiveLines.nonempty_pullback_iso_unit_of_finrank_H0_twists_lt_two k (pullback.snd c x) M₁ M₂ i₁ i₂ hi₁ hi₂ hcover a b ha hnode hinter htrans 𝒲₀
    hU0₁ hU0₂ hU1₁ hU1₂ g hH0X hH1X L'.L (Mplus c x ε L' g) (Mminus c x ε L' g) hLinv
    (isInvertible_Mplus c x ε U hε L' g) (isInvertible_Mminus c x ε U hε L' g) hχp₁ hχp₂ hχm₁ hχm₂ (hnum 𝒲₀).1 (hnum 𝒲₀).2
  exact AlgebraicGeometry.TwoGluedProjectiveLines.isAlgEquivZero_of_pullback_iso_unit k (pullback.snd c x) M₁ M₂ i₁ i₂
    hi₁ hi₂ hcover a b ha hnode hinter htrans L'.L hLinv h₁ h₂

end AlgebraicGeometry.RelPicard.HCutDR

theorem solution
    (R : Type u) [CommRing R] [IsNoetherianRing R]
    {C : Scheme.{u}} (c : C ⟶ Spec (CommRingCat.of R)) [IsProper c] [Flat c]
    (𝒱 : C.TwoAffineOpenCover)
    (hH0 : ∀ (A : Type u) [CommRing A] [Algebra R A],
      letI := Scheme.TwoAffineOpenCover.algebraOfHom
        (Limits.pullback.snd c (Scheme.TwoAffineOpenCover.specMap R A)) ⊤
      Function.Bijective (algebraMap A Γ(Limits.pullback c (Scheme.TwoAffineOpenCover.specMap R A), ⊤)))

    (U : C.Opens) [SmoothOfRelativeDimension 1 (U.ι ≫ c)]
    (ε : SchemeHomOver (𝟙 (Spec (CommRingCat.of R))) c) (hε : Set.range ε.1.base ⊆ (U : Set C))

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

    (hbad : ∀ (k : Type u) [Field k] [IsAlgClosed k] [DecidableEq (RatFunc k)]
      (s : Spec (CommRingCat.of k) ⟶ Spec (CommRingCat.of R)), ¬ Smooth (pullback.snd c s) →
      ∃ (M₁ M₂ : CurveModel k (RatFunc k)) (i₁ : M₁.C ⟶ pullback c s) (i₂ : M₂.C ⟶ pullback c s)
        (_ : IsClosedImmersion i₁) (_ : IsClosedImmersion i₂)
        (n : ℕ) (a b : Fin n → kˣ) (𝒲₀ : (pullback c s).TwoAffineOpenCover),
        i₁ ≫ pullback.snd c s = M₁.toBase ∧ i₂ ≫ pullback.snd c s = M₂.toBase ∧
        Set.range i₁.base ∪ Set.range i₂.base = Set.univ ∧
        Function.Injective a ∧
        (∀ i, i₁.base (M₁.placeEquiv.symm (RationalFunctionField.placeOfPoint k (a i : k))).1 =
          i₂.base (M₂.placeEquiv.symm (RationalFunctionField.placeOfPoint k (b i : k))).1) ∧
        (∀ (p : M₁.C) (q : M₂.C), i₁.base p = i₂.base q →
          ∃ i, p = (M₁.placeEquiv.symm (RationalFunctionField.placeOfPoint k (a i : k))).1 ∧
            q = (M₂.placeEquiv.symm (RationalFunctionField.placeOfPoint k (b i : k))).1) ∧
        IsReduced (pullback i₁ i₂) ∧
        ((i₁ ⁻¹ᵁ 𝒲₀.U0 : M₁.C.Opens) : Set M₁.C) =
          {(M₁.placeEquiv.symm (RationalFunctionField.placeInfty k)).1}ᶜ ∧
        ((i₂ ⁻¹ᵁ 𝒲₀.U0 : M₂.C.Opens) : Set M₂.C) =
          {(M₂.placeEquiv.symm (RationalFunctionField.placeInfty k)).1}ᶜ ∧
        ((i₁ ⁻¹ᵁ 𝒲₀.U1 : M₁.C.Opens) : Set M₁.C) =
          {(M₁.placeEquiv.symm (RationalFunctionField.placeOfPoint k 0)).1}ᶜ ∧
        ((i₂ ⁻¹ᵁ 𝒲₀.U1 : M₂.C.Opens) : Set M₂.C) =
          {(M₂.placeEquiv.symm (RationalFunctionField.placeOfPoint k 0)).1}ᶜ ∧
        i₁.base (M₁.placeEquiv.symm (RationalFunctionField.placeInfty k)).1 = ((sectionFibrePoint ε s).1).base (IsLocalRing.closedPoint k) ∧
        Set.range i₁.base ∩ ((pullback.fst c s ⁻¹ᵁ U : (pullback c s).Opens) : Set ↥(pullback c s)) =
          connectedComponentIn ((pullback.fst c s ⁻¹ᵁ U : (pullback c s).Opens) : Set ↥(pullback c s)) (((sectionFibrePoint ε s).1).base (IsLocalRing.closedPoint k)) ∧
        (∀ i, i₁.base (M₁.placeEquiv.symm (RationalFunctionField.placeOfPoint k (a i : k))).1 ∉
          (pullback.fst c s ⁻¹ᵁ U : (pullback c s).Opens)) ∧
        (∀ y : ↥(pullback c s),
          (∀ i, y ≠ i₁.base (M₁.placeEquiv.symm (RationalFunctionField.placeOfPoint k (a i : k))).1) →
            y ∈ (pullback.fst c s ⁻¹ᵁ U : (pullback c s).Opens)) ∧
        (∃ W₁ : (pullback c s).Opens, (W₁ : Set ↥(pullback c s)) = (Set.range i₂.base)ᶜ ∧
          IsOpenImmersion ((i₁ ⁻¹ᵁ W₁).ι ≫ i₁)))

    (Z₀ : Set ↥(Spec (CommRingCat.of R))) (hZ₀ : IsClosed Z₀)
    (hZ₀off : ∀ (k : Type u) [Field k] [IsAlgClosed k] (s : Spec (CommRingCat.of k) ⟶ Spec (CommRingCat.of R)),
      s.base (IsLocalRing.closedPoint k) ∉ Z₀ → Smooth (pullback.snd c s))
    (hZ₀on : ∀ (k : Type u) [Field k] [IsAlgClosed k] (s : Spec (CommRingCat.of k) ⟶ Spec (CommRingCat.of R)),
      s.base (IsLocalRing.closedPoint k) ∈ Z₀ → ¬ Smooth (pullback.snd c s)) :
    ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) [LocallyOfFiniteType t]
      (L : RigidifiedLineBundle c ε t), ∃ W : Set ↥T, IsOpen W ∧
        W ∩ (⇑t) ⁻¹' Z₀ = {x : ↥T | t x ∈ Z₀ ∧ ∀ (k : Type u) [Field k] [IsAlgClosed k] (s : Spec (CommRingCat.of k) ⟶ T),
          Set.range ⇑s ⊆ {x} → IsAlgEquivZero (fibreAt c t s) (fibreModule c t s L.L)} := by
  intro T t _ L
  exact AlgebraicGeometry.RelPicard.HCutDR.exists_isOpen_inter_preimage_eq_setOf_isAlgEquivZero_of_handA_baseChange
    c t ε 𝒱 U hε L Z₀ g 2
    (fun k _ _ x hx L' h0 => AlgebraicGeometry.RelPicard.HCutDR.handA_forward_X R c 𝒱 hH0 U ε hε hgoodU hgred g hg hbad
      Z₀ hZ₀ hZ₀off hZ₀on k x hx L' h0)
    (fun k _ _ x hx L' hnum => AlgebraicGeometry.RelPicard.HCutDR.handA_backward_X R c 𝒱 hH0 U ε hε hgoodU hgred g hg hbad
      Z₀ hZ₀ hZ₀off hZ₀on k x hx L' hnum)

end

end S_AlgebraicGeometry_RelPicard_exists_isOpen_inter_preimage_eq_setOf_isAlgEquivZero_fibre_of_smoothLocus_of_twoLineDegenerations
end P2MW
export P2MW.S_AlgebraicGeometry_RelPicard_exists_isOpen_inter_preimage_eq_setOf_isAlgEquivZero_fibre_of_smoothLocus_of_twoLineDegenerations (solution)
