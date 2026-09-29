-- Prove2me | solution 1 for AlgebraicGeometry.RelPicard.surjective_of_poincare_pullbackAlong_iso_twistModule
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:03.589526+00:00
-- url     : https://prove2.me/submissions/82fee410-68c7-532b-bee7-02956b154211

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
import Definitions.Def_AlgebraicGeometry_RelEffCartierDiv
import Definitions.Def_AlgebraicGeometry_RelEffCartierDivFunctor
import Definitions.Def_AlgebraicGeometry_RelEffCartierDivTwist2
import Definitions.Def_AlgebraicGeometry_TwoAffineOpenCover
import Definitions.Def_AlgebraicGeometry_TwoChartCechSectionsOf
import Definitions.Def_AlgebraicGeometry_IdealSheafModule
import Definitions.Def_AlgebraicGeometry_RelEffCartierDivSum
import Definitions.Def_AlgebraicGeometry_RelEffCartierDivOfPoint
import Definitions.Def_AlgebraicGeometry_ModulesRigidify
import Definitions.Def_AlgebraicGeometry_RigidifiedLineBundleOfInvertible
import Definitions.Def_AlgebraicGeometry_ModulesPullbackMonoidal
import Definitions.Def_AlgebraicGeometry_RelPicardAbelJacobiFamily
import Theorems.Thm_AlgebraicGeometry_RelPicard_isAlgEquivZero_iff_eulerChar_sectionsOf_eq
import Theorems.Thm_AlgebraicGeometry_Scheme_TwoAffineOpenCover_finrank_H1_sectionsOf_unit_eq_and_finrank_H0_eq_one
import Theorems.Thm_AlgebraicGeometry_RelEffCartierDiv_exists_I_eq_prodKerGraph
import Theorems.Thm_AlgebraicGeometry_RelEffCartierDiv_eulerChar_tensor_lineBundle_eq
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_IsInvertible_nontrivial_H0_sectionsOf_of_le_eulerChar_sub
import Theorems.Thm_AlgebraicGeometry_Scheme_TwoAffineOpenCover_exists_linearEquiv_sectionsOf_H0
import Theorems.Thm_AlgebraicGeometry_RelEffCartierDiv_exists_I_eq_zeroSchemeIdeal_of_eulerChar_eq
import Theorems.Thm_AlgebraicGeometry_RelEffCartierDiv_nonempty_twistModule_pullbackAlong_iso_pullback
import Theorems.Thm_AlgebraicGeometry_RelEffCartierDiv_isInvertible_I
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_IsInvertible_tensor
import Theorems.Thm_AlgebraicGeometry_Scheme_IdealSheafData_IsInvertible_isInvertible_invModule
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_RelPicard_surjective_of_poincare_pullbackAlong_iso_twistModule
p2m_attr_erase "instance" "AlgebraicCurve.IsCurveOver.instNontrivialKaehler AlgebraicCurve.IsCurveOver.instFreeKaehler AlgebraicCurve.IsCurveOver.toHasPrincipalDivisors AlgebraicCurve.IsCurveOver.instFiniteResidue AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.instFundamentalIdentityOfSumRamificationInertia AlgebraicCurve.Place.instIsScalarTowerResidueFieldRestrictPushforward AlgebraicCurve.Place.instAlgebraResidueFieldRestrictPushforward AlgebraicCurve.Place.instIsLocalHomRestrictInclusion AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.SemilinearAut.instDistribMulActionSubtypeProdRingAutMemSubgroupPic0 AlgebraicCurve.SemilinearAut.instDistribMulActionSubtypeProdRingAutMemSubgroupDivisor AlgebraicCurve.Pic0.instModuleZModTorsion AlgebraicCurve.SemilinearAut.instSMulSubtypeProdRingAutMemSubgroupPlace AlgebraicCurve.SemilinearAut.instDistribMulActionTorsion AlgebraicCurve.SemilinearAut.instSMulSubtypeProdRingAutMemSubgroupPic0 AlgebraicCurve.SemilinearAut.instSMulTorsion AlgebraicCurve.SemilinearAut.instMulActionSubtypeProdRingAutMemSubgroupPlace AlgebraicCurve.SemilinearAut.instSMulCommClassZModTorsion AlgebraicCurve.SemilinearAut.instMulSemiringActionSubtypeProdRingAutMemSubgroup instDecEqAlgebraicClosureRat WeierstrassCurve.Affine.Point.instDistribMulActionAlgEquiv WeierstrassCurve.Affine.Point.instModuleZModTorsionBy WeierstrassCurve.Affine.Point.instSMulTorsionBy WeierstrassCurve.Affine.Point.instDistribMulActionTorsionBy WeierstrassCurve.Affine.Point.instSMulAlgEquiv WeierstrassCurve.Affine.Point.instSMulCommClassAlgEquivZModTorsionBy AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions AlgebraicCurve.instHasLocalResidue_of_hasCanonicalLocalResidueK AlgebraicCurve.instHasCanonicalLocalResidueK_of_hasCanonicalLocalResidueKStar AlgebraicCurve.Place.kw_ffgc_finiteDimensional_adicCompletion instAlgebraSubtypeMemValuationSubring_definitions AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersIntegersCompletion ModularCurve.KwF4gRRTate.instAlgebraKAdicCompletionIntegers AlgebraicCurve.Place.kw_ffgc_continuousSMul_adicCompletionComap"
p2m_attr_erase "instance" "AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersCompletionCompletion IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions AlgebraicCurve.instHasCanonicalLocalResidueK AlgebraicCurve.Place.instAlgebra_restrictResidueField AlgebraicCurve.Place.instIsScalarTower_restrictResidueField AlgebraicCurve.instHasLocalResidue AlgebraicCurve.HasSeparableResidue.of_perfectField_of_isCurveOver AlgebraicCurve.HasSeparableResidue.of_perfectField AlgebraicCurve.Place.instIsLocalHom_restrictSubringHom AlgebraicCurve.instHasCanonicalLocalResidueKStar ModularCurve.KwNo6Pin.isLocalRing_completion SheafOfModules.isIso_ihomModelToIhom AlgebraicGeometry.OModulePresheaf.isScalarTower AlgebraicGeometry.Scheme.OrderedAffineCover.instLinearOrder AlgebraicGeometry.OModulePresheaf.module AlgebraicGeometry.Scheme.OrderedAffineCover.instFintype AlgebraicGeometry.Scheme.OrderedAffineCover.instFintypeIdx AlgebraicGeometry.OModulePresheaf.addCommGroup AlgebraicGeometry.Scheme.OrderedAffineCover.instDecidableEqIdx AlgebraicGeometry.OModulePresheaf.moduleSections AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instDecidableEqIdx AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instFintype AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instLinearOrder AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instFintypeIdx AlgebraicGeometry.OModulePresheaf.instSubsingletonObjZero AlgebraicGeometry.OModulePresheaf.Leray.relAltC_scalarTower AlgebraicGeometry.OModulePresheaf.Leray.ker_relAltd_modΓ AlgebraicGeometry.OModulePresheaf.Leray.relAltC_modΓ AlgebraicGeometry.OModulePresheaf.Leray.biC_abGrp AlgebraicGeometry.OModulePresheaf.Leray.relAltH_modΓ AlgebraicGeometry.OModulePresheaf.Leray.ker_relAltd_smul AlgebraicGeometry.OModulePresheaf.Leray.relAltH_scalarTower AlgebraicGeometry.OModulePresheaf.Leray.relAltH_smul AlgebraicGeometry.OModulePresheaf.Leray.biC_module DoubleComplex.instModuleE₂I"
p2m_attr_erase "instance" "DoubleComplex.Bounded.modR DoubleComplex.instModuleE₂II DoubleComplex.instAddCommGroupE₂II DoubleComplex.Bounded.abGrp DoubleComplex.instAddCommGroupE₂I AlgebraicGeometry.ChowDatum.hι_closed AlgebraicGeometry.ChowDatumProj.hιN_closed AlgebraicGeometry.ChowDatumProj.hp_proper AlgebraicGeometry.ChowDatum.hp_isoU AlgebraicGeometry.ChowDatum.hp_proper AlgebraicGeometry.ProjSpace.algebraAway AlgebraicGeometry.ProjSpace.instIsProperProdOverπ AlgebraicGeometry.ChowDatumProj.hp_isoU AlgebraicGeometry.ProjSpace.isProper_π AlgebraicGeometry.ProjSpace.finiteType_mvPolynomial ProjSpaceCech.GradedModule.H.module ProjSpaceCech.GradedModule.H.addCommGroup ProjSpaceCech.GradedModule.sec.instAdd ProjSpaceCech.GradedModule.sec.instNeg ProjSpaceCech.GradedModule.acg ProjSpaceCech.GradedModule.Frac.setoid ProjSpaceCech.GradedModule.modR ProjSpaceCech.GradedModule.sec.instModule ProjSpaceCech.GradedModule.sec.instAddCommGroup ProjSpaceCech.GradedModule.sec.instZero ProjSpaceCech.GradedModule.Presentation.fJ ProjSpaceCech.GradedModule.sec.instSMul ProjSpaceCech.Twist.H.module ProjSpaceCech.Idx.instFintype ProjSpaceCech.Twist.H.addCommGroup ProjSpaceCech.Idx.instDecidableEq ProjSpaceCech.Twist.Mon.instDecidableEq ProjSpaceCech.Twist.cochain.instAddCommGroup ProjSpaceCech.Twist.cochain.instModule AlgebraicGeometry.SmoothOfRelativeDimension.fiberToSpecResidueField AlgebraicGeometry.SmoothOfRelativeDimension.pullback_snd AlgebraicGeometry.SmoothOfRelativeDimension.pullback_fst AlgebraicGeometry.SmoothOfRelativeDimension.smooth_one AlgebraicGeometry.SmoothProperCurve.isIntegral_pullback_Spec_field AlgebraicGeometry.IsProper.fiberToSpecResidueField"
p2m_attr_erase "simp" "AlgebraicCurve.coe_cechH0Equiv_apply AlgebraicCurve.cechH1ToH1_mk AlgebraicCurve.lSpaceOn_univ AlgebraicCurve.lSpaceOn_empty AlgebraicCurve.Place.congrEquiv_symm_apply AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply AlgebraicCurve.RationalFunctionField.deg_placeOfPoint AlgebraicCurve.Divisor.mapRestrict_single AlgebraicCurve.Divisor.pushforward_single AlgebraicCurve.Place.coe_restrictInclusion AlgebraicCurve.Place.mem_fiber AlgebraicCurve.Place.restrict_toValuationSubring AlgebraicCurve.Divisor.degree_pushforward AlgebraicCurve.Place.restrictResidueMap_residue AlgebraicCurve.Pic0.coe_pushforwardDegZeroHom AlgebraicCurve.Pic0.coe_pullbackDegZeroHom AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal AlgebraicCurve.IsFrobeniusEndo.frobNormRingHom_apply ModularCurve.frobeniusPushforwardGeomLevelPic0_mk ModularCurve.coe_frobeniusGeomLevelEquiv_apply ModularCurve.coe_frobeniusPushforwardGeomLevelDegZero ModularCurve.heckeFibreGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusGeomLevel_apply_coe ModularCurve.frobeniusPullbackGeomLevelPic0OfIsCurveOver_mk ModularCurve.coe_heckeFibreGeomLevelDegZero ModularCurve.coe_frobeniusPullbackGeomLevelDegZero ModularCurve.frobeniusPullbackGeomLevelPic0_mk ModularCurve.frobeniusPullbackGeomLevel_single ModularCurve.heckeFibreGeomLevelPic0_mk ModularCurve.frobeniusPushforwardGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusPushforwardGeomLevel_single ModularCurve.qExpandAlgC_apply AlgebraicCurve.Divisor.degree_pushforwardAlong"
p2m_attr_erase "simp" "AlgebraicCurve.Pic0.coe_degZeroCorrespondence AlgebraicCurve.Place.mem_fiberAlong AlgebraicCurve.SemilinearAut.toRingAut_inv AlgebraicCurve.SemilinearAut.smul_def AlgebraicCurve.SemilinearAut.smul_single AlgebraicCurve.SemilinearAut.smul_toValuationSubring AlgebraicCurve.SemilinearAut.baseAut_inv AlgebraicCurve.SemilinearAut.baseAut_ofAlgAut AlgebraicCurve.SemilinearAut.toRingAut_ofAlgAut AlgebraicCurve.SemilinearAut.torsionRep_apply AlgebraicCurve.SemilinearAut.toRingAut_one AlgebraicCurve.SemilinearAut.deg_smul AlgebraicCurve.SemilinearAut.degree_smul AlgebraicCurve.SemilinearAut.coe_degZeroSMulHom AlgebraicCurve.SemilinearAut.baseAut_mul AlgebraicCurve.SemilinearAut.coe_smulValuationSubringEquiv_apply AlgebraicCurve.SemilinearAut.baseAut_one AlgebraicCurve.SemilinearAut.ofAlgAut_smul AlgebraicCurve.SemilinearAut.coe_torsion_smul AlgebraicCurve.SemilinearAut.toRingAut_mul AlgebraicCurve.coe_frobeniusPushforwardDegZero AlgebraicCurve.IsFrobeniusEndo.coe_frobeniusPullbackDegZero ModularCurve.jqNModC_one ModularCurve.qExpand_coeff_mul ModularCurve.qExpandₐ_apply ModularCurve.jqN_one ModularCurve.qExpand_single ModularCurve.dedekindPsi_one ModularCurve.ModularPolynomialData.mk.sizeOf_spec ModularCurve.evalAtJ_X ModularCurve.ModularPolynomialData.mk.injEq ModularCurve.constantCoeff_jNum ModularCurve.constantCoeff_eisenstein4 ModularCurve.qExpand_C ModularCurve.coeff_jq_neg_one ModularCurve.constantCoeff_jNumQ ModularCurve.reduceModBivar_C_X ModularCurve.laurentMap_coeff ModularCurve.reduceModBivar_X ModularCurve.laurentMap_single"
p2m_attr_erase "simp" "ModularCurve.evalAtJInt_X ModularCurve.evalAtJMod_X ModularCurve.jqNMod_one ModularCurve.aeval_heckeGen ModularCurve.coe_mTorsionGaloisRep_apply ModularCurve.eisensteinSystem_of_dvd ModularCurve.eisensteinSystem_of_not_dvd FreyPackage.mk.sizeOf_spec FreyPackage.mk.injEq WeierstrassCurve.Affine.Point.galoisRepModuleEnd_apply AlgebraicCurve.RationalFunctionField.placeInfty_toValuationSubring AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none AlgebraicCurve.Divisor.evalFun_zero AlgebraicCurve.Place.evalAt_one AlgebraicCurve.Place.differentialCoeff_zero AlgebraicCurve.Place.differentialCoeff_dCoord AlgebraicCurve.TranscendenceTower.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.injEq AlgebraicCurve.TranscendenceTower.mk.injEq AlgebraicCurve.PoleDivisorPackage.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.sizeOf_spec AlgebraicCurve.PoleDivisorPackage.mk.injEq AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.sizeOf_spec AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.injEq AlgebraicCurve.adeleSingle_coe AlgebraicCurve.kaehlerResidueTermKFam_apply AlgebraicCurve.Place.LocalResidueData.mk.injEq AlgebraicCurve.Place.LocalResidueData.mk.sizeOf_spec AlgebraicCurve.Place.kw_ffgc_adicCompletionComapIntegers_coe AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.sizeOf_spec AlgebraicCurve.Place.mem_simplePoleSubmodule AlgebraicCurve.Place.coe_uniformizerSubring ModularCurve.Lg37.Lg37CompletionSection.mk.injEq AlgebraicCurve.Place.CoefficientFieldSection.mk.injEq AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.injEq ModularCurve.Lg37.Lg37CompletionSection.mk.sizeOf_spec AlgebraicCurve.Place.CoefficientFieldSection.mk.sizeOf_spec"
p2m_attr_erase "simp" "AlgebraicCurve.Place.poleSubmodule_one AlgebraicCurve.Place.mem_poleSubmodule PresheafOfModules.InternalHom.IsSheafAux.appAt_toPresheafHom SheafOfModules.ihomSectionsEquivFamily_unit AlgebraicGeometry.Scheme.Modules.restrictHomEquivFamily_apply SheafOfModules.ihomEval_unit_app AlgebraicGeometry.Scheme.Modules.ihomEval_zero_right AlgebraicGeometry.Scheme.Modules.ihomEval_zero_left AlgebraicGeometry.Scheme.Modules.homOfFamily_app_apply SheafOfModules.unit_ihomSectionsEquivFamily AlgebraicGeometry.Scheme.Modules.familyOfHom_app AlgebraicGeometry.Scheme.Modules.restrictUnitIso_hom_app_apply AlgebraicGeometry.Scheme.Modules.restrictUnitIso_inv_app_apply AlgebraicGeometry.Scheme.Modules.restrictHomOfFamily_app_apply AlgebraicGeometry.Scheme.Modules.restrictHomEquivFamily_symm_apply AlgebraicGeometry.Scheme.Modules.tensorSections_zero_right AlgebraicGeometry.Scheme.Modules.map_unitSection AlgebraicGeometry.Scheme.Modules.tensorSectionsBilin_apply AlgebraicGeometry.Scheme.Modules.tensorPowSection_zero AlgebraicGeometry.Scheme.Modules.tensorSections_zero_left AlgebraicGeometry.Scheme.Modules.tensorPow_zero AlgebraicGeometry.Scheme.Modules.tensorPow_succ AlgebraicGeometry.Scheme.OrderedAffineCover.mk.injEq AlgebraicGeometry.OModulePresheaf.mk.sizeOf_spec AlgebraicGeometry.Scheme.OrderedAffineCover.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.mk.injEq AlgebraicGeometry.Scheme.Modules.pullbackLocalSection_neg AlgebraicGeometry.Scheme.Modules.pullbackLocalSection_zero AlgebraicGeometry.Scheme.Modules.pullbackLocalSection_sub AlgebraicGeometry.Scheme.Modules.pullbackLocalSection_add AlgebraicGeometry.Scheme.OrderedAffineCover.toCoverOf_U AlgebraicGeometry.Scheme.OrderedAffineCoverOf.mk.sizeOf_spec AlgebraicGeometry.Scheme.OrderedAffineCoverOf.mk.injEq AlgebraicGeometry.Scheme.OrderedAffineCover.restrict_U AlgebraicGeometry.OModulePresheaf.Hom.mk.injEq AlgebraicGeometry.OModulePresheaf.Hom.id_app AlgebraicGeometry.OModulePresheaf.AffHom.appSections_apply AlgebraicGeometry.OModulePresheaf.AffHom.comp_app AlgebraicGeometry.OModulePresheaf.AffSES.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.AffHom.kerMap_coe"
p2m_attr_erase "simp" "AlgebraicGeometry.OModulePresheaf.AffHom.id_app AlgebraicGeometry.OModulePresheaf.Hom.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.Hom.toAffHom_app AlgebraicGeometry.OModulePresheaf.SES.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.AffHom.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.Hom.comp_app AlgebraicGeometry.OModulePresheaf.SES.mk.injEq AlgebraicGeometry.OModulePresheaf.AffHom.mk.injEq AlgebraicGeometry.OModulePresheaf.Hom.appSections_apply AlgebraicGeometry.OModulePresheaf.AffSES.mk.injEq AlgebraicGeometry.OModulePresheaf.prod_obj AlgebraicGeometry.OModulePresheaf.restrOpen_obj AlgebraicGeometry.OModulePresheaf.DevissageStep.mk.injEq AlgebraicGeometry.OModulePresheaf.pushforward_obj AlgebraicGeometry.OModulePresheaf.im_obj AlgebraicGeometry.OModulePresheaf.pow_obj AlgebraicGeometry.OModulePresheaf.fstHom_app AlgebraicGeometry.OModulePresheaf.ker_obj AlgebraicGeometry.OModulePresheaf.coker_obj AlgebraicGeometry.OModulePresheaf.DevissageStep.mk.sizeOf_spec AlgebraicGeometry.Scheme.OrderedAffineCover.preimage_U AlgebraicGeometry.OModulePresheaf.sndHom_app AlgebraicGeometry.OModulePresheaf.Leray.restrictToPreimage_U DoubleComplex.Bounded.mk.injEq DoubleComplex.Bounded.mk.sizeOf_spec DoubleComplex.Convergence.mk.injEq DoubleComplex.Convergence.mk.sizeOf_spec DoubleComplex.SubQuot.mk.sizeOf_spec DoubleComplex.SubQuot.mk.injEq AlgebraicGeometry.ChowDatumProj.mk.sizeOf_spec AlgebraicGeometry.ChowDatum.mk.sizeOf_spec AlgebraicGeometry.ChowDatumProj.mk.injEq AlgebraicGeometry.ChowDatum.mk.injEq ProjSpaceCech.GradedModule.mk.injEq ProjSpaceCech.GradedModule.mk.sizeOf_spec ProjSpaceCech.GradedModule.Frac.mk.sizeOf_spec ProjSpaceCech.GradedModule.Presentation.mk.injEq ProjSpaceCech.GradedModule.Frac.mk.injEq ProjSpaceCech.GradedModule.Presentation.mk.sizeOf_spec ProjSpaceCech.GradedModule.Hom.shift_toLinearMap"
p2m_attr_erase "simp" "ProjSpaceCech.GradedModule.Hom.mk.sizeOf_spec ProjSpaceCech.GradedModule.Hom.mk.injEq TwoChartCech.Mumford.dK_apply TwoChartCech.Mumford.ι0_apply TwoChartCech.Mumford.ι1_apply TwoChartCech.KerCoprod.dK_apply TwoChartCech.KerCoprod.ι1_apply TwoChartCech.KerCoprod.ι0_apply AlgebraicGeometry.tilde.functorCompPullbackSpecIso_app AlgebraicGeometry.RelPicard.algEquivZeroGroupCut_toSubPicCondition AlgebraicGeometry.SmoothProperCurve.sectionBaseChange_coe_snd AlgebraicGeometry.SmoothProperCurve.sectionBaseChange_coe_fst"

set_option autoImplicit false
set_option maxHeartbeats 800000

universe u

p2m_open "CategoryTheory CategoryTheory.Limits AlgebraicGeometry P2MW.S_AlgebraicGeometry_RelPicard_surjective_of_poincare_pullbackAlong_iso_twistModule.AlgebraicGeometry AlgebraicGeometry.RelPicard P2MW.S_AlgebraicGeometry_RelPicard_surjective_of_poincare_pullbackAlong_iso_twistModule.AlgebraicGeometry.RelPicard NeronModelInfra GoodReductionJacobian AlgebraicCurve CategoryTheory.MonoidalCategory Opposite"

namespace AlgebraicGeometry
p2m_export "AlgebraicGeometry" "Spec.map_preimage Surjective Scheme.Modules.Hom.zero_app SmoothOfRelativeDimension IsProper Scheme.Modules.pullback GeometricallyIntegral.geometrically_isIntegral Scheme.Hom GeometricallyIntegral Scheme.Modules.presheaf GeometricallyIrreducible Scheme.Modules.Hom Spec IsIntegral Spec.map Scheme Scheme.Modules.Hom.app IsSeparated smoothOfRelativeDimension_isStableUnderBaseChange Spec.preimage Scheme.Modules.pullbackCongr Scheme.fromSpecResidueField_apply Scheme.Modules.pullbackId Scheme.Modules Scheme.Hom.comp_apply Scheme.IdealSheafData Scheme.Modules.pullbackComp Scheme.Modules.IsInvertible SmoothProperCurve.FiniteMapData Scheme.TwoAffineOpenCover RelEffCartierDiv RelEffCartierDiv.twistModule RelEffCartierDiv.twistModule_def Scheme.Modules.rigidifyMapIso prodKerGraph_eq_prod Scheme.IdealSheafData.IsInvertible RelEffCartierDiv.isInvertible_I Scheme.TwoAffineOpenCover.finrank_H1_sectionsOf_unit_eq_and_finrank_H0_eq_one RelEffCartierDiv.exists_I_eq_prodKerGraph RelEffCartierDiv.eulerChar_tensor_lineBundle_eq Scheme.Modules.IsInvertible.nontrivial_H0_sectionsOf_of_le_eulerChar_sub Scheme.TwoAffineOpenCover.exists_linearEquiv_sectionsOf_H0 RelEffCartierDiv.exists_I_eq_zeroSchemeIdeal_of_eulerChar_eq RelEffCartierDiv.nonempty_twistModule_pullbackAlong_iso_pullback"
namespace RelPicard
p2m_export "AlgebraicGeometry.RelPicard" "baseChangeSnd postComp baseChangeSnd_comp RigidifiedLineBundle RepresentsRelSubPic fibreAt IsAlgEquivZero FibrewiseAlgEquivZero IsAlgEquivZero.of_iso algEquivZeroCut sectionIdeal RigidifiedLineBundle.nonempty_ofInvertible_iso_of_rigidified Scheme.IdealSheafData.IsInvertible.nonempty_invModule_tensor_module_iso isAlgEquivZero_iff_eulerChar_sectionsOf_eq"
namespace AJSurj
p2m_open "AlgebraicGeometry.RelPicard AlgebraicGeometry"

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

variable (R : Type u) [CommRing R] [IsNoetherianRing R] {C : Scheme.{u}} (c : C ⟶ Spec (CommRingCat.of R))
    [IsProper c] [SmoothOfRelativeDimension 1 c] [GeometricallyIntegral c]
    (ε : SchemeHomOver (𝟙 (Spec (CommRingCat.of R))) c)

omit [IsNoetherianRing R] [IsProper c] [SmoothOfRelativeDimension 1 c] [GeometricallyIntegral c] in

theorem isAlgEquivZero_of_fibrewise {k : Type u} [Field k] [IsAlgClosed k]
    {s : Spec (CommRingCat.of k) ⟶ Spec (CommRingCat.of R)}
    (M : RigidifiedLineBundle c ε s) (hM : FibrewiseAlgEquivZero M) :
    IsAlgEquivZero (pullback.snd c s) M.L := by
  have h1 := hM k (𝟙 _)
  let e : pullback c s ⟶ pullback (pullback.snd c s) (𝟙 (Spec (CommRingCat.of k))) :=
    pullback.lift (𝟙 _) (pullback.snd c s) (by simp)
  have he : e ≫ fibreAt c s (𝟙 _) = pullback.snd c s := pullback.lift_snd _ _ _
  have hfst : e ≫ pullback.fst (pullback.snd c s) (𝟙 _) = 𝟙 _ := pullback.lift_fst _ _ _
  refine IsAlgEquivZero.of_iso ?_ (h1.pullback e he)
  exact (Scheme.Modules.pullbackComp _ _).app M.L ≪≫ (Scheme.Modules.pullbackCongr hfst).app M.L ≪≫
    (Scheme.Modules.pullbackId _).app M.L

omit [IsNoetherianRing R] [IsProper c] [SmoothOfRelativeDimension 1 c] [GeometricallyIntegral c] in

theorem nonempty_twoAffineOpenCover (h𝔉 : ∀ m₀ : ℕ, ∃ 𝔉 : SmoothProperCurve.FiniteMapData c ε, m₀ ≤ 𝔉.m)
    {k : Type u} [Field k] (s : Spec (CommRingCat.of k) ⟶ Spec (CommRingCat.of R)) :
    Nonempty ((pullback c s).TwoAffineOpenCover) := by
  obtain ⟨𝔉, -⟩ := h𝔉 0
  obtain ⟨φ, rfl⟩ : ∃ φ : CommRingCat.of R ⟶ CommRingCat.of k, Spec.map φ = s :=
    ⟨Spec.preimage s, Spec.map_preimage s⟩
  letI : Algebra R k := φ.hom.toAlgebra
  exact ⟨𝔉.twoAffineOpenCover.pullback c k⟩

omit [IsNoetherianRing R] in
theorem core (h𝔉 : ∀ m₀ : ℕ, ∃ 𝔉 : SmoothProperCurve.FiniteMapData c ε, m₀ ≤ 𝔉.m) (g : ℕ)
    (hg : ∀ (k : Type u) [Field k] [IsAlgClosed k] (s : Spec (CommRingCat.of k) ⟶ Spec (CommRingCat.of R))
      (L : Type u) [Field L] [Algebra k L] (M : CurveModel k L) (e : M.C ≅ pullback c s)
      (_ : e.hom ≫ pullback.snd c s = M.toBase) (Kc : Divisor k L) (g' : ℕ),
      (∀ D : Divisor k L, (ell D : ℤ) - ell (Kc - D) = Divisor.degree D + 1 - g') → g' = g)
    {k : Type u} [Field k] [IsAlgClosed k] (s : Spec (CommRingCat.of k) ⟶ Spec (CommRingCat.of R))
    (M : RigidifiedLineBundle c ε s) (hM : FibrewiseAlgEquivZero M) :
    ∃ E : RelEffCartierDiv c g s, Nonempty (E.twistModule c ε ≅ M.L) := by

  haveI : IsSeparated c := inferInstance
  haveI : GeometricallyIrreducible c := inferInstance
  haveI : IsProper (pullback.snd c s) := MorphismProperty.pullback_snd (P := @IsProper) _ _ inferInstance
  haveI := smoothOfRelativeDimension_isStableUnderBaseChange 1
  haveI : SmoothOfRelativeDimension 1 (pullback.snd c s) :=
    MorphismProperty.pullback_snd (P := @SmoothOfRelativeDimension 1) _ _ inferInstance
  haveI : IsIntegral (pullback c s) :=
    GeometricallyIntegral.geometrically_isIntegral (f := c) s (pullback.fst c s) (pullback.snd c s)
      (IsPullback.of_hasPullback c s)
  obtain ⟨𝒱⟩ := nonempty_twoAffineOpenCover R c ε h𝔉 s

  have h0 : IsAlgEquivZero (pullback.snd c s) M.L := isAlgEquivZero_of_fibrewise R c ε M hM
  have hχM := (isAlgEquivZero_iff_eulerChar_sectionsOf_eq k (pullback.snd c s) M.L M.isInvertible 𝒱).mp h0

  obtain ⟨hH1, hH0⟩ := Scheme.TwoAffineOpenCover.finrank_H1_sectionsOf_unit_eq_and_finrank_H0_eq_one k
    (pullback.snd c s) g (hg k s) 𝒱

  have hεs : (s ≫ ε.1) ≫ c = s := by rw [Category.assoc, ε.2, Category.comp_id]
  obtain ⟨Eg, hEgI⟩ := RelEffCartierDiv.exists_I_eq_prodKerGraph (f := c) (g := s)
    (fun _ : Fin g => s ≫ ε.1) (fun _ => hεs)
  have hEginv : Eg.I.IsInvertible := RelEffCartierDiv.isInvertible_I Eg
  have hN : Scheme.Modules.IsInvertible (M.L ⊗ Eg.lineBundle) :=
    M.isInvertible.tensor hEginv.isInvertible_invModule
  have hχ2 := RelEffCartierDiv.eulerChar_tensor_lineBundle_eq (f := c) s Eg M.L M.isInvertible 𝒱

  have hpos : (Module.finrank k (𝒱.sectionsOf (pullback.snd c s)
        (SheafOfModules.unit (pullback c s).ringCatSheaf : (pullback c s).Modules)).H1 : ℤ)
      ≤ ((Module.finrank k (𝒱.sectionsOf (pullback.snd c s) (M.L ⊗ Eg.lineBundle)).H0 : ℤ)
          - Module.finrank k (𝒱.sectionsOf (pullback.snd c s) (M.L ⊗ Eg.lineBundle)).H1)
        - ((Module.finrank k (𝒱.sectionsOf (pullback.snd c s)
              (SheafOfModules.unit (pullback c s).ringCatSheaf : (pullback c s).Modules)).H0 : ℤ)
            - Module.finrank k (𝒱.sectionsOf (pullback.snd c s)
              (SheafOfModules.unit (pullback c s).ringCatSheaf : (pullback c s).Modules)).H1) := by
    omega
  have hnt : Nontrivial (𝒱.sectionsOf (pullback.snd c s) (M.L ⊗ Eg.lineBundle)).H0 :=
    Scheme.Modules.IsInvertible.nontrivial_H0_sectionsOf_of_le_eulerChar_sub k (pullback.snd c s) _ hN 𝒱 hpos
  obtain ⟨yv, hyv⟩ := exists_ne (0 : (𝒱.sectionsOf (pullback.snd c s) (M.L ⊗ Eg.lineBundle)).H0)
  obtain ⟨eΓ, -⟩ := Scheme.TwoAffineOpenCover.exists_linearEquiv_sectionsOf_H0 𝒱 (pullback.snd c s)
    (M.L ⊗ Eg.lineBundle)
  have hσ : eΓ.symm yv ≠ 0 := fun h => hyv (by rw [← eΓ.apply_symm_apply yv, h, map_zero])
  obtain ⟨σ, hσ0⟩ := exists_hom_ne_zero (M.L ⊗ Eg.lineBundle) (eΓ.symm yv) hσ

  have hχ3u : (Module.finrank k (𝒱.sectionsOf (pullback.snd c s) (M.L ⊗ Eg.lineBundle)).H0 : ℤ)
        - Module.finrank k (𝒱.sectionsOf (pullback.snd c s) (M.L ⊗ Eg.lineBundle)).H1
      = (Module.finrank k (𝒱.sectionsOf (pullback.snd c s)
            (SheafOfModules.unit (pullback c s).ringCatSheaf : (pullback c s).Modules)).H0 : ℤ)
        - Module.finrank k (𝒱.sectionsOf (pullback.snd c s)
            (SheafOfModules.unit (pullback c s).ringCatSheaf : (pullback c s).Modules)).H1 + g := by
    omega
  have hχ3 : (Module.finrank k (𝒱.sectionsOf (pullback.snd c s) (M.L ⊗ Eg.lineBundle)).H0 : ℤ)
        - Module.finrank k (𝒱.sectionsOf (pullback.snd c s) (M.L ⊗ Eg.lineBundle)).H1
      = (Module.finrank k (𝒱.sectionsOf (pullback.snd c s) (𝟙_ (pullback c s).Modules)).H0 : ℤ)
        - Module.finrank k (𝒱.sectionsOf (pullback.snd c s) (𝟙_ (pullback c s).Modules)).H1 + g := hχ3u
  obtain ⟨E, -, ⟨eE, -⟩⟩ := RelEffCartierDiv.exists_I_eq_zeroSchemeIdeal_of_eulerChar_eq (f := c)
    s hN σ hσ0 𝒱 g hχ3

  have hEg : Eg.I = (sectionIdeal c ε s) ^ g := by
    rw [hEgI, prodKerGraph_eq_prod, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
    rfl
  obtain ⟨eC⟩ := Scheme.IdealSheafData.IsInvertible.nonempty_invModule_tensor_module_iso hEginv
  have eI : ((sectionIdeal c ε s) ^ g).module ≅ Eg.I.module := eqToIso (by rw [hEg])
  have i1 : E.lineBundle ⊗ ((sectionIdeal c ε s) ^ g).module ≅ M.L :=
    (eE.symm ⊗ᵢ eI) ≪≫ (α_ _ _ _) ≪≫ (Iso.refl _ ⊗ᵢ eC) ≪≫ (ρ_ _)
  refine ⟨E, ⟨?_⟩⟩
  rw [RelEffCartierDiv.twistModule_def]
  exact Scheme.Modules.rigidifyMapIso _ _ i1 ≪≫ (RigidifiedLineBundle.nonempty_ofInvertible_iso_of_rigidified M).some

omit [IsNoetherianRing R] in
theorem main
    (h𝔉 : ∀ m₀ : ℕ, ∃ 𝔉 : SmoothProperCurve.FiniteMapData c ε, m₀ ≤ 𝔉.m)
    (g : ℕ)
    (hg : ∀ (k : Type u) [Field k] [IsAlgClosed k] (s : Spec (CommRingCat.of k) ⟶ Spec (CommRingCat.of R))
      (L : Type u) [Field L] [Algebra k L] (M : CurveModel k L) (e : M.C ≅ pullback c s)
      (_ : e.hom ≫ pullback.snd c s = M.toBase) (Kc : Divisor k L) (g' : ℕ),
      (∀ D : Divisor k L, (ell D : ℤ) - ell (Kc - D) = Divisor.degree D + 1 - g') → g' = g)
    (D : RelativePic0Designation R c) (h : RepresentsRelSubPic c ε (algEquivZeroCut c ε) D)
    {Y : Scheme.{u}} {y : Y ⟶ Spec (CommRingCat.of R)} {𝒟 : RelEffCartierDiv c g y} (hU : 𝒟.IsUniversal)
    (aj : Y ⟶ D.P) (haj : aj ≫ D.toBase = y)
    (hclass : Nonempty ((h.poincare.pullbackAlong (⟨aj, haj⟩ : SchemeHomOver y D.toBase)).L ≅ 𝒟.twistModule c ε)) :
    Surjective aj := by
  haveI : IsSeparated c := inferInstance
  refine ⟨fun z => ?_⟩

  let kz := D.P.residueField z
  let k : Type u := AlgebraicClosure kz
  let ι : Spec (CommRingCat.of k) ⟶ D.P :=
    Spec.map (CommRingCat.ofHom (algebraMap kz k)) ≫ D.P.fromSpecResidueField z
  let s : Spec (CommRingCat.of k) ⟶ Spec (CommRingCat.of R) := ι ≫ D.toBase
  let tb : SchemeHomOver s D.toBase := ⟨ι, rfl⟩

  let M : RigidifiedLineBundle c ε s := h.poincare.pullbackAlong tb
  have hM : FibrewiseAlgEquivZero M := (algEquivZeroCut c ε).pullback_mem _ _ tb _ h.poincare_mem

  obtain ⟨E, ⟨eE⟩⟩ := core R c ε h𝔉 g hg s M hM

  let y₀ : Spec (CommRingCat.of k) ⟶ Y := hU.lift E
  have hy₀ : y₀ ≫ y = s := hU.lift_comp E
  let ψ : SchemeHomOver s y := ⟨y₀, hy₀⟩
  have hE : 𝒟.pullbackAlong y₀ hy₀ = E := hU.pullbackAlong_lift E
  let ajO : SchemeHomOver y D.toBase := ⟨aj, haj⟩

  have key : Nonempty ((h.poincare.pullbackAlong (postComp ajO ψ)).L ≅ (h.poincare.pullbackAlong tb).L) := by
    obtain ⟨ecl⟩ := hclass
    obtain ⟨etw⟩ := RelEffCartierDiv.nonempty_twistModule_pullbackAlong_iso_pullback c ε ψ 𝒟
    exact ⟨(Scheme.Modules.pullbackCongr (baseChangeSnd_comp c ajO ψ).symm).app h.poincare.L ≪≫
      ((Scheme.Modules.pullbackComp _ _).app h.poincare.L).symm ≪≫
      (Scheme.Modules.pullback (baseChangeSnd c ψ)).mapIso ecl ≪≫ etw.symm ≪≫
      eqToIso (congrArg (fun D' => RelEffCartierDiv.twistModule c ε D') hE) ≪≫ eE⟩
  have heq : postComp ajO ψ = tb := h.ext_of_iso s _ _ key
  have hcomp : y₀ ≫ aj = ι := congrArg Subtype.val heq
  refine ⟨y₀ (IsLocalRing.closedPoint k), ?_⟩
  rw [← Scheme.Hom.comp_apply, hcomp]
  exact Scheme.fromSpecResidueField_apply z _

end AlgebraicGeometry.RelPicard.AJSurj

p2m_open "CategoryTheory CategoryTheory.Limits AlgebraicGeometry P2MW.S_AlgebraicGeometry_RelPicard_surjective_of_poincare_pullbackAlong_iso_twistModule.AlgebraicGeometry AlgebraicGeometry.RelPicard P2MW.S_AlgebraicGeometry_RelPicard_surjective_of_poincare_pullbackAlong_iso_twistModule.AlgebraicGeometry.RelPicard NeronModelInfra GoodReductionJacobian AlgebraicCurve CategoryTheory.MonoidalCategory"

theorem solution
    (R : Type u) [CommRing R] [IsNoetherianRing R] {C : Scheme.{u}} (c : C ⟶ Spec (CommRingCat.of R))
    [IsProper c] [SmoothOfRelativeDimension 1 c] [GeometricallyIntegral c]
    (ε : SchemeHomOver (𝟙 (Spec (CommRingCat.of R))) c)
    (h𝔉 : ∀ m₀ : ℕ, ∃ 𝔉 : SmoothProperCurve.FiniteMapData c ε, m₀ ≤ 𝔉.m)
    (g : ℕ)
    (hg : ∀ (k : Type u) [Field k] [IsAlgClosed k] (s : Spec (CommRingCat.of k) ⟶ Spec (CommRingCat.of R))
      (L : Type u) [Field L] [Algebra k L] (M : CurveModel k L) (e : M.C ≅ pullback c s)
      (_ : e.hom ≫ pullback.snd c s = M.toBase) (Kc : Divisor k L) (g' : ℕ),
      (∀ D : Divisor k L, (ell D : ℤ) - ell (Kc - D) = Divisor.degree D + 1 - g') → g' = g)
    (D : RelativePic0Designation R c) (h : RepresentsRelSubPic c ε (algEquivZeroCut c ε) D)
    {Y : Scheme.{u}} {y : Y ⟶ Spec (CommRingCat.of R)} {𝒟 : RelEffCartierDiv c g y} (hU : 𝒟.IsUniversal)
    (aj : Y ⟶ D.P) (haj : aj ≫ D.toBase = y)
    (hclass : Nonempty ((h.poincare.pullbackAlong (⟨aj, haj⟩ : SchemeHomOver y D.toBase)).L ≅ 𝒟.twistModule c ε)) :
    Surjective aj :=
  AlgebraicGeometry.RelPicard.AJSurj.main R c ε h𝔉 g hg D h hU aj haj hclass

end S_AlgebraicGeometry_RelPicard_surjective_of_poincare_pullbackAlong_iso_twistModule
end P2MW
export P2MW.S_AlgebraicGeometry_RelPicard_surjective_of_poincare_pullbackAlong_iso_twistModule (solution)
