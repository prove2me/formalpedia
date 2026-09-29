-- Prove2me | solution 1 for AlgebraicGeometry.RelPicard.exists_pic0_equiv_points_nontrivial_H0_pullback_iff_ell_pos
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:03.589526+00:00
-- url     : https://prove2.me/submissions/76f9c21a-7783-5018-a3cb-b6b9227463c6

import Mathlib
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import Definitions.Def_AlgebraicGeometry_RepresentsRelSubPic
import Definitions.Def_AlgebraicGeometry_RelPicardAlgEquivZeroCut
import Definitions.Def_AlgebraicGeometry_RelPicardAlgEquivZeroGroupCut
import Definitions.Def_AlgebraicGeometry_RelSubPicGroup
import Definitions.Def_AlgebraicGeometry_RelSubPicPresheaf
import Definitions.Def_JacJ1Iface
import Definitions.Def_AlgebraicGeometry_SmoothProperCurveFiniteMapData
import Definitions.Def_AlgebraicCurve_CurveModel
import Definitions.Def_AlgebraicCurve_AdelicIndex
import Definitions.Def_AlgebraicCurve_IsCurveOver
import Definitions.Def_SheafOfModules_Monoidal
import Definitions.Def_AlgebraicGeometry_ModulesPullbackMonoidal
import Definitions.Def_AlgebraicGeometry_RelPicardThetaBundle
import Definitions.Def_AlgebraicGeometry_ModulesSectionZeroScheme
import Definitions.Def_AlgebraicCurve_DivisorClassGroup
import Definitions.Def_AlgebraicGeometry_TwoChartCechSectionsOf
import Definitions.Def_AlgebraicGeometry_IdealSheafModule
import Definitions.Def_AlgebraicGeometry_RelPicardAbelJacobiFamily
import Definitions.Def_AlgebraicCurve_RelCartier
import Theorems.Thm_AlgebraicCurve_CurveModel_exists_divisorClassMap
import Theorems.Thm_AlgebraicCurve_exists_list_isPrincipal_sub_sum_single_sub_smul_single
import Theorems.Thm_AlgebraicGeometry_Scheme_Hom_nonempty_pullback_ker_pow_invModule_iso_of_isIso
import Theorems.Thm_AlgebraicGeometry_RelPicard_IsAlgEquivZero_nonempty_iso_tensorUnit_of_ne_zero
import Theorems.Thm_AlgebraicGeometry_RelPicard_RigidifiedLineBundle_fibrewiseAlgEquivZero_of_iso_pointsSubBasepointModule
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_IsInvertible_nonempty_iso_tensorUnit_of_field
import Theorems.Thm_AlgebraicGeometry_RelPicard_RepresentsRelSubPic_nonempty_poincare_pullbackAlong_mul_iso
import Theorems.Thm_AlgebraicGeometry_RelPicard_RepresentsRelSubPic_nonempty_poincare_pullbackAlong_one_iso
import Theorems.Thm_AlgebraicGeometry_RelPicard_IsAlgEquivZero_eulerChar_sectionsOf_tensor_eq
import Theorems.Thm_AlgebraicCurve_exists_isAffineOpen_sup_eq_top
import Theorems.Thm_AlgebraicGeometry_Scheme_TwoAffineOpenCover_exists_linearEquiv_sectionsOf_of_iso
import Theorems.Thm_AlgebraicGeometry_Scheme_TwoAffineOpenCover_exists_linearEquiv_sectionsOf_H0
import Theorems.Thm_AlgebraicGeometry_Scheme_Hom_isInvertible_ker_of_comp_eq_id
import Theorems.Thm_AlgebraicGeometry_Scheme_IdealSheafData_IsInvertible_pow
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_IsInvertible_tensor
import Theorems.Thm_AlgebraicGeometry_RelEffCartierDiv_isInvertible_I
import Theorems.Thm_AlgebraicGeometry_Scheme_IdealSheafData_IsInvertible_isInvertible_module
import Theorems.Thm_AlgebraicGeometry_Scheme_IdealSheafData_IsInvertible_isInvertible_invModule
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_RelPicard_exists_pic0_equiv_points_nontrivial_H0_pullback_iff_ell_pos
p2m_attr_erase "instance" "AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.instFundamentalIdentityOfSumRamificationInertia AlgebraicCurve.Place.instIsScalarTowerResidueFieldRestrictPushforward AlgebraicCurve.Place.instAlgebraResidueFieldRestrictPushforward AlgebraicCurve.Place.instIsLocalHomRestrictInclusion AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.SemilinearAut.instDistribMulActionSubtypeProdRingAutMemSubgroupPic0 AlgebraicCurve.SemilinearAut.instDistribMulActionSubtypeProdRingAutMemSubgroupDivisor AlgebraicCurve.Pic0.instModuleZModTorsion AlgebraicCurve.SemilinearAut.instSMulSubtypeProdRingAutMemSubgroupPlace AlgebraicCurve.SemilinearAut.instDistribMulActionTorsion AlgebraicCurve.SemilinearAut.instSMulSubtypeProdRingAutMemSubgroupPic0 AlgebraicCurve.SemilinearAut.instSMulTorsion AlgebraicCurve.SemilinearAut.instMulActionSubtypeProdRingAutMemSubgroupPlace AlgebraicCurve.SemilinearAut.instSMulCommClassZModTorsion AlgebraicCurve.SemilinearAut.instMulSemiringActionSubtypeProdRingAutMemSubgroup instDecEqAlgebraicClosureRat WeierstrassCurve.Affine.Point.instDistribMulActionAlgEquiv WeierstrassCurve.Affine.Point.instModuleZModTorsionBy WeierstrassCurve.Affine.Point.instSMulTorsionBy WeierstrassCurve.Affine.Point.instDistribMulActionTorsionBy WeierstrassCurve.Affine.Point.instSMulAlgEquiv WeierstrassCurve.Affine.Point.instSMulCommClassAlgEquivZModTorsionBy AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions SheafOfModules.isIso_ihomModelToIhom AlgebraicCurve.instHasLocalResidue_of_hasCanonicalLocalResidueK AlgebraicCurve.instHasCanonicalLocalResidueK_of_hasCanonicalLocalResidueKStar AlgebraicCurve.Place.kw_ffgc_finiteDimensional_adicCompletion instAlgebraSubtypeMemValuationSubring_definitions AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersIntegersCompletion ModularCurve.KwF4gRRTate.instAlgebraKAdicCompletionIntegers AlgebraicCurve.Place.kw_ffgc_continuousSMul_adicCompletionComap AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersCompletionCompletion IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions"
p2m_attr_erase "instance" "IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions AlgebraicCurve.instHasCanonicalLocalResidueK AlgebraicCurve.Place.instAlgebra_restrictResidueField AlgebraicCurve.Place.instIsScalarTower_restrictResidueField AlgebraicCurve.instHasLocalResidue AlgebraicCurve.HasSeparableResidue.of_perfectField_of_isCurveOver AlgebraicCurve.HasSeparableResidue.of_perfectField AlgebraicCurve.Place.instIsLocalHom_restrictSubringHom AlgebraicCurve.instHasCanonicalLocalResidueKStar ModularCurve.KwNo6Pin.isLocalRing_completion AlgebraicGeometry.RelEffCartierDiv.subsingleton_of_degree_zero AlgebraicGeometry.OModulePresheaf.isScalarTower AlgebraicGeometry.Scheme.OrderedAffineCover.instLinearOrder AlgebraicGeometry.OModulePresheaf.module AlgebraicGeometry.Scheme.OrderedAffineCover.instFintype AlgebraicGeometry.Scheme.OrderedAffineCover.instFintypeIdx AlgebraicGeometry.OModulePresheaf.addCommGroup AlgebraicGeometry.Scheme.OrderedAffineCover.instDecidableEqIdx AlgebraicGeometry.OModulePresheaf.moduleSections AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instDecidableEqIdx AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instFintype AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instLinearOrder AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instFintypeIdx AlgebraicGeometry.OModulePresheaf.instSubsingletonObjZero AlgebraicGeometry.OModulePresheaf.Leray.relAltC_scalarTower AlgebraicGeometry.OModulePresheaf.Leray.ker_relAltd_modΓ AlgebraicGeometry.OModulePresheaf.Leray.relAltC_modΓ AlgebraicGeometry.OModulePresheaf.Leray.biC_abGrp AlgebraicGeometry.OModulePresheaf.Leray.relAltH_modΓ AlgebraicGeometry.OModulePresheaf.Leray.ker_relAltd_smul AlgebraicGeometry.OModulePresheaf.Leray.relAltH_scalarTower AlgebraicGeometry.OModulePresheaf.Leray.relAltH_smul AlgebraicGeometry.OModulePresheaf.Leray.biC_module DoubleComplex.instModuleE₂I DoubleComplex.Bounded.modR DoubleComplex.instModuleE₂II DoubleComplex.instAddCommGroupE₂II"
p2m_attr_erase "instance" "DoubleComplex.Bounded.abGrp DoubleComplex.instAddCommGroupE₂I AlgebraicGeometry.ChowDatum.hι_closed AlgebraicGeometry.ChowDatumProj.hιN_closed AlgebraicGeometry.ChowDatumProj.hp_proper AlgebraicGeometry.ChowDatum.hp_isoU AlgebraicGeometry.ChowDatum.hp_proper AlgebraicGeometry.ProjSpace.algebraAway AlgebraicGeometry.ProjSpace.instIsProperProdOverπ AlgebraicGeometry.ChowDatumProj.hp_isoU AlgebraicGeometry.ProjSpace.isProper_π AlgebraicGeometry.ProjSpace.finiteType_mvPolynomial ProjSpaceCech.GradedModule.H.module ProjSpaceCech.GradedModule.H.addCommGroup ProjSpaceCech.GradedModule.sec.instAdd ProjSpaceCech.GradedModule.sec.instNeg ProjSpaceCech.GradedModule.acg ProjSpaceCech.GradedModule.Frac.setoid ProjSpaceCech.GradedModule.modR ProjSpaceCech.GradedModule.sec.instModule ProjSpaceCech.GradedModule.sec.instAddCommGroup ProjSpaceCech.GradedModule.sec.instZero ProjSpaceCech.GradedModule.Presentation.fJ ProjSpaceCech.GradedModule.sec.instSMul ProjSpaceCech.Twist.H.module ProjSpaceCech.Idx.instFintype ProjSpaceCech.Twist.H.addCommGroup ProjSpaceCech.Idx.instDecidableEq ProjSpaceCech.Twist.Mon.instDecidableEq ProjSpaceCech.Twist.cochain.instAddCommGroup ProjSpaceCech.Twist.cochain.instModule"
p2m_attr_erase "simp" "AlgebraicCurve.coe_cechH0Equiv_apply AlgebraicCurve.cechH1ToH1_mk AlgebraicCurve.lSpaceOn_univ AlgebraicCurve.lSpaceOn_empty AlgebraicCurve.Place.congrEquiv_symm_apply AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply AlgebraicCurve.RationalFunctionField.deg_placeOfPoint AlgebraicCurve.Divisor.mapRestrict_single AlgebraicCurve.Divisor.pushforward_single AlgebraicCurve.Place.coe_restrictInclusion AlgebraicCurve.Place.mem_fiber AlgebraicCurve.Place.restrict_toValuationSubring AlgebraicCurve.Divisor.degree_pushforward AlgebraicCurve.Place.restrictResidueMap_residue AlgebraicCurve.Pic0.coe_pushforwardDegZeroHom AlgebraicCurve.Pic0.coe_pullbackDegZeroHom AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal AlgebraicCurve.IsFrobeniusEndo.frobNormRingHom_apply ModularCurve.frobeniusPushforwardGeomLevelPic0_mk ModularCurve.coe_frobeniusGeomLevelEquiv_apply ModularCurve.coe_frobeniusPushforwardGeomLevelDegZero ModularCurve.heckeFibreGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusGeomLevel_apply_coe ModularCurve.frobeniusPullbackGeomLevelPic0OfIsCurveOver_mk ModularCurve.coe_heckeFibreGeomLevelDegZero ModularCurve.coe_frobeniusPullbackGeomLevelDegZero ModularCurve.frobeniusPullbackGeomLevelPic0_mk ModularCurve.frobeniusPullbackGeomLevel_single ModularCurve.heckeFibreGeomLevelPic0_mk ModularCurve.frobeniusPushforwardGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusPushforwardGeomLevel_single ModularCurve.qExpandAlgC_apply AlgebraicCurve.Divisor.degree_pushforwardAlong"
p2m_attr_erase "simp" "AlgebraicCurve.Pic0.coe_degZeroCorrespondence AlgebraicCurve.Place.mem_fiberAlong AlgebraicCurve.SemilinearAut.toRingAut_inv AlgebraicCurve.SemilinearAut.smul_def AlgebraicCurve.SemilinearAut.smul_single AlgebraicCurve.SemilinearAut.smul_toValuationSubring AlgebraicCurve.SemilinearAut.baseAut_inv AlgebraicCurve.SemilinearAut.baseAut_ofAlgAut AlgebraicCurve.SemilinearAut.toRingAut_ofAlgAut AlgebraicCurve.SemilinearAut.torsionRep_apply AlgebraicCurve.SemilinearAut.toRingAut_one AlgebraicCurve.SemilinearAut.deg_smul AlgebraicCurve.SemilinearAut.degree_smul AlgebraicCurve.SemilinearAut.coe_degZeroSMulHom AlgebraicCurve.SemilinearAut.baseAut_mul AlgebraicCurve.SemilinearAut.coe_smulValuationSubringEquiv_apply AlgebraicCurve.SemilinearAut.baseAut_one AlgebraicCurve.SemilinearAut.ofAlgAut_smul AlgebraicCurve.SemilinearAut.coe_torsion_smul AlgebraicCurve.SemilinearAut.toRingAut_mul AlgebraicCurve.coe_frobeniusPushforwardDegZero AlgebraicCurve.IsFrobeniusEndo.coe_frobeniusPullbackDegZero ModularCurve.jqNModC_one ModularCurve.qExpand_coeff_mul ModularCurve.qExpandₐ_apply ModularCurve.jqN_one ModularCurve.qExpand_single ModularCurve.dedekindPsi_one ModularCurve.ModularPolynomialData.mk.sizeOf_spec ModularCurve.evalAtJ_X ModularCurve.ModularPolynomialData.mk.injEq ModularCurve.constantCoeff_jNum ModularCurve.constantCoeff_eisenstein4 ModularCurve.qExpand_C ModularCurve.coeff_jq_neg_one ModularCurve.constantCoeff_jNumQ ModularCurve.reduceModBivar_C_X ModularCurve.laurentMap_coeff ModularCurve.reduceModBivar_X ModularCurve.laurentMap_single"
p2m_attr_erase "simp" "ModularCurve.evalAtJInt_X ModularCurve.evalAtJMod_X ModularCurve.jqNMod_one ModularCurve.aeval_heckeGen ModularCurve.coe_mTorsionGaloisRep_apply ModularCurve.eisensteinSystem_of_dvd ModularCurve.eisensteinSystem_of_not_dvd FreyPackage.mk.sizeOf_spec FreyPackage.mk.injEq WeierstrassCurve.Affine.Point.galoisRepModuleEnd_apply AlgebraicCurve.RationalFunctionField.placeInfty_toValuationSubring AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none AlgebraicCurve.Divisor.evalFun_zero AlgebraicCurve.Place.evalAt_one AlgebraicCurve.Place.differentialCoeff_zero AlgebraicCurve.Place.differentialCoeff_dCoord AlgebraicCurve.TranscendenceTower.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.injEq AlgebraicCurve.TranscendenceTower.mk.injEq AlgebraicCurve.PoleDivisorPackage.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.sizeOf_spec AlgebraicCurve.PoleDivisorPackage.mk.injEq AlgebraicGeometry.Scheme.Modules.tensorPow_zero AlgebraicGeometry.Scheme.Modules.tensorPow_succ AlgebraicGeometry.Scheme.Modules.tensorSections_zero_right AlgebraicGeometry.Scheme.Modules.map_unitSection AlgebraicGeometry.Scheme.Modules.tensorSectionsBilin_apply AlgebraicGeometry.Scheme.Modules.tensorPowSection_zero AlgebraicGeometry.Scheme.Modules.tensorSections_zero_left PresheafOfModules.InternalHom.IsSheafAux.appAt_toPresheafHom SheafOfModules.ihomSectionsEquivFamily_unit AlgebraicGeometry.Scheme.Modules.restrictHomEquivFamily_apply SheafOfModules.ihomEval_unit_app AlgebraicGeometry.Scheme.Modules.ihomEval_zero_right AlgebraicGeometry.Scheme.Modules.ihomEval_zero_left AlgebraicGeometry.Scheme.Modules.homOfFamily_app_apply SheafOfModules.unit_ihomSectionsEquivFamily"
p2m_attr_erase "simp" "AlgebraicGeometry.Scheme.Modules.familyOfHom_app AlgebraicGeometry.Scheme.Modules.restrictUnitIso_hom_app_apply AlgebraicGeometry.Scheme.Modules.restrictUnitIso_inv_app_apply AlgebraicGeometry.Scheme.Modules.restrictHomOfFamily_app_apply AlgebraicGeometry.Scheme.Modules.restrictHomEquivFamily_symm_apply AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.sizeOf_spec AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.injEq AlgebraicCurve.adeleSingle_coe AlgebraicCurve.kaehlerResidueTermKFam_apply AlgebraicCurve.Place.LocalResidueData.mk.injEq AlgebraicCurve.Place.LocalResidueData.mk.sizeOf_spec AlgebraicCurve.Place.kw_ffgc_adicCompletionComapIntegers_coe AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.sizeOf_spec AlgebraicCurve.Place.mem_simplePoleSubmodule AlgebraicCurve.Place.coe_uniformizerSubring ModularCurve.Lg37.Lg37CompletionSection.mk.injEq AlgebraicCurve.Place.CoefficientFieldSection.mk.injEq AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.injEq ModularCurve.Lg37.Lg37CompletionSection.mk.sizeOf_spec AlgebraicCurve.Place.CoefficientFieldSection.mk.sizeOf_spec AlgebraicCurve.Place.poleSubmodule_one AlgebraicCurve.Place.mem_poleSubmodule AlgebraicGeometry.prodKerGraph_one AlgebraicGeometry.fibrePowOver.proj_comp AlgebraicGeometry.prodKerGraph_zero AlgebraicGeometry.RelEffCartierDiv.empty_I AlgebraicGeometry.fibrePowOver.proj_comp_assoc AlgebraicCurve.SymmetricPowerPackage.mk.sizeOf_spec AlgebraicCurve.SymmetricPowerPackage.mk.injEq AlgebraicGeometry.Scheme.OrderedAffineCover.mk.injEq AlgebraicGeometry.OModulePresheaf.mk.sizeOf_spec AlgebraicGeometry.Scheme.OrderedAffineCover.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.mk.injEq AlgebraicGeometry.Scheme.Modules.pullbackLocalSection_neg AlgebraicGeometry.Scheme.Modules.pullbackLocalSection_zero AlgebraicGeometry.Scheme.Modules.pullbackLocalSection_sub AlgebraicGeometry.Scheme.Modules.pullbackLocalSection_add AlgebraicGeometry.Scheme.OrderedAffineCover.toCoverOf_U AlgebraicGeometry.Scheme.OrderedAffineCoverOf.mk.sizeOf_spec AlgebraicGeometry.Scheme.OrderedAffineCoverOf.mk.injEq"
p2m_attr_erase "simp" "AlgebraicGeometry.Scheme.OrderedAffineCover.restrict_U AlgebraicGeometry.OModulePresheaf.Hom.mk.injEq AlgebraicGeometry.OModulePresheaf.Hom.id_app AlgebraicGeometry.OModulePresheaf.AffHom.appSections_apply AlgebraicGeometry.OModulePresheaf.AffHom.comp_app AlgebraicGeometry.OModulePresheaf.AffSES.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.AffHom.kerMap_coe AlgebraicGeometry.OModulePresheaf.AffHom.id_app AlgebraicGeometry.OModulePresheaf.Hom.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.Hom.toAffHom_app AlgebraicGeometry.OModulePresheaf.SES.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.AffHom.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.Hom.comp_app AlgebraicGeometry.OModulePresheaf.SES.mk.injEq AlgebraicGeometry.OModulePresheaf.AffHom.mk.injEq AlgebraicGeometry.OModulePresheaf.Hom.appSections_apply AlgebraicGeometry.OModulePresheaf.AffSES.mk.injEq AlgebraicGeometry.OModulePresheaf.prod_obj AlgebraicGeometry.OModulePresheaf.restrOpen_obj AlgebraicGeometry.OModulePresheaf.DevissageStep.mk.injEq AlgebraicGeometry.OModulePresheaf.pushforward_obj AlgebraicGeometry.OModulePresheaf.im_obj AlgebraicGeometry.OModulePresheaf.pow_obj AlgebraicGeometry.OModulePresheaf.fstHom_app AlgebraicGeometry.OModulePresheaf.ker_obj AlgebraicGeometry.OModulePresheaf.coker_obj AlgebraicGeometry.OModulePresheaf.DevissageStep.mk.sizeOf_spec AlgebraicGeometry.Scheme.OrderedAffineCover.preimage_U AlgebraicGeometry.OModulePresheaf.sndHom_app AlgebraicGeometry.OModulePresheaf.Leray.restrictToPreimage_U DoubleComplex.Bounded.mk.injEq DoubleComplex.Bounded.mk.sizeOf_spec DoubleComplex.Convergence.mk.injEq DoubleComplex.Convergence.mk.sizeOf_spec DoubleComplex.SubQuot.mk.sizeOf_spec DoubleComplex.SubQuot.mk.injEq AlgebraicGeometry.ChowDatumProj.mk.sizeOf_spec AlgebraicGeometry.ChowDatum.mk.sizeOf_spec AlgebraicGeometry.ChowDatumProj.mk.injEq AlgebraicGeometry.ChowDatum.mk.injEq"
p2m_attr_erase "simp" "ProjSpaceCech.GradedModule.mk.injEq ProjSpaceCech.GradedModule.mk.sizeOf_spec ProjSpaceCech.GradedModule.Frac.mk.sizeOf_spec ProjSpaceCech.GradedModule.Presentation.mk.injEq ProjSpaceCech.GradedModule.Frac.mk.injEq ProjSpaceCech.GradedModule.Presentation.mk.sizeOf_spec ProjSpaceCech.GradedModule.Hom.shift_toLinearMap ProjSpaceCech.GradedModule.Hom.mk.sizeOf_spec ProjSpaceCech.GradedModule.Hom.mk.injEq TwoChartCech.Mumford.dK_apply TwoChartCech.Mumford.ι0_apply TwoChartCech.Mumford.ι1_apply TwoChartCech.KerCoprod.dK_apply TwoChartCech.KerCoprod.ι1_apply TwoChartCech.KerCoprod.ι0_apply AlgebraicGeometry.tilde.functorCompPullbackSpecIso_app AlgebraicGeometry.RelPicard.rigSection_snd AlgebraicGeometry.RelPicard.RigidifiedLineBundle.ofInvertible_L AlgebraicGeometry.RelPicard.rigSection_snd_assoc"

set_option autoImplicit false

universe u

p2m_open "CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory AlgebraicGeometry P2MW.S_AlgebraicGeometry_RelPicard_exists_pic0_equiv_points_nontrivial_H0_pullback_iff_ell_pos.AlgebraicGeometry AlgebraicGeometry.RelPicard P2MW.S_AlgebraicGeometry_RelPicard_exists_pic0_equiv_points_nontrivial_H0_pullback_iff_ell_pos.AlgebraicGeometry.RelPicard NeronModelInfra AlgebraicGeometry.SmoothProperCurve GoodReductionJacobian AlgebraicCurve"

open scoped CategoryTheory.MonObj

noncomputable section

namespace AlgebraicGeometry
p2m_export "AlgebraicGeometry" "Surjective Scheme.Modules.Hom.zero_app SmoothOfRelativeDimension IsProper Scheme.Modules.pullback Scheme.Hom GeometricallyIntegral Scheme.Modules.Hom Spec Scheme Scheme.Modules.Hom.app IsClosedImmersion IsSeparated Scheme.Modules.pullbackCongr Scheme.Modules.pullbackId Scheme.Modules toSpecΓ Scheme.IdealSheafData Scheme.Modules.pullbackComp isClosedImmersion_of_comp_eq_id Scheme.Modules.IsInvertible Scheme.Modules.isInvertible_unit Scheme.Modules.pullbackTensorObjIso Scheme.Modules.pullbackTensorUnitObjIso Scheme.TwoAffineOpenCover Scheme.IdealSheafData.module Scheme.IdealSheafData.invModule RelEffCartierDiv Scheme.Modules.toUnitSection Scheme.Modules.ofUnitSection graphOver graphOver_fst graphOver_snd RelEffCartierDiv.ofPoint RelEffCartierDiv.isInvertible_I Scheme.Hom.nonempty_pullback_ker_pow_invModule_iso_of_isIso Scheme.Modules.IsInvertible.nonempty_iso_tensorUnit_of_field Scheme.TwoAffineOpenCover.exists_linearEquiv_sectionsOf_of_iso Scheme.TwoAffineOpenCover.exists_linearEquiv_sectionsOf_H0 Scheme.Hom.isInvertible_ker_of_comp_eq_id"
namespace RelPicard
p2m_export "AlgebraicGeometry.RelPicard" "baseChangeSnd rigSection RigidifiedLineBundle RigidifiedLineBundle.unit RepresentsRelSubPic fibreAt IsAlgEquivZero FibrewiseAlgEquivZero algEquivZeroCut algEquivZeroGroupCut toProdSpec toProdSpec_fst fst_toProdSpec pointsSubBasepointModule pointsSubBasepointModule_nil pointsSubBasepointModule_cons toProdSpec_fst_assoc IsAlgEquivZero.nonempty_iso_tensorUnit_of_ne_zero RigidifiedLineBundle.fibrewiseAlgEquivZero_of_iso_pointsSubBasepointModule RepresentsRelSubPic.nonempty_poincare_pullbackAlong_mul_iso RepresentsRelSubPic.nonempty_poincare_pullbackAlong_one_iso IsAlgEquivZero.eulerChar_sectionsOf_tensor_eq"
namespace PtsCoreGlue
p2m_open "AlgebraicGeometry.RelPicard AlgebraicGeometry"

set_option maxHeartbeats 6400000 in
set_option synthInstance.maxHeartbeats 1600000 in
theorem twoAffineOpenCover_ext {Y : Scheme.{u}} {𝒲 𝒲' : Y.TwoAffineOpenCover}
    (h0 : 𝒲.U0 = 𝒲'.U0) (h1 : 𝒲.U1 = 𝒲'.U1) : 𝒲 = 𝒲' := by
  obtain ⟨U0, U1, _, _, _, _⟩ := 𝒲
  obtain ⟨U0', U1', _, _, _, _⟩ := 𝒲'
  dsimp only at h0 h1
  subst h0
  subst h1
  rfl

set_option maxHeartbeats 6400000 in
set_option synthInstance.maxHeartbeats 1600000 in
theorem preimage_id_opens {Y : Scheme.{u}} (U : Y.Opens) : (𝟙 Y) ⁻¹ᵁ U = U := rfl

set_option maxHeartbeats 6400000 in
set_option synthInstance.maxHeartbeats 1600000 in

theorem nonempty_linearEquiv_of_iso {k : Type u} [Field k] {Y : Scheme.{u}} (y : Y ⟶ Spec (CommRingCat.of k))
    (𝒲 : Y.TwoAffineOpenCover) {M M' : Y.Modules} (e : M ≅ M') :
    Nonempty ((𝒲.sectionsOf y M).H0 ≃ₗ[k] (𝒲.sectionsOf y M').H0) ∧
      Nonempty ((𝒲.sectionsOf y M).H1 ≃ₗ[k] (𝒲.sectionsOf y M').H1) := by
  obtain ⟨𝒲', h0, h1, ⟨e0⟩, ⟨e1⟩⟩ :=
    Scheme.TwoAffineOpenCover.exists_linearEquiv_sectionsOf_of_iso y y (Iso.refl Y) (Category.id_comp y)
      𝒲 M' M (e ≪≫ ((Scheme.Modules.pullbackId Y).app M').symm)
  have h𝒲 : 𝒲' = 𝒲 :=
    twoAffineOpenCover_ext (h0.trans (preimage_id_opens _)) (h1.trans (preimage_id_opens _))
  subst h𝒲
  exact ⟨⟨e0⟩, ⟨e1⟩⟩

set_option maxHeartbeats 6400000 in
set_option synthInstance.maxHeartbeats 1600000 in
theorem eulerChar_congr {k : Type u} [Field k] {Y : Scheme.{u}} (y : Y ⟶ Spec (CommRingCat.of k))
    (𝒲 : Y.TwoAffineOpenCover) {M M' : Y.Modules} (e : M ≅ M') :
    (Module.finrank k (𝒲.sectionsOf y M).H0 : ℤ) - Module.finrank k (𝒲.sectionsOf y M).H1
      = (Module.finrank k (𝒲.sectionsOf y M').H0 : ℤ) - Module.finrank k (𝒲.sectionsOf y M').H1 := by
  obtain ⟨⟨e0⟩, ⟨e1⟩⟩ := nonempty_linearEquiv_of_iso y 𝒲 e
  rw [e0.finrank_eq, e1.finrank_eq]

set_option maxHeartbeats 6400000 in
set_option synthInstance.maxHeartbeats 1600000 in

def pullbackCompCompIso {X Y Z W : Scheme.{u}} (f : X ⟶ Y) (s : Y ⟶ Z) (q : Z ⟶ W) (g : X ⟶ W)
    (hfac : (f ≫ s) ≫ q = g) (L : W.Modules) :
    (Scheme.Modules.pullback (f ≫ s)).obj ((Scheme.Modules.pullback q).obj L) ≅ (Scheme.Modules.pullback g).obj L :=
  (Scheme.Modules.pullbackComp (f ≫ s) q).app L ≪≫ (Scheme.Modules.pullbackCongr hfac).app L

set_option maxHeartbeats 6400000 in
set_option synthInstance.maxHeartbeats 1600000 in

def isoPullbackInvPullbackObj {X Y : Scheme.{u}} (p : X ⟶ Y) [IsIso p] (L : Y.Modules) :
    L ≅ (Scheme.Modules.pullback (inv p)).obj ((Scheme.Modules.pullback p).obj L) :=
  ((Scheme.Modules.pullbackComp (inv p) p ≪≫ Scheme.Modules.pullbackCongr (IsIso.inv_hom_id p) ≪≫
      Scheme.Modules.pullbackId Y).app L).symm

end AlgebraicGeometry.RelPicard.PtsCoreGlue

namespace AlgebraicGeometry
p2m_export "AlgebraicGeometry" "Surjective Scheme.Modules.Hom.zero_app SmoothOfRelativeDimension IsProper Scheme.Modules.pullback Scheme.Hom GeometricallyIntegral Scheme.Modules.Hom Spec Scheme Scheme.Modules.Hom.app IsClosedImmersion IsSeparated Scheme.Modules.pullbackCongr Scheme.Modules.pullbackId Scheme.Modules toSpecΓ Scheme.IdealSheafData Scheme.Modules.pullbackComp isClosedImmersion_of_comp_eq_id Scheme.Modules.IsInvertible Scheme.Modules.isInvertible_unit Scheme.Modules.pullbackTensorObjIso Scheme.Modules.pullbackTensorUnitObjIso Scheme.TwoAffineOpenCover Scheme.IdealSheafData.module Scheme.IdealSheafData.invModule RelEffCartierDiv Scheme.Modules.toUnitSection Scheme.Modules.ofUnitSection graphOver graphOver_fst graphOver_snd RelEffCartierDiv.ofPoint RelEffCartierDiv.isInvertible_I Scheme.Hom.nonempty_pullback_ker_pow_invModule_iso_of_isIso Scheme.Modules.IsInvertible.nonempty_iso_tensorUnit_of_field Scheme.TwoAffineOpenCover.exists_linearEquiv_sectionsOf_of_iso Scheme.TwoAffineOpenCover.exists_linearEquiv_sectionsOf_H0 Scheme.Hom.isInvertible_ker_of_comp_eq_id"
namespace RelPicard
p2m_export "AlgebraicGeometry.RelPicard" "baseChangeSnd rigSection RigidifiedLineBundle RigidifiedLineBundle.unit RepresentsRelSubPic fibreAt IsAlgEquivZero FibrewiseAlgEquivZero algEquivZeroCut algEquivZeroGroupCut toProdSpec toProdSpec_fst fst_toProdSpec pointsSubBasepointModule pointsSubBasepointModule_nil pointsSubBasepointModule_cons toProdSpec_fst_assoc IsAlgEquivZero.nonempty_iso_tensorUnit_of_ne_zero RigidifiedLineBundle.fibrewiseAlgEquivZero_of_iso_pointsSubBasepointModule RepresentsRelSubPic.nonempty_poincare_pullbackAlong_mul_iso RepresentsRelSubPic.nonempty_poincare_pullbackAlong_one_iso IsAlgEquivZero.eulerChar_sectionsOf_tensor_eq"
namespace PtsCoreGlue
p2m_open "AlgebraicGeometry.RelPicard AlgebraicGeometry"

set_option maxHeartbeats 6400000 in
set_option synthInstance.maxHeartbeats 1600000 in

noncomputable def sectionsOfGlobal {X : Scheme.{u}} (L : X.Modules) (m : Γ(L, ⊤)) : SheafOfModules.sections L :=
  PresheafOfModules.sectionsMk (M := L.val)
    (fun U => (L.presheaf.map (homOfLE (le_top : U.unop ≤ ⊤)).op m : Γ(L, U.unop)))
    (by
      intro U V f
      change (L.presheaf.map f) ((L.presheaf.map (homOfLE (le_top : U.unop ≤ ⊤)).op) m) =
        (L.presheaf.map (homOfLE (le_top : V.unop ≤ ⊤)).op) m
      rw [← ConcreteCategory.comp_apply, ← Functor.map_comp]
      exact congrArg (fun g => (L.presheaf.map g) m) (Quiver.Hom.unop_inj (Subsingleton.elim _ _)))

set_option maxHeartbeats 6400000 in
set_option synthInstance.maxHeartbeats 1600000 in
theorem sectionsOfGlobal_top {X : Scheme.{u}} (L : X.Modules) (m : Γ(L, ⊤)) :
    (sectionsOfGlobal L m).1 (Opposite.op ⊤) = m := by
  change (L.presheaf.map (homOfLE (le_top : (⊤ : X.Opens) ≤ ⊤)).op) m = m
  have : (homOfLE (le_top : (⊤ : X.Opens) ≤ ⊤)).op = 𝟙 _ := Quiver.Hom.unop_inj (Subsingleton.elim _ _)
  rw [this, CategoryTheory.Functor.map_id]
  rfl

set_option maxHeartbeats 6400000 in
set_option synthInstance.maxHeartbeats 1600000 in

noncomputable def homOfGlobal {X : Scheme.{u}} (L : X.Modules) (m : Γ(L, ⊤)) : 𝟙_ X.Modules ⟶ L :=
  (SheafOfModules.unitHomEquiv L).symm (sectionsOfGlobal L m)

set_option maxHeartbeats 6400000 in
set_option synthInstance.maxHeartbeats 1600000 in
theorem app_homOfGlobal_one {X : Scheme.{u}} (L : X.Modules) (m : Γ(L, ⊤)) :
    (Scheme.Modules.Hom.app (homOfGlobal L m) ⊤) (Scheme.Modules.toUnitSection ⊤ 1) = m := by
  have h1 := SheafOfModules.unitHomEquiv_apply_coe L (homOfGlobal L m) (Opposite.op ⊤)
  rw [homOfGlobal, Equiv.apply_symm_apply, sectionsOfGlobal_top] at h1
  exact h1.symm

set_option maxHeartbeats 6400000 in
set_option synthInstance.maxHeartbeats 1600000 in
theorem homOfGlobal_ne_zero {X : Scheme.{u}} (L : X.Modules) {m : Γ(L, ⊤)} (hm : m ≠ 0) :
    homOfGlobal L m ≠ 0 := by
  intro h0
  apply hm
  have h1 := app_homOfGlobal_one L m
  rw [h0, Scheme.Modules.Hom.zero_app] at h1
  exact h1.symm.trans (AddCommGrpCat.zero_apply _ _ _)

set_option maxHeartbeats 6400000 in
set_option synthInstance.maxHeartbeats 1600000 in

theorem exists_hom_ne_zero_of_nontrivial_H0 {k : Type u} [Field k] {X : Scheme.{u}} (x : X ⟶ Spec (CommRingCat.of k))
    (𝒱 : X.TwoAffineOpenCover) (L : X.Modules) (hL : Nontrivial (𝒱.sectionsOf x L).H0) :
    ∃ s : 𝟙_ X.Modules ⟶ L, s ≠ 0 := by
  obtain ⟨e, -⟩ := Scheme.TwoAffineOpenCover.exists_linearEquiv_sectionsOf_H0 𝒱 x L
  haveI : Nontrivial Γ(L, ⊤) := e.toEquiv.nontrivial
  obtain ⟨m, hm⟩ := exists_ne (0 : Γ(L, ⊤))
  exact ⟨homOfGlobal L m, homOfGlobal_ne_zero L hm⟩

set_option maxHeartbeats 6400000 in
set_option synthInstance.maxHeartbeats 1600000 in

theorem nontrivial_H0_tensorUnit {k : Type u} [Field k] {X : Scheme.{u}} [Nonempty X] (x : X ⟶ Spec (CommRingCat.of k))
    (𝒱 : X.TwoAffineOpenCover) : Nontrivial (𝒱.sectionsOf x (𝟙_ X.Modules)).H0 := by
  obtain ⟨e, -⟩ := Scheme.TwoAffineOpenCover.exists_linearEquiv_sectionsOf_H0 𝒱 x (𝟙_ X.Modules)
  obtain ⟨pt⟩ := ‹Nonempty X›
  haveI : Nontrivial Γ(X, ⊤) := (X.presheaf.germ ⊤ pt trivial).hom.domain_nontrivial
  haveI : Nontrivial Γ((𝟙_ X.Modules : X.Modules), ⊤) :=
    Function.Injective.nontrivial (f := Scheme.Modules.toUnitSection (X := X) ⊤)
      (fun a b h => by simpa using congrArg (Scheme.Modules.ofUnitSection (X := X) ⊤) h)
  exact e.symm.toEquiv.nontrivial

set_option maxHeartbeats 6400000 in
set_option synthInstance.maxHeartbeats 1600000 in

theorem nonempty_twoAffineOpenCover_of_iso {X X' : Scheme.{u}} (φ : X ≅ X') (𝒱' : X'.TwoAffineOpenCover) :
    Nonempty X.TwoAffineOpenCover := by
  obtain ⟨𝒱, -, -, -, -⟩ := Scheme.TwoAffineOpenCover.exists_linearEquiv_sectionsOf_of_iso
    (R := Γ(X', ⊤)) (φ.hom ≫ X'.toSpecΓ) X'.toSpecΓ φ rfl 𝒱' (𝟙_ X'.Modules)
    ((Scheme.Modules.pullback φ.hom).obj (𝟙_ X'.Modules)) (Iso.refl _)
  exact ⟨𝒱⟩

end AlgebraicGeometry.RelPicard.PtsCoreGlue

namespace AlgebraicGeometry
p2m_export "AlgebraicGeometry" "Surjective Scheme.Modules.Hom.zero_app SmoothOfRelativeDimension IsProper Scheme.Modules.pullback Scheme.Hom GeometricallyIntegral Scheme.Modules.Hom Spec Scheme Scheme.Modules.Hom.app IsClosedImmersion IsSeparated Scheme.Modules.pullbackCongr Scheme.Modules.pullbackId Scheme.Modules toSpecΓ Scheme.IdealSheafData Scheme.Modules.pullbackComp isClosedImmersion_of_comp_eq_id Scheme.Modules.IsInvertible Scheme.Modules.isInvertible_unit Scheme.Modules.pullbackTensorObjIso Scheme.Modules.pullbackTensorUnitObjIso Scheme.TwoAffineOpenCover Scheme.IdealSheafData.module Scheme.IdealSheafData.invModule RelEffCartierDiv Scheme.Modules.toUnitSection Scheme.Modules.ofUnitSection graphOver graphOver_fst graphOver_snd RelEffCartierDiv.ofPoint RelEffCartierDiv.isInvertible_I Scheme.Hom.nonempty_pullback_ker_pow_invModule_iso_of_isIso Scheme.Modules.IsInvertible.nonempty_iso_tensorUnit_of_field Scheme.TwoAffineOpenCover.exists_linearEquiv_sectionsOf_of_iso Scheme.TwoAffineOpenCover.exists_linearEquiv_sectionsOf_H0 Scheme.Hom.isInvertible_ker_of_comp_eq_id"
namespace RelPicard
p2m_export "AlgebraicGeometry.RelPicard" "baseChangeSnd rigSection RigidifiedLineBundle RigidifiedLineBundle.unit RepresentsRelSubPic fibreAt IsAlgEquivZero FibrewiseAlgEquivZero algEquivZeroCut algEquivZeroGroupCut toProdSpec toProdSpec_fst fst_toProdSpec pointsSubBasepointModule pointsSubBasepointModule_nil pointsSubBasepointModule_cons toProdSpec_fst_assoc IsAlgEquivZero.nonempty_iso_tensorUnit_of_ne_zero RigidifiedLineBundle.fibrewiseAlgEquivZero_of_iso_pointsSubBasepointModule RepresentsRelSubPic.nonempty_poincare_pullbackAlong_mul_iso RepresentsRelSubPic.nonempty_poincare_pullbackAlong_one_iso IsAlgEquivZero.eulerChar_sectionsOf_tensor_eq"
namespace PtsCoreGlue
p2m_open "AlgebraicGeometry.RelPicard AlgebraicGeometry"

set_option maxHeartbeats 6400000 in
set_option synthInstance.maxHeartbeats 1600000 in

theorem isIso_toProdSpec {k : Type u} [Field k] {A : Scheme.{u}} (a : A ⟶ Spec (CommRingCat.of k)) :
    IsIso (toProdSpec a) :=
  ⟨⟨pullback.fst a (𝟙 _), toProdSpec_fst a, fst_toProdSpec a⟩⟩

set_option maxHeartbeats 6400000 in
set_option synthInstance.maxHeartbeats 1600000 in
theorem toProdSpec_snd {k : Type u} [Field k] {A : Scheme.{u}} (a : A ⟶ Spec (CommRingCat.of k)) :
    toProdSpec a ≫ pullback.snd a (𝟙 _) = a :=
  pullback.lift_snd _ _ _

set_option maxHeartbeats 6400000 in
set_option synthInstance.maxHeartbeats 1600000 in

theorem comp_toProdSpec_eq_graphOver {k : Type u} [Field k] {C Y : Scheme.{u}}
    (c : C ⟶ Spec (CommRingCat.of k)) (y : Y ⟶ Spec (CommRingCat.of k)) (f : Y ⟶ C) (hf : f ≫ c = y)
    (q : Spec (CommRingCat.of k) ⟶ Y) (hq : q ≫ y = 𝟙 _) (t : Spec (CommRingCat.of k) ⟶ C)
    (ht : t ≫ c = 𝟙 _) (hqt : q ≫ f = t) :
    q ≫ (f ≫ toProdSpec c) = graphOver c t ht := by
  apply pullback.hom_ext
  · rw [Category.assoc, Category.assoc, toProdSpec_fst, Category.comp_id, graphOver_fst, hqt]
  · rw [Category.assoc, Category.assoc, toProdSpec_snd, graphOver_snd, hf, hq]

set_option maxHeartbeats 6400000 in
set_option synthInstance.maxHeartbeats 1600000 in

theorem nonempty_pullback_lineBundle_ofPoint_iso {k : Type u} [Field k] {C Y : Scheme.{u}}
    (c : C ⟶ Spec (CommRingCat.of k)) [IsSeparated c] [SmoothOfRelativeDimension 1 c]
    (y : Y ⟶ Spec (CommRingCat.of k)) [IsSeparated y] [SmoothOfRelativeDimension 1 y]
    (f : Y ⟶ C) [IsIso f] (hf : f ≫ c = y)
    (q : Spec (CommRingCat.of k) ⟶ Y) (hq : q ≫ y = 𝟙 _) (t : Spec (CommRingCat.of k) ⟶ C)
    (ht : t ≫ c = 𝟙 _) (hqt : q ≫ f = t) :
    Nonempty ((Scheme.Modules.pullback (f ≫ toProdSpec c)).obj (RelEffCartierDiv.ofPoint c t ht).lineBundle ≅
      ((q.ker) ^ 1).invModule) := by
  haveI := isIso_toProdSpec c
  have hI : (graphOver c t ht).ker.IsInvertible :=
    RelEffCartierDiv.isInvertible_I (RelEffCartierDiv.ofPoint c t ht)
  have hI' : q.ker.IsInvertible := Scheme.Hom.isInvertible_ker_of_comp_eq_id (p := y) q hq
  obtain ⟨e⟩ := (Scheme.Hom.nonempty_pullback_ker_pow_invModule_iso_of_isIso (f ≫ toProdSpec c)
    (graphOver c t ht) q (comp_toProdSpec_eq_graphOver c y f hf q hq t ht hqt) hI hI' 1).1
  exact ⟨(Scheme.Modules.pullback (f ≫ toProdSpec c)).mapIso
      (eqToIso (congrArg Scheme.IdealSheafData.invModule (pow_one (graphOver c t ht).ker))).symm ≪≫ e⟩

set_option maxHeartbeats 6400000 in
set_option synthInstance.maxHeartbeats 1600000 in

theorem nonempty_pullback_idealModule_ofPoint_iso {k : Type u} [Field k] {C Y : Scheme.{u}}
    (c : C ⟶ Spec (CommRingCat.of k)) [IsSeparated c] [SmoothOfRelativeDimension 1 c]
    (y : Y ⟶ Spec (CommRingCat.of k)) [IsSeparated y] [SmoothOfRelativeDimension 1 y]
    (f : Y ⟶ C) [IsIso f] (hf : f ≫ c = y)
    (q : Spec (CommRingCat.of k) ⟶ Y) (hq : q ≫ y = 𝟙 _) (t : Spec (CommRingCat.of k) ⟶ C)
    (ht : t ≫ c = 𝟙 _) (hqt : q ≫ f = t) :
    Nonempty ((Scheme.Modules.pullback (f ≫ toProdSpec c)).obj (RelEffCartierDiv.ofPoint c t ht).idealModule ≅
      ((q.ker) ^ 1).module) := by
  haveI := isIso_toProdSpec c
  have hI : (graphOver c t ht).ker.IsInvertible :=
    RelEffCartierDiv.isInvertible_I (RelEffCartierDiv.ofPoint c t ht)
  have hI' : q.ker.IsInvertible := Scheme.Hom.isInvertible_ker_of_comp_eq_id (p := y) q hq
  obtain ⟨e⟩ := (Scheme.Hom.nonempty_pullback_ker_pow_invModule_iso_of_isIso (f ≫ toProdSpec c)
    (graphOver c t ht) q (comp_toProdSpec_eq_graphOver c y f hf q hq t ht hqt) hI hI' 1).2
  exact ⟨(Scheme.Modules.pullback (f ≫ toProdSpec c)).mapIso
      (eqToIso (congrArg Scheme.IdealSheafData.module (pow_one (graphOver c t ht).ker))).symm ≪≫ e⟩

set_option maxHeartbeats 6400000 in
set_option synthInstance.maxHeartbeats 1600000 in

theorem nonempty_pullback_pointsSubBasepointModule_iso_foldr
    {k : Type u} [Field k] {C Y : Scheme.{u}} (c : C ⟶ Spec (CommRingCat.of k))
    [IsSeparated c] [SmoothOfRelativeDimension 1 c]
    (y : Y ⟶ Spec (CommRingCat.of k)) [IsSeparated y] [SmoothOfRelativeDimension 1 y]
    (f : Y ⟶ C) [IsIso f] (hf : f ≫ c = y)
    (ε : SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) c)
    (ε' : {p : Spec (CommRingCat.of k) ⟶ Y // p ≫ y = 𝟙 _}) (hε : ε'.1 ≫ f = ε.1)
    (Ps : List {p : Spec (CommRingCat.of k) ⟶ Y // p ≫ y = 𝟙 _}) :
    Nonempty ((Scheme.Modules.pullback (f ≫ toProdSpec c)).obj
        (pointsSubBasepointModule (a := c) ε
          (Ps.map fun P => (⟨P.1 ≫ f, by rw [Category.assoc, hf, P.2]⟩ : SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) c))) ≅
      Ps.foldr (fun P A => ((((P.1).ker) ^ 1).invModule ⊗ (((ε'.1).ker) ^ 1).module) ⊗ A) (𝟙_ Y.Modules)) := by
  induction Ps with
  | nil =>
      simp only [List.map_nil, List.foldr_nil, pointsSubBasepointModule_nil]
      exact ⟨Scheme.Modules.pullbackTensorUnitObjIso (f ≫ toProdSpec c)⟩
  | cons P Ps ih =>
      obtain ⟨eT⟩ := ih
      obtain ⟨eP⟩ := nonempty_pullback_lineBundle_ofPoint_iso c y f hf P.1 P.2 (P.1 ≫ f)
        (by rw [Category.assoc, hf, P.2]) rfl
      obtain ⟨eE⟩ := nonempty_pullback_idealModule_ofPoint_iso c y f hf ε'.1 ε'.2 ε.1 ε.2 hε
      simp only [List.map_cons, List.foldr_cons, pointsSubBasepointModule_cons]
      exact ⟨Scheme.Modules.pullbackTensorObjIso (f ≫ toProdSpec c) _ _ ≪≫
        tensorIso (Scheme.Modules.pullbackTensorObjIso (f ≫ toProdSpec c) _ _ ≪≫ tensorIso eP eE) eT⟩

set_option maxHeartbeats 6400000 in
set_option synthInstance.maxHeartbeats 1600000 in

theorem isClosedImmersion_of_comp_eq_id {X S : Scheme.{u}} (p : X ⟶ S) [IsSeparated p] (σ : S ⟶ X)
    (hσ : σ ≫ p = 𝟙 S) : IsClosedImmersion σ := by
  have : IsClosedImmersion (σ ≫ p) := by rw [hσ]; infer_instance
  exact .of_comp σ p

set_option maxHeartbeats 6400000 in
set_option synthInstance.maxHeartbeats 1600000 in

theorem comp_lift_eq_comp_toProdSpec_baseChangeSnd {k : Type u} [Field k] {C Y T : Scheme.{u}}
    (c : C ⟶ Spec (CommRingCat.of k)) (f : Y ⟶ C)
    (t : T ⟶ Spec (CommRingCat.of k)) (x : Spec (CommRingCat.of k) ⟶ T) (hx : x ≫ t = 𝟙 _)
    (h : 𝟙 C ≫ c = (c ≫ x) ≫ t) :
    f ≫ pullback.lift (𝟙 C) (c ≫ x) h =
      (f ≫ toProdSpec c) ≫ baseChangeSnd c (⟨x, hx⟩ : SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) t) := by
  apply pullback.hom_ext
  · rw [Category.assoc, pullback.lift_fst, Category.assoc, Category.assoc, baseChangeSnd,
      pullback.lift_fst, toProdSpec_fst_assoc, Category.comp_id]
  · rw [Category.assoc, pullback.lift_snd, Category.assoc, Category.assoc, baseChangeSnd,
      pullback.lift_snd, ← Category.assoc (toProdSpec c), toProdSpec_snd]

set_option maxHeartbeats 6400000 in
set_option synthInstance.maxHeartbeats 1600000 in

theorem nonempty_pullback_ker_pow_invModule_iso_of_sections {k : Type u} [Field k] {C Y : Scheme.{u}}
    (c : C ⟶ Spec (CommRingCat.of k)) [IsSeparated c] [SmoothOfRelativeDimension 1 c]
    (y : Y ⟶ Spec (CommRingCat.of k)) [IsSeparated y] [SmoothOfRelativeDimension 1 y]
    (f : Y ⟶ C) [IsIso f]
    (ε : SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) c)
    (ε' : {p : Spec (CommRingCat.of k) ⟶ Y // p ≫ y = 𝟙 _}) (hε : ε'.1 ≫ f = ε.1) (n : ℕ) :
    Nonempty ((Scheme.Modules.pullback f).obj (((ε.1.ker) ^ n).invModule) ≅ (((ε'.1).ker) ^ n).invModule) ∧
      Nonempty ((Scheme.Modules.pullback f).obj (((ε.1.ker) ^ n).module) ≅ (((ε'.1).ker) ^ n).module) := by
  haveI : IsClosedImmersion ε.1 := isClosedImmersion_of_comp_eq_id c ε.1 ε.2
  exact Scheme.Hom.nonempty_pullback_ker_pow_invModule_iso_of_isIso f ε.1 ε'.1 hε
    (Scheme.Hom.isInvertible_ker_of_comp_eq_id (p := c) ε.1 ε.2)
    (Scheme.Hom.isInvertible_ker_of_comp_eq_id (p := y) ε'.1 ε'.2) n

set_option maxHeartbeats 6400000 in
set_option synthInstance.maxHeartbeats 1600000 in

theorem nonempty_pullback_fibreReading_iso
    {k : Type u} [Field k] {C Y T : Scheme.{u}} (c : C ⟶ Spec (CommRingCat.of k))
    [IsSeparated c] [SmoothOfRelativeDimension 1 c]
    (y : Y ⟶ Spec (CommRingCat.of k)) [IsSeparated y] [SmoothOfRelativeDimension 1 y]
    (f : Y ⟶ C) [IsIso f] (hf : f ≫ c = y)
    (ε : SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) c)
    (ε' : {p : Spec (CommRingCat.of k) ⟶ Y // p ≫ y = 𝟙 _}) (hε : ε'.1 ≫ f = ε.1)
    (t : T ⟶ Spec (CommRingCat.of k)) (x : Spec (CommRingCat.of k) ⟶ T) (hx : x ≫ t = 𝟙 _)
    (PL : (pullback c t).Modules) (d : ℕ) :
    Nonempty ((Scheme.Modules.pullback f).obj
        ((Scheme.Modules.pullback
            (pullback.lift (𝟙 C) (c ≫ x) (by rw [Category.id_comp, Category.assoc, hx, Category.comp_id]))).obj PL ⊗
          ((ε.1.ker) ^ d).invModule) ≅
      (Scheme.Modules.pullback (f ≫ toProdSpec c)).obj
          ((Scheme.Modules.pullback (baseChangeSnd c (⟨x, hx⟩ : SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) t))).obj PL) ⊗
        (((ε'.1).ker) ^ d).invModule) := by
  obtain ⟨e2⟩ := (nonempty_pullback_ker_pow_invModule_iso_of_sections c y f ε ε' hε d).1
  have e1 := (Scheme.Modules.pullbackComp f (pullback.lift (𝟙 C) (c ≫ x)
      (by rw [Category.id_comp, Category.assoc, hx, Category.comp_id]))).app PL ≪≫
    (Scheme.Modules.pullbackCongr (comp_lift_eq_comp_toProdSpec_baseChangeSnd c f t x hx _)).app PL ≪≫
    ((Scheme.Modules.pullbackComp (f ≫ toProdSpec c)
      (baseChangeSnd c (⟨x, hx⟩ : SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) t))).app PL).symm
  exact ⟨Scheme.Modules.pullbackTensorObjIso f _ _ ≪≫ tensorIso e1 e2⟩

set_option maxHeartbeats 6400000 in
set_option synthInstance.maxHeartbeats 1600000 in

theorem isInvertible_pointsSubBasepointModule {k : Type u} [Field k] {C : Scheme.{u}} (c : C ⟶ Spec (CommRingCat.of k))
    [IsSeparated c] [SmoothOfRelativeDimension 1 c] (ε : SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) c)
    (Ps : List (SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) c)) :
    Scheme.Modules.IsInvertible (pointsSubBasepointModule (a := c) ε Ps) := by
  induction Ps with
  | nil => exact Scheme.Modules.isInvertible_unit _
  | cons P Ps ih =>
      rw [pointsSubBasepointModule_cons]
      exact ((RelEffCartierDiv.isInvertible_I _).isInvertible_invModule.tensor
        (RelEffCartierDiv.isInvertible_I _).isInvertible_module).tensor ih

end AlgebraicGeometry.RelPicard.PtsCoreGlue

namespace AlgebraicGeometry
p2m_export "AlgebraicGeometry" "Surjective Scheme.Modules.Hom.zero_app SmoothOfRelativeDimension IsProper Scheme.Modules.pullback Scheme.Hom GeometricallyIntegral Scheme.Modules.Hom Spec Scheme Scheme.Modules.Hom.app IsClosedImmersion IsSeparated Scheme.Modules.pullbackCongr Scheme.Modules.pullbackId Scheme.Modules toSpecΓ Scheme.IdealSheafData Scheme.Modules.pullbackComp isClosedImmersion_of_comp_eq_id Scheme.Modules.IsInvertible Scheme.Modules.isInvertible_unit Scheme.Modules.pullbackTensorObjIso Scheme.Modules.pullbackTensorUnitObjIso Scheme.TwoAffineOpenCover Scheme.IdealSheafData.module Scheme.IdealSheafData.invModule RelEffCartierDiv Scheme.Modules.toUnitSection Scheme.Modules.ofUnitSection graphOver graphOver_fst graphOver_snd RelEffCartierDiv.ofPoint RelEffCartierDiv.isInvertible_I Scheme.Hom.nonempty_pullback_ker_pow_invModule_iso_of_isIso Scheme.Modules.IsInvertible.nonempty_iso_tensorUnit_of_field Scheme.TwoAffineOpenCover.exists_linearEquiv_sectionsOf_of_iso Scheme.TwoAffineOpenCover.exists_linearEquiv_sectionsOf_H0 Scheme.Hom.isInvertible_ker_of_comp_eq_id"
namespace RelPicard
p2m_export "AlgebraicGeometry.RelPicard" "baseChangeSnd rigSection RigidifiedLineBundle RigidifiedLineBundle.unit RepresentsRelSubPic fibreAt IsAlgEquivZero FibrewiseAlgEquivZero algEquivZeroCut algEquivZeroGroupCut toProdSpec toProdSpec_fst fst_toProdSpec pointsSubBasepointModule pointsSubBasepointModule_nil pointsSubBasepointModule_cons toProdSpec_fst_assoc IsAlgEquivZero.nonempty_iso_tensorUnit_of_ne_zero RigidifiedLineBundle.fibrewiseAlgEquivZero_of_iso_pointsSubBasepointModule RepresentsRelSubPic.nonempty_poincare_pullbackAlong_mul_iso RepresentsRelSubPic.nonempty_poincare_pullbackAlong_one_iso IsAlgEquivZero.eulerChar_sectionsOf_tensor_eq"
namespace PtsCoreGlue
p2m_open "AlgebraicGeometry.RelPicard AlgebraicGeometry"

variable {K : Type u} [Field K] {F : Type u} [Field F] [Algebra K F]

set_option maxHeartbeats 6400000 in
set_option synthInstance.maxHeartbeats 1600000 in
theorem pic_mk_eq_iff (D E : Divisor K F) :
    (QuotientAddGroup.mk D : Pic K F) = QuotientAddGroup.mk E ↔ Divisor.IsPrincipal (D - E) := by
  rw [QuotientAddGroup.eq_iff_sub_mem, Divisor.mem_principal]

set_option maxHeartbeats 6400000 in
set_option synthInstance.maxHeartbeats 1600000 in
theorem pic0_mk_eq_iff (D E : Divisor.degZero (K := K) (F := F)) :
    Pic0.mk D = Pic0.mk E ↔ (QuotientAddGroup.mk (D : Divisor K F) : Pic K F) = QuotientAddGroup.mk (E : Divisor K F) := by
  rw [pic_mk_eq_iff, Pic0.mk, Pic0.mk, QuotientAddGroup.eq_iff_sub_mem, AddSubgroup.mem_addSubgroupOf,
    AddSubgroup.coe_sub, Divisor.mem_principal]

end AlgebraicGeometry.RelPicard.PtsCoreGlue

open AlgebraicGeometry.RelPicard.PtsCoreGlue in
set_option maxHeartbeats 6400000 in
set_option synthInstance.maxHeartbeats 1600000 in
theorem solution
    (k : Type u) [Field k] [IsAlgClosed k] {C : Scheme.{u}} (c : C ⟶ Spec (CommRingCat.of k))
    [IsProper c] [SmoothOfRelativeDimension 1 c] [GeometricallyIntegral c]
    (ε : SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) c)
    (J : RelativePic0Designation k c) (h : RepresentsRelSubPic c ε (algEquivZeroCut c ε) J)
    {F : Type u} [Field F] [Algebra k F] [IsCurveOver k F] [Algebra.EssFiniteType k F]
    (M : CurveModel k F) (e : M.C ≅ C) (he : e.hom ≫ c = M.toBase)
    (ε' : {p : Spec (CommRingCat.of k) ⟶ M.C // p ≫ M.toBase = 𝟙 _}) (hε' : ε'.1 ≫ e.hom = ε.1) :
    letI := (show RepresentsRelSubPic c ε (algEquivZeroGroupCut c ε).toSubPicCondition J from h).grpObj
    ∃ pts : Pic0 k F ≃ (Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ Over.mk J.toBase),
      (∀ a b : Pic0 k F, pts (a + b) = pts a * pts b) ∧
      ∀ (Dv : Divisor.degZero (K := k) (F := F)) (d : ℕ) (𝒱 : C.TwoAffineOpenCover),
        Nontrivial (𝒱.sectionsOf c
          ((Scheme.Modules.pullback
              (pullback.lift (𝟙 C) (c ≫ (pts (Pic0.mk Dv)).left)
                (((Category.id_comp c).trans (Category.comp_id c).symm).trans
                  ((congrArg (c ≫ ·) (Over.w (pts (Pic0.mk Dv)))).symm.trans
                    (Category.assoc c _ _).symm)))).obj h.poincare.L ⊗
            ((ε.1.ker) ^ d).invModule)).H0 ↔
          0 < ell ((Dv : Divisor k F) + Finsupp.single (M.pointEquivPlace ε') (d : ℤ)) := by
  letI := (show RepresentsRelSubPic c ε (algEquivZeroGroupCut c ε).toSubPicCondition J from h).grpObj

  let hG : RepresentsRelSubPic c ε (algEquivZeroGroupCut c ε).toSubPicCondition J := h

  let pt : (Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ Over.mk J.toBase) → SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) J.toBase :=
    fun a => ⟨a.left, by have w := Over.w a; simp only [Over.mk_left, Over.mk_hom] at w; exact w⟩

  let P : (Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ Over.mk J.toBase) → (pullback c (𝟙 (Spec (CommRingCat.of k)))).Modules :=
    fun a => (h.poincare.pullbackAlong (pt a)).L

  let g : M.C ⟶ pullback c (𝟙 (Spec (CommRingCat.of k))) := e.hom ≫ toProdSpec c
  haveI : IsIso (toProdSpec c) := ⟨⟨pullback.fst c (𝟙 _), toProdSpec_fst c, fst_toProdSpec c⟩⟩
  haveI : IsIso g := IsIso.comp_isIso
  let Lmod : (Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ Over.mk J.toBase) → M.C.Modules :=
    fun a => (Scheme.Modules.pullback g).obj (P a)

  obtain ⟨cl, hcl_iso, hcl_tensor, hcl_one, hcl_pt, hcl_num⟩ := AlgebraicCurve.CurveModel.exists_divisorClassMap M
  let Φ : (Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ Over.mk J.toBase) → Pic k F := fun a => cl (Lmod a)

  have hPinv : ∀ a, Scheme.Modules.IsInvertible (P a) := fun a => (h.poincare.pullbackAlong (pt a)).isInvertible
  have hLinv : ∀ a, Scheme.Modules.IsInvertible (Lmod a) := fun a => (hPinv a).pullback g

  have hΦmul : ∀ a b, Φ (a * b) = Φ a + Φ b := by
    intro a b
    obtain ⟨i⟩ := RepresentsRelSubPic.nonempty_poincare_pullbackAlong_mul_iso hG a b
    have i' : Lmod (a * b) ≅ Lmod a ⊗ Lmod b :=
      (Scheme.Modules.pullback g).mapIso i ≪≫ Scheme.Modules.pullbackTensorObjIso g _ _
    show cl (Lmod (a * b)) = cl (Lmod a) + cl (Lmod b)
    rw [hcl_iso _ _ (hLinv _) ⟨i'⟩, hcl_tensor _ _ (hLinv a) (hLinv b)]
  have hΦone : Φ 1 = 0 := by
    obtain ⟨i⟩ := RepresentsRelSubPic.nonempty_poincare_pullbackAlong_one_iso hG (Over.mk (𝟙 (Spec (CommRingCat.of k))))
    have i' : Lmod 1 ≅ 𝟙_ M.C.Modules :=
      (Scheme.Modules.pullback g).mapIso i ≪≫ Scheme.Modules.pullbackTensorUnitObjIso g
    show cl (Lmod 1) = 0
    rw [hcl_iso _ _ (hLinv _) ⟨i'⟩, hcl_one]

  have hcutP : ∀ a, FibrewiseAlgEquivZero (h.poincare.pullbackAlong (pt a)) := fun a =>
    (algEquivZeroCut c ε).pullback_mem _ _ (pt a) _ h.poincare_mem
  let s₁ : pullback c (𝟙 (Spec (CommRingCat.of k))) ⟶
      pullback (pullback.snd c (𝟙 (Spec (CommRingCat.of k)))) (𝟙 (Spec (CommRingCat.of k))) :=
    pullback.lift (𝟙 _) (pullback.snd c (𝟙 _)) (by rw [Category.id_comp, Category.comp_id])
  have hs₁fst : s₁ ≫ pullback.fst _ _ = 𝟙 _ := pullback.lift_fst _ _ _
  have hs₁snd : s₁ ≫ fibreAt c (𝟙 _) (𝟙 (Spec (CommRingCat.of k))) = pullback.snd c (𝟙 _) := by
    show s₁ ≫ pullback.snd _ _ = _
    exact pullback.lift_snd _ _ _
  have hιsnd : toProdSpec c ≫ pullback.snd c (𝟙 _) = c := by
    show pullback.lift (𝟙 C) c (by simp) ≫ pullback.snd _ _ = c
    exact pullback.lift_snd _ _ _
  have hg_base : (g ≫ s₁) ≫ fibreAt c (𝟙 _) (𝟙 (Spec (CommRingCat.of k))) = M.toBase := by
    rw [Category.assoc, hs₁snd, show g = e.hom ≫ toProdSpec c from rfl, Category.assoc, hιsnd, he]
  have hι_base : (toProdSpec c ≫ s₁) ≫ fibreAt c (𝟙 _) (𝟙 (Spec (CommRingCat.of k))) = c := by
    rw [Category.assoc, hs₁snd, hιsnd]
  have hg_fac : (g ≫ s₁) ≫ pullback.fst _ _ = g := by rw [Category.assoc, hs₁fst, Category.comp_id]
  have hι_fac : (toProdSpec c ≫ s₁) ≫ pullback.fst _ _ = toProdSpec c := by rw [Category.assoc, hs₁fst, Category.comp_id]
  have halgM : ∀ a, IsAlgEquivZero M.toBase (Lmod a) := fun a =>
    (((hcutP a) k (𝟙 _)).pullback (g ≫ s₁) hg_base).of_iso (pullbackCompCompIso g s₁ _ g hg_fac (P a))
  let LC : (Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ Over.mk J.toBase) → C.Modules :=
    fun a => (Scheme.Modules.pullback (toProdSpec c)).obj (P a)
  have hLCinv : ∀ a, Scheme.Modules.IsInvertible (LC a) := fun a => (hPinv a).pullback _
  have halgC : ∀ a, IsAlgEquivZero c (LC a) := fun a =>
    (((hcutP a) k (𝟙 _)).pullback (toProdSpec c ≫ s₁) hι_base).of_iso (pullbackCompCompIso _ s₁ _ _ hι_fac (P a))
  have hLmodLC : ∀ a, Nonempty (Lmod a ≅ (Scheme.Modules.pullback e.hom).obj (LC a)) := fun a =>
    ⟨((Scheme.Modules.pullbackComp e.hom (toProdSpec c)).app (P a)).symm⟩

  obtain ⟨U, V, hU, hV, hUV, hsup⟩ := AlgebraicCurve.exists_isAffineOpen_sup_eq_top M.toBase M.finset_subset_affineOpen
  let 𝒱M : M.C.TwoAffineOpenCover :=
    { U0 := U, U1 := V, isAffineOpen_U0 := hU, isAffineOpen_U1 := hV, sup_eq_top := hsup, isAffineOpen_inf := hUV }
  have hdeg0 : ∀ a (D : Divisor k F), (QuotientAddGroup.mk D : Pic k F) = Φ a → Divisor.degree D = 0 := by
    intro a D hD
    obtain ⟨-, -, -, hχ⟩ := hcl_num 𝒱M (Lmod a) (hLinv a) D hD
    have hcc := IsAlgEquivZero.eulerChar_sectionsOf_tensor_eq M.toBase 𝒱M (Lmod a) (𝟙_ _) (hLinv a)
      (Scheme.Modules.isInvertible_unit _) (halgM a)
    have hcongr := eulerChar_congr M.toBase 𝒱M (ρ_ (Lmod a))
    linarith

  let Φ' : (Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ Over.mk J.toBase) → Pic0 k F := fun a =>
    Pic0.mk ⟨(Φ a).out, Divisor.mem_degZero.mpr (hdeg0 a _ (QuotientAddGroup.out_eq' (Φ a)))⟩
  have hΦ'Φ : ∀ a (Dv : Divisor.degZero (K := k) (F := F)),
      Φ' a = Pic0.mk Dv ↔ Φ a = QuotientAddGroup.mk (Dv : Divisor k F) := by
    intro a Dv
    rw [pic0_mk_eq_iff]
    show (QuotientAddGroup.mk (Φ a).out : Pic k F) = _ ↔ _
    rw [QuotientAddGroup.out_eq']
  have hΦ'mul : ∀ a b, Φ' (a * b) = Φ' a + Φ' b := by
    intro a b
    rw [← Pic0.mk_add, hΦ'Φ, AddSubgroup.coe_add, QuotientAddGroup.mk_add]
    show Φ (a * b) = (QuotientAddGroup.mk (Φ a).out : Pic k F) + QuotientAddGroup.mk (Φ b).out
    rw [QuotientAddGroup.out_eq', QuotientAddGroup.out_eq', hΦmul]

  haveI : IsSeparated c := inferInstance
  have hker : ∀ a, Φ a = 0 → a = 1 := by
    intro a ha

    obtain ⟨𝒱C⟩ := nonempty_twoAffineOpenCover_of_iso e.symm 𝒱M

    obtain ⟨𝒱n, -, -, ⟨e0⟩, -⟩ := Scheme.TwoAffineOpenCover.exists_linearEquiv_sectionsOf_of_iso
      M.toBase c e he 𝒱C (LC a) (Lmod a) (hLmodLC a).some

    have h0 : (QuotientAddGroup.mk (0 : Divisor k F) : Pic k F) = Φ a := by rw [ha, QuotientAddGroup.mk_zero]
    obtain ⟨hfinL, -, hL0, -⟩ := hcl_num 𝒱n (Lmod a) (hLinv a) 0 h0
    have h1 : (QuotientAddGroup.mk (0 : Divisor k F) : Pic k F) = cl (𝟙_ M.C.Modules) := by rw [hcl_one, QuotientAddGroup.mk_zero]
    obtain ⟨hfin1, -, h10, -⟩ := hcl_num 𝒱n (𝟙_ M.C.Modules) (Scheme.Modules.isInvertible_unit _) 0 h1
    haveI := hfin1
    have hpos : 0 < Module.finrank k (𝒱n.sectionsOf M.toBase (Lmod a)).H0 := by
      rw [hL0, ← h10]
      haveI := nontrivial_H0_tensorUnit (X := M.C) M.toBase 𝒱n
      exact Module.finrank_pos
    haveI : Nontrivial (𝒱n.sectionsOf M.toBase (Lmod a)).H0 := Module.nontrivial_of_finrank_pos hpos
    obtain ⟨u, v, huv⟩ := (inferInstance : Nontrivial (𝒱n.sectionsOf M.toBase (Lmod a)).H0)
    have hntC : Nontrivial (𝒱C.sectionsOf c (LC a)).H0 := ⟨e0 u, e0 v, fun hh => huv (e0.injective hh)⟩

    obtain ⟨s, hs⟩ := exists_hom_ne_zero_of_nontrivial_H0 c 𝒱C (LC a) hntC
    obtain ⟨iC⟩ := IsAlgEquivZero.nonempty_iso_tensorUnit_of_ne_zero c 𝒱C (hLCinv a) (halgC a) s hs

    have iP : P a ≅ (RigidifiedLineBundle.unit (c := c) (ε := ε) (𝟙 (Spec (CommRingCat.of k)))).L :=
      isoPullbackInvPullbackObj (toProdSpec c) (P a) ≪≫ (Scheme.Modules.pullback (inv (toProdSpec c))).mapIso iC ≪≫
        Scheme.Modules.pullbackTensorUnitObjIso (inv (toProdSpec c))

    obtain ⟨i1⟩ := RepresentsRelSubPic.nonempty_poincare_pullbackAlong_one_iso hG (Over.mk (𝟙 (Spec (CommRingCat.of k))))
    have hpt : pt a = pt 1 := h.ext_of_iso (𝟙 _) (pt a) (pt 1) ⟨iP ≪≫ i1.symm⟩
    exact Over.OverMorphism.ext (congrArg Subtype.val hpt)
  have hΦ'inj : Function.Injective Φ' := by
    intro a b hab
    have h2 : Φ a = Φ b := by
      have := (hΦ'Φ a ⟨(Φ b).out, Divisor.mem_degZero.mpr (hdeg0 b _ (QuotientAddGroup.out_eq' (Φ b)))⟩).mp hab
      rw [this]
      exact QuotientAddGroup.out_eq' (Φ b)
    have h3 : Φ (a * b⁻¹) = 0 := by
      have h4 : Φ (b * b⁻¹) = 0 := by rw [mul_inv_cancel, hΦone]
      rw [hΦmul] at h4 ⊢
      rw [h2]; exact h4
    have := hker _ h3
    rw [mul_inv_eq_one] at this
    exact this

  haveI : IsSeparated M.toBase := inferInstance
  have hkerinv : ∀ (P : {p : Spec (CommRingCat.of k) ⟶ M.C // p ≫ M.toBase = 𝟙 _}) (n : ℕ),
      (((P.1).ker) ^ n).IsInvertible := fun P n =>
    (Scheme.Hom.isInvertible_ker_of_comp_eq_id (p := M.toBase) P.1 P.2).pow n
  have hcl_foldr : ∀ Ps' : List {p : Spec (CommRingCat.of k) ⟶ M.C // p ≫ M.toBase = 𝟙 _},
      Scheme.Modules.IsInvertible
          (Ps'.foldr (fun P A => ((((P.1).ker) ^ 1).invModule ⊗ (((ε'.1).ker) ^ 1).module) ⊗ A) (𝟙_ M.C.Modules)) ∧
        cl (Ps'.foldr (fun P A => ((((P.1).ker) ^ 1).invModule ⊗ (((ε'.1).ker) ^ 1).module) ⊗ A) (𝟙_ M.C.Modules)) =
          QuotientAddGroup.mk ((Ps'.map fun P => Finsupp.single (M.pointEquivPlace P) (1 : ℤ)).sum
            - (Ps'.length : ℤ) • Finsupp.single (M.pointEquivPlace ε') 1) := by
    intro Ps'
    induction Ps' with
    | nil =>
        refine ⟨Scheme.Modules.isInvertible_unit _, ?_⟩
        simp only [List.foldr_nil, List.map_nil, List.sum_nil, List.length_nil, Nat.cast_zero, zero_smul, sub_zero,
          QuotientAddGroup.mk_zero]
        exact hcl_one
    | cons P Ps' ih =>
        obtain ⟨ihinv, ihcl⟩ := ih
        have hA : Scheme.Modules.IsInvertible ((((P.1).ker) ^ 1).invModule ⊗ (((ε'.1).ker) ^ 1).module) :=
          (hkerinv P 1).isInvertible_invModule.tensor (hkerinv ε' 1).isInvertible_module
        refine ⟨hA.tensor ihinv, ?_⟩
        rw [List.foldr_cons, hcl_tensor _ _ hA ihinv, hcl_tensor _ _ (hkerinv P 1).isInvertible_invModule
          (hkerinv ε' 1).isInvertible_module, (hcl_pt P 1).1, (hcl_pt ε' 1).2, ihcl]
        simp only [List.map_cons, List.sum_cons, List.length_cons, Nat.cast_succ, one_smul, add_smul]
        rw [← QuotientAddGroup.mk_add, ← QuotientAddGroup.mk_add]
        congr 1
        abel
  have hΦ'surj : Function.Surjective Φ' := by
    intro ξ
    obtain ⟨Dv, rfl⟩ := Pic0.mk_surjective ξ
    obtain ⟨l, hl⟩ := AlgebraicCurve.exists_list_isPrincipal_sub_sum_single_sub_smul_single
      (M.pointEquivPlace ε') (Dv : Divisor k F) (Divisor.mem_degZero.mp Dv.2)
    let Ps' : List {p : Spec (CommRingCat.of k) ⟶ M.C // p ≫ M.toBase = 𝟙 _} := l.map M.pointEquivPlace.symm
    let Ps : List (SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) c) :=
      Ps'.map fun P => (⟨P.1 ≫ e.hom, by rw [Category.assoc, he, P.2]⟩ : SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) c)
    have hNinv : Scheme.Modules.IsInvertible (pointsSubBasepointModule (a := c) ε Ps) :=
      isInvertible_pointsSubBasepointModule c ε Ps
    obtain ⟨rig⟩ := Scheme.Modules.IsInvertible.nonempty_iso_tensorUnit_of_field k
      ((Scheme.Modules.pullback (rigSection c (𝟙 (Spec (CommRingCat.of k))) ε)).obj (pointsSubBasepointModule (a := c) ε Ps))
      (hNinv.pullback _)
    let N : RigidifiedLineBundle c ε (𝟙 (Spec (CommRingCat.of k))) :=
      { L := pointsSubBasepointModule (a := c) ε Ps, isInvertible := hNinv, rigidified := ⟨rig⟩ }
    have hcut : (algEquivZeroCut c ε).P (𝟙 _) N :=
      RigidifiedLineBundle.fibrewiseAlgEquivZero_of_iso_pointsSubBasepointModule N Ps (Iso.refl _)
    let a' : SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) J.toBase := h.classify (𝟙 _) N hcut
    let a : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ Over.mk J.toBase := Over.homMk a'.1 a'.2
    have hpa : pt a = a' := Subtype.ext rfl
    obtain ⟨iN⟩ := h.classify_spec (𝟙 _) N hcut
    have iP : P a ≅ pointsSubBasepointModule (a := c) ε Ps := by
      show (h.poincare.pullbackAlong (pt a)).L ≅ _
      rw [hpa]
      exact iN
    obtain ⟨iF⟩ := nonempty_pullback_pointsSubBasepointModule_iso_foldr c M.toBase e.hom he ε ε' hε' Ps'
    refine ⟨a, ?_⟩
    rw [hΦ'Φ]
    show cl (Lmod a) = _
    rw [hcl_iso _ _ (hLinv a) ⟨(Scheme.Modules.pullback g).mapIso iP ≪≫ iF⟩, (hcl_foldr Ps').2, pic_mk_eq_iff]
    have hmap : Ps'.map (fun P => Finsupp.single (M.pointEquivPlace P) (1 : ℤ)) = l.map fun v => Finsupp.single v (1 : ℤ) := by
      simp only [Ps', List.map_map]
      congr 1
      funext v
      simp only [Function.comp, Equiv.apply_symm_apply]
    have hlen : Ps'.length = l.length := by simp only [Ps', List.length_map]
    rw [hmap, hlen]

    have := Divisor.principal.neg_mem hl
    rw [neg_sub] at this
    exact this

  let Ψ : (Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ Over.mk J.toBase) ≃ Pic0 k F := Equiv.ofBijective Φ' ⟨hΦ'inj, hΦ'surj⟩
  refine ⟨Ψ.symm, fun x y => ?_, fun Dv d 𝒱 => ?_⟩
  · apply Ψ.injective
    show Φ' (Ψ.symm (x + y)) = Φ' (Ψ.symm x * Ψ.symm y)
    rw [hΦ'mul]
    show Ψ (Ψ.symm (x + y)) = Ψ (Ψ.symm x) + Ψ (Ψ.symm y)
    simp only [Equiv.apply_symm_apply]
  ·
    let a : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ Over.mk J.toBase := Ψ.symm (Pic0.mk Dv)
    have ha : Φ a = QuotientAddGroup.mk (Dv : Divisor k F) := (hΦ'Φ a Dv).mp (Ψ.apply_symm_apply (Pic0.mk Dv))

    obtain ⟨iG⟩ := nonempty_pullback_fibreReading_iso c M.toBase e.hom he ε ε' hε' J.toBase a.left (pt a).2 h.poincare.L d
    obtain ⟨𝒱n, -, -, ⟨e0⟩, -⟩ := Scheme.TwoAffineOpenCover.exists_linearEquiv_sectionsOf_of_iso M.toBase c e he 𝒱 _
      (Lmod a ⊗ (((ε'.1).ker) ^ d).invModule) iG.symm

    have hinvG : Scheme.Modules.IsInvertible (Lmod a ⊗ (((ε'.1).ker) ^ d).invModule) :=
      (hLinv a).tensor (hkerinv ε' d).isInvertible_invModule
    have hclG : (QuotientAddGroup.mk ((Dv : Divisor k F) + Finsupp.single (M.pointEquivPlace ε') (d : ℤ)) : Pic k F) =
        cl (Lmod a ⊗ (((ε'.1).ker) ^ d).invModule) := by
      rw [hcl_tensor _ _ (hLinv a) (hkerinv ε' d).isInvertible_invModule, (hcl_pt ε' d).1, QuotientAddGroup.mk_add,
        Finsupp.smul_single, Nat.smul_one_eq_cast]
      show _ = Φ a + _
      rw [ha]
    obtain ⟨hfin, -, hh0, -⟩ := hcl_num 𝒱n _ hinvG _ hclG
    haveI := hfin
    constructor
    · rintro ⟨u, v, huv⟩
      haveI : Nontrivial (𝒱n.sectionsOf M.toBase (Lmod a ⊗ (((ε'.1).ker) ^ d).invModule)).H0 :=
        ⟨e0.symm u, e0.symm v, fun hh => huv (e0.symm.injective hh)⟩
      have hpos : 0 < Module.finrank k (𝒱n.sectionsOf M.toBase (Lmod a ⊗ (((ε'.1).ker) ^ d).invModule)).H0 :=
        Module.finrank_pos
      rwa [hh0] at hpos
    · intro hpos
      rw [← hh0] at hpos
      obtain ⟨u, v, huv⟩ := Module.nontrivial_of_finrank_pos hpos
      exact ⟨e0 u, e0 v, fun hh => huv (e0.injective hh)⟩

end
end S_AlgebraicGeometry_RelPicard_exists_pic0_equiv_points_nontrivial_H0_pullback_iff_ell_pos
end P2MW
export P2MW.S_AlgebraicGeometry_RelPicard_exists_pic0_equiv_points_nontrivial_H0_pullback_iff_ell_pos (solution)
