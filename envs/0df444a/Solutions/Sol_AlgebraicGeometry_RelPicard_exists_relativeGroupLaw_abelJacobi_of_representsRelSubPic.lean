-- Prove2me | solution 1 for AlgebraicGeometry.RelPicard.exists_relativeGroupLaw_abelJacobi_of_representsRelSubPic
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:03.589526+00:00
-- url     : https://prove2.me/submissions/2ce67ddd-2aa5-5575-821e-497ceac6d86b

import Mathlib
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import Definitions.Def_AlgebraicGeometry_RepresentsRelSubPic
import Definitions.Def_AlgebraicGeometry_RelPicardAlgEquivZeroCut
import Definitions.Def_JacJ1Iface
import Definitions.Def_AlgebraicGeometry_RelativeGroupLaw
import Definitions.Def_AlgebraicCurve_CurveModel
import Definitions.Def_AlgebraicCurve_IsCurveOver

import Definitions.Def_AlgebraicGeometry_RelPicardAlgEquivZeroGroupCut
import Definitions.Def_AlgebraicGeometry_RelSubPicGroup
import Definitions.Def_AlgebraicGeometry_SmoothProperCurveBase
import Definitions.Def_AlgebraicGeometry_RelSubPicBaseChange
import Definitions.Def_AlgebraicGeometry_RelativePic0DesignationBaseChange
import Definitions.Def_AlgebraicGeometry_RelPicardAbelJacobiFamily
import Definitions.Def_AlgebraicCurve_DivisorClassGroup
import Definitions.Def_SheafOfModules_Monoidal
import Definitions.Def_AlgebraicGeometry_ModulesPullbackMonoidal
import Definitions.Def_AlgebraicGeometry_IdealSheafModule
import Definitions.Def_AlgebraicGeometry_RelEffCartierDivOfPoint
import Definitions.Def_AlgebraicCurve_RelCartier
import Theorems.Thm_AlgebraicGeometry_Scheme_Hom_nonempty_pullback_ker_pow_invModule_iso_of_isIso
import Theorems.Thm_AlgebraicGeometry_RelEffCartierDiv_isInvertible_I
import Theorems.Thm_AlgebraicGeometry_RelPicard_exists_abelJacobi_of_representsRelSubPic
import Theorems.Thm_AlgebraicGeometry_RelPicard_baseChange_points_mul_poincare_compat
import Theorems.Thm_AlgebraicGeometry_RelPicard_exists_pic0_equiv_points_abelJacobi_of_curveModel
import Theorems.Thm_AlgebraicCurve_essFiniteType_functionField
import Theorems.Thm_AlgebraicGeometry_RelPicard_exists_representsRelSubPic_baseChange
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_RelPicard_exists_relativeGroupLaw_abelJacobi_of_representsRelSubPic
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

p2m_open "CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory AlgebraicGeometry P2MW.S_AlgebraicGeometry_RelPicard_exists_relativeGroupLaw_abelJacobi_of_representsRelSubPic.AlgebraicGeometry AlgebraicGeometry.RelPicard P2MW.S_AlgebraicGeometry_RelPicard_exists_relativeGroupLaw_abelJacobi_of_representsRelSubPic.AlgebraicGeometry.RelPicard NeronModelInfra GoodReductionJacobian AlgebraicCurve AlgebraicGeometry.SmoothProperCurve"

universe u v

noncomputable section

namespace AlgebraicGeometry
p2m_export "AlgebraicGeometry" "SmoothOfRelativeDimension IsProper Scheme.Modules.pullback Scheme.Hom GeometricallyIntegral Scheme.Hom.range_fiberι Spec Spec.map Scheme Smooth IsSeparated Scheme.Modules GeometricallyConnected geometrically Scheme.IdealSheafData Scheme.Modules.pullbackTensorObjIso Scheme.IdealSheafData.module Scheme.IdealSheafData.invModule RelEffCartierDiv graphOver graphOver_fst graphOver_snd RelEffCartierDiv.ofPoint graphOver_fst_assoc RelEffCartierDiv.isInvertible_I Scheme.Hom.nonempty_pullback_ker_pow_invModule_iso_of_isIso RelPicard.exists_abelJacobi_of_representsRelSubPic RelPicard.baseChange_points_mul_poincare_compat RelPicard.exists_pic0_equiv_points_abelJacobi_of_curveModel RelPicard.exists_representsRelSubPic_baseChange"
namespace RelPicard
p2m_export "AlgebraicGeometry.RelPicard" "RepresentsRelSubPic algEquivZeroCut algEquivZeroGroupCut BaseChange.κ BaseChange.κ_hom_snd BaseChange.κ_hom_fst pointsSubBasepointModule pointsSubBasepointModule_nil pointsSubBasepointModule_cons exists_abelJacobi_of_representsRelSubPic baseChange_points_mul_poincare_compat exists_pic0_equiv_points_abelJacobi_of_curveModel exists_representsRelSubPic_baseChange"
namespace DictGlue
p2m_open "AlgebraicGeometry.RelPicard AlgebraicGeometry"

set_option maxHeartbeats 6400000 in
set_option synthInstance.maxHeartbeats 1600000 in

theorem essFiniteType_of_curveModel {K : Type u} [Field K] {L : Type v} [Field L] [Algebra K L]
    (M : CurveModel K L) : Algebra.EssFiniteType K L := by
  letI := M.functionFieldAlgebra
  haveI : Algebra.EssFiniteType K M.C.functionField :=
    AlgebraicCurve.essFiniteType_functionField M.toBase
  exact Algebra.EssFiniteType.of_surjective M.ffAlgEquiv.symm.toAlgHom M.ffAlgEquiv.symm.surjective

set_option maxHeartbeats 6400000 in
set_option synthInstance.maxHeartbeats 1600000 in

theorem isConnected_fibre_of_geometricallyConnected {R : Type u} [CommRing R] {A : Scheme.{u}}
    (f : A ⟶ Spec (CommRingCat.of R)) (hgc : GeometricallyConnected f)
    (z : Spec (CommRingCat.of R) ⟶ A) (hz : z ≫ f = 𝟙 _) :
    ∀ s : Spec (CommRingCat.of R), _root_.IsConnected (f.base ⁻¹' {s}) := by
  intro s
  haveI := hgc
  have h := isConnected_range (f.fiberι s).continuous
  rwa [Scheme.Hom.range_fiberι] at h

set_option maxHeartbeats 6400000 in
set_option synthInstance.maxHeartbeats 1600000 in

theorem nonempty_pullback_κ_inv_pointsSubBasepointModule_iso
    (R : Type u) [CommRing R] {C : Scheme.{u}} (c : C ⟶ Spec (CommRingCat.of R))
    [IsSeparated c] [SmoothOfRelativeDimension 1 c]
    (ε : SchemeHomOver (𝟙 (Spec (CommRingCat.of R))) c)
    (K : Type u) [Field K] [Algebra R K]
    (xK : SchemeHomOver (𝟙 (Spec (CommRingCat.of K))) (baseChange R c K)) :
    Nonempty ((Scheme.Modules.pullback (BaseChange.κ c K (𝟙 (Spec (CommRingCat.of K)))).inv).obj
        (pointsSubBasepointModule (a := baseChange R c K) (sectionBaseChange K ε) [xK]) ≅
      (RelEffCartierDiv.ofPoint c (xK.1 ≫ pullback.fst c (specMap R K))
          ((Category.assoc _ _ _).trans ((congrArg (xK.1 ≫ ·) pullback.condition).trans
            ((Category.assoc _ _ _).symm.trans ((congrArg (· ≫ specMap R K) xK.2).trans (Category.id_comp _)))))).lineBundle ⊗
        (RelEffCartierDiv.ofPoint c (specMap R K ≫ ε.1)
          ((Category.assoc _ _ _).trans ((congrArg (specMap R K ≫ ·) ε.2).trans (Category.comp_id _)))).idealModule) := by

  have hx : (xK.1 ≫ pullback.fst c (specMap R K)) ≫ c =
      𝟙 (Spec (CommRingCat.of K)) ≫ specMap R K :=
    (Category.assoc _ _ _).trans ((congrArg (xK.1 ≫ ·) pullback.condition).trans
      ((Category.assoc _ _ _).symm.trans (congrArg (· ≫ specMap R K) xK.2)))
  have hε : (specMap R K ≫ ε.1) ≫ c = 𝟙 (Spec (CommRingCat.of K)) ≫ specMap R K :=
    (Category.assoc _ _ _).trans (((congrArg (specMap R K ≫ ·) ε.2).trans (Category.comp_id _)).trans
      (Category.id_comp _).symm)

  have hpx : graphOver c (xK.1 ≫ pullback.fst c (specMap R K)) hx ≫
      (BaseChange.κ c K (𝟙 (Spec (CommRingCat.of K)))).inv =
        graphOver (baseChange R c K) xK.1 xK.2 := by
    rw [Iso.comp_inv_eq]
    apply pullback.hom_ext
    · rw [graphOver_fst, Category.assoc, BaseChange.κ_hom_fst, graphOver_fst_assoc]
    · rw [graphOver_snd, Category.assoc, BaseChange.κ_hom_snd, graphOver_snd]
  have hpε : graphOver c (specMap R K ≫ ε.1) hε ≫
      (BaseChange.κ c K (𝟙 (Spec (CommRingCat.of K)))).inv =
        graphOver (baseChange R c K) (sectionBaseChange K ε).1 (sectionBaseChange K ε).2 := by
    rw [Iso.comp_inv_eq]
    apply pullback.hom_ext
    · rw [graphOver_fst, Category.assoc, BaseChange.κ_hom_fst, graphOver_fst_assoc,
        sectionBaseChange_coe_fst]
    · rw [graphOver_snd, Category.assoc, BaseChange.κ_hom_snd, graphOver_snd]

  obtain ⟨ex⟩ := (Scheme.Hom.nonempty_pullback_ker_pow_invModule_iso_of_isIso
    (BaseChange.κ c K (𝟙 (Spec (CommRingCat.of K)))).inv
    (graphOver (baseChange R c K) xK.1 xK.2) (graphOver c (xK.1 ≫ pullback.fst c (specMap R K)) hx) hpx
    (RelEffCartierDiv.isInvertible_I (RelEffCartierDiv.ofPoint (baseChange R c K) xK.1 xK.2))
    (RelEffCartierDiv.isInvertible_I (RelEffCartierDiv.ofPoint c (xK.1 ≫ pullback.fst c (specMap R K)) hx))
    1).1
  obtain ⟨eε⟩ := (Scheme.Hom.nonempty_pullback_ker_pow_invModule_iso_of_isIso
    (BaseChange.κ c K (𝟙 (Spec (CommRingCat.of K)))).inv
    (graphOver (baseChange R c K) (sectionBaseChange K ε).1 (sectionBaseChange K ε).2)
    (graphOver c (specMap R K ≫ ε.1) hε) hpε
    (RelEffCartierDiv.isInvertible_I
      (RelEffCartierDiv.ofPoint (baseChange R c K) (sectionBaseChange K ε).1 (sectionBaseChange K ε).2))
    (RelEffCartierDiv.isInvertible_I (RelEffCartierDiv.ofPoint c (specMap R K ≫ ε.1) hε))
    1).2

  have ex' : (Scheme.Modules.pullback (BaseChange.κ c K (𝟙 (Spec (CommRingCat.of K)))).inv).obj
      (RelEffCartierDiv.ofPoint (baseChange R c K) xK.1 xK.2).lineBundle ≅
        (RelEffCartierDiv.ofPoint c (xK.1 ≫ pullback.fst c (specMap R K)) hx).lineBundle :=
    (Scheme.Modules.pullback _).mapIso
        (eqToIso (congrArg Scheme.IdealSheafData.invModule (pow_one _).symm)) ≪≫ ex ≪≫
      eqToIso (congrArg Scheme.IdealSheafData.invModule (pow_one _))
  have eε' : (Scheme.Modules.pullback (BaseChange.κ c K (𝟙 (Spec (CommRingCat.of K)))).inv).obj
      (RelEffCartierDiv.ofPoint (baseChange R c K) (sectionBaseChange K ε).1 (sectionBaseChange K ε).2).idealModule ≅
        (RelEffCartierDiv.ofPoint c (specMap R K ≫ ε.1) hε).idealModule :=
    (Scheme.Modules.pullback _).mapIso
        (eqToIso (congrArg Scheme.IdealSheafData.module (pow_one _).symm)) ≪≫ eε ≪≫
      eqToIso (congrArg Scheme.IdealSheafData.module (pow_one _))

  rw [pointsSubBasepointModule_cons, pointsSubBasepointModule_nil]
  exact ⟨(Scheme.Modules.pullback _).mapIso (ρ_ _) ≪≫ Scheme.Modules.pullbackTensorObjIso _ _ _ ≪≫
    tensorIso ex' eε'⟩

end AlgebraicGeometry.RelPicard.DictGlue

set_option maxHeartbeats 6400000 in
set_option synthInstance.maxHeartbeats 1600000 in

theorem solution
    (R : Type u) [CommRing R]
    {C : Scheme.{u}} (c : C ⟶ Spec (CommRingCat.of R)) [IsProper c]
    [SmoothOfRelativeDimension 1 c] [GeometricallyIntegral c]
    (ε : SchemeHomOver (𝟙 (Spec (CommRingCat.of R))) c)
    (D : RelativePic0Designation R c) (h : RepresentsRelSubPic c ε (algEquivZeroCut c ε) D)
    (hsm : Smooth D.toBase) (hpr : IsProper D.toBase) (hgc : GeometricallyConnected D.toBase) :
    ∃ (L : RelativeGroupLaw R D.toBase) (aj : SchemeHomOver c D.toBase),
      AbelianSchemePropertyBundle R D.toBase ∧
      (∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) (x y : SchemeHomOver t D.toBase),
        L.mul t x y = L.mul t y x) ∧
      (L.one (𝟙 (Spec (CommRingCat.of R)))).1 = D.zeroSection ∧
      ε.1 ≫ aj.1 = D.zeroSection ∧
      ∀ (K : Type u) [Field K] [IsAlgClosed K] (i : R →+* K)
        (F : Type v) [Field F] [Algebra K F] [IsCurveOver K F] (M : CurveModel K F)
        (e : M.C ⟶ pullback c (Spec.map (CommRingCat.ofHom i))) [IsIso e],
        e ≫ pullback.snd c (Spec.map (CommRingCat.ofHom i)) = M.toBase →
        ∃ pts : Pic0 K F ≃ SchemeHomOver (Spec.map (CommRingCat.ofHom i)) D.toBase,
          (∀ x y : Pic0 K F,
            pts (x + y) = L.mul (Spec.map (CommRingCat.ofHom i)) (pts x) (pts y)) ∧
          ∀ (x s : {q : Spec (CommRingCat.of K) ⟶ M.C // q ≫ M.toBase = 𝟙 _}),
            s.1 ≫ e ≫ pullback.fst c (Spec.map (CommRingCat.ofHom i)) =
              Spec.map (CommRingCat.ofHom i) ≫ ε.1 →
            ∃ Dv : Divisor.degZero (K := K) (F := F),
              (Dv : Divisor K F) =
                Finsupp.single (M.pointEquivPlace x) 1 - Finsupp.single (M.pointEquivPlace s) 1 ∧
              (pts (Pic0.mk Dv)).1 =
                x.1 ≫ e ≫ pullback.fst c (Spec.map (CommRingCat.ofHom i)) ≫ aj.1 := by

  let hG : RepresentsRelSubPic c ε (algEquivZeroGroupCut c ε).toSubPicCondition D := h
  haveI : IsSeparated c := inferInstance
  obtain ⟨aj, hajε, hajP⟩ := AlgebraicGeometry.RelPicard.exists_abelJacobi_of_representsRelSubPic R c ε D h
  refine ⟨hG.relativeGroupLaw, aj, ?_, ?_, hG.relativeGroupLaw_one, ?_, ?_⟩
  ·
    exact ⟨hsm, hpr, DictGlue.isConnected_fibre_of_geometricallyConnected D.toBase hgc D.zeroSection D.zeroSection_toBase,
      ⟨hG.relativeGroupLaw⟩⟩
  ·
    intro T t x y
    exact hG.relativeGroupLaw_isCommutative t x y
  ·
    exact hajε
  ·
    intro K _ _ i F _ _ _ M e _ he
    letI : Algebra R K := i.toAlgebra
    haveI : Algebra.EssFiniteType K F := DictGlue.essFiniteType_of_curveModel M

    obtain ⟨h', hP'⟩ := AlgebraicGeometry.RelPicard.exists_representsRelSubPic_baseChange R c ε D h K
    obtain ⟨Θ, hΘ1, hΘmul, hΘP⟩ := AlgebraicGeometry.RelPicard.baseChange_points_mul_poincare_compat R c ε D h K h' hP'

    let eI : M.C ≅ pullback c (specMap R K) := asIso e
    have heI : eI.hom ≫ baseChange R c K = M.toBase := he
    let εK : SchemeHomOver (𝟙 (Spec (CommRingCat.of K))) (baseChange R c K) := sectionBaseChange K ε
    let ε'ₘ : {p : Spec (CommRingCat.of K) ⟶ M.C // p ≫ M.toBase = 𝟙 _} :=
      ⟨εK.1 ≫ inv e, by rw [Category.assoc, ← heI]; show εK.1 ≫ inv e ≫ e ≫ _ = _; rw [IsIso.inv_hom_id_assoc]; exact εK.2⟩
    have hε'ₘ : ε'ₘ.1 ≫ eI.hom = εK.1 := by show (εK.1 ≫ inv e) ≫ e = εK.1; rw [Category.assoc, IsIso.inv_hom_id, Category.comp_id]
    obtain ⟨pts, hadd, hAJ, -⟩ :=
      AlgebraicGeometry.RelPicard.exists_pic0_equiv_points_abelJacobi_of_curveModel K (baseChange R c K) εK
        (D.baseChange K) h' M eI heI ε'ₘ hε'ₘ
    refine ⟨pts.trans Θ, fun x y => ?_, fun x s hs => ?_⟩
    · show Θ (pts (x + y)) = _
      rw [hadd, hΘmul]
      rfl
    ·
      have hsK : s.1 ≫ e = εK.1 := by
        apply pullback.hom_ext
        · rw [Category.assoc]
          exact hs.trans (sectionBaseChange_coe_fst (R := R) K ε).symm
        · rw [Category.assoc]
          show s.1 ≫ e ≫ baseChange R c K = εK.1 ≫ pullback.snd _ _
          rw [he, s.2]
          exact (sectionBaseChange_coe_snd (R := R) K ε).symm
      have hsε : s = ε'ₘ := by
        apply Subtype.ext
        show s.1 = εK.1 ≫ inv e
        rw [← hsK, Category.assoc, IsIso.hom_inv_id, Category.comp_id]
      subst hsε
      have hdeg1 : ∀ v : Place K F, v.deg = 1 := IsCurveOver.deg_eq_one_of_isAlgClosed
      have hDv : Finsupp.single (M.pointEquivPlace x) 1 - Finsupp.single (M.pointEquivPlace ε'ₘ) 1 ∈
          Divisor.degZero (K := K) (F := F) := by
        rw [Divisor.mem_degZero, map_sub, Divisor.degree_single, Divisor.degree_single, hdeg1, hdeg1]
        simp
      refine ⟨⟨Finsupp.single (M.pointEquivPlace x) 1 - Finsupp.single (M.pointEquivPlace ε'ₘ) 1, hDv⟩, rfl, ?_⟩
      ·
        obtain ⟨iAJ⟩ := hAJ [x] ⟨_, hDv⟩ (by
          show Finsupp.single (M.pointEquivPlace x) (1 : ℤ) - Finsupp.single (M.pointEquivPlace ε'ₘ) 1 = _
          simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero, List.length_cons,
            List.length_nil, zero_add, Nat.cast_one, one_smul])

        let xK : SchemeHomOver (𝟙 (Spec (CommRingCat.of K))) (baseChange R c K) :=
          ⟨x.1 ≫ eI.hom, (Category.assoc _ _ _).trans ((congrArg (x.1 ≫ ·) heI).trans x.2)⟩
        let xR : SchemeHomOver (specMap R K) c :=
          ⟨xK.1 ≫ pullback.fst c (specMap R K),
            (Category.assoc _ _ _).trans ((congrArg (xK.1 ≫ ·) pullback.condition).trans
              ((Category.assoc _ _ _).symm.trans ((congrArg (· ≫ specMap R K) xK.2).trans (Category.id_comp _))))⟩
        obtain ⟨iR⟩ := hajP K (specMap R K) xR
        obtain ⟨iΘ⟩ := hΘP (pts (Pic0.mk ⟨_, hDv⟩))

        have key : Θ (pts (Pic0.mk ⟨Finsupp.single (M.pointEquivPlace x) 1 - Finsupp.single (M.pointEquivPlace ε'ₘ) 1, hDv⟩)) =
            ⟨xR.1 ≫ aj.1, (Category.assoc _ _ _).trans ((congrArg (xR.1 ≫ ·) aj.2).trans xR.2)⟩ := by
          apply h.ext_of_iso (specMap R K)
          obtain ⟨iM⟩ := DictGlue.nonempty_pullback_κ_inv_pointsSubBasepointModule_iso R c ε K xK
          exact ⟨iΘ ≪≫ (Scheme.Modules.pullback (BaseChange.κ c K (𝟙 _)).inv).mapIso iAJ ≪≫ iM ≪≫ iR.symm⟩
        show (Θ (pts (Pic0.mk ⟨_, hDv⟩))).1 = _
        rw [key]
        show ((x.1 ≫ e) ≫ pullback.fst c (specMap R K)) ≫ aj.1 = _
        simp only [Category.assoc]

end
end S_AlgebraicGeometry_RelPicard_exists_relativeGroupLaw_abelJacobi_of_representsRelSubPic
end P2MW
export P2MW.S_AlgebraicGeometry_RelPicard_exists_relativeGroupLaw_abelJacobi_of_representsRelSubPic (solution)
