-- Prove2me | solution 1 for AlgebraicCurve.Pic0.abelJacobiCard_genusFF_of_frobenius_of_isAlgebraic
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:01.734404+00:00
-- url     : https://prove2.me/submissions/8caf3efc-6a4d-5fbe-b689-33db31048613

import Mathlib
import Definitions.Def_AlgebraicCurve_Correspondence
import Definitions.Def_AlgebraicCurve_IsCurveOver
import Definitions.Def_AlgebraicCurve_Repartitions
import Definitions.Def_AlgebraicCurve_DivisorClassGroup
import Definitions.Def_AlgebraicCurve_FrobeniusEndoPic0
import Definitions.Def_AlgebraicCurve_AdelicIndex
import Theorems.Thm_AlgebraicCurve_Pic0_exists_monic_natCard_fixedPoints_iterate_eq_resultant_of_pushforwardAlong_frobenius
import Theorems.Thm_AlgebraicCurve_constantsAreBase_of_apply_algebraMap_eq_pow_card
import Theorems.Thm_AddCommGroup_natCard_torsionBy_pow_eq_pow_of_natCard_fixed_primaryComponent
import Theorems.Thm_AddCommGroup_finite_and_natCard_torsionBy_le_of_natCard_fixed_primaryComponent_le_of_divisible
import Theorems.Thm_Polynomial_exists_factorization_resultant_X_pow_sub_one_eq_mul_add_of_not_dvd
import Theorems.Thm_AlgebraicCurve_Pic0_exists_iterate_apply_eq_self_of_pushforwardAlong_frobenius_of_isAlgebraic
import Theorems.Thm_AlgebraicCurve_Pic0_exists_nsmul_eq_of_charP
import Theorems.Thm_AlgebraicCurve_IsCurveOver_exists_separating_transcendental
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicCurve_Pic0_abelJacobiCard_genusFF_of_frobenius_of_isAlgebraic
p2m_attr_erase "instance" "AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation instDecEqAlgebraicClosureRat WeierstrassCurve.Affine.Point.instDistribMulActionAlgEquiv WeierstrassCurve.Affine.Point.instModuleZModTorsionBy WeierstrassCurve.Affine.Point.instSMulTorsionBy WeierstrassCurve.Affine.Point.instDistribMulActionTorsionBy WeierstrassCurve.Affine.Point.instSMulAlgEquiv WeierstrassCurve.Affine.Point.instSMulCommClassAlgEquivZModTorsionBy AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions AlgebraicCurve.CurveModel.isProper AlgebraicCurve.CurveModel.isIntegral AlgebraicCurve.CurveModel.smooth AlgebraicCurve.CurveModel.locallyOfFiniteType_gluedToBase AlgebraicCurve.CurveModel.isFractionRing_overlap AlgebraicCurve.CurveModel.isLocallyNoetherian_glued AlgebraicCurve.CurveModel.jacobsonSpace_glued AlgebraicCurve.CurveModel.isOpenImmersion_ι₀ AlgebraicCurve.CurveModel.isIntegral_glued AlgebraicCurve.CurveModel.quasiSeparated_gluedToBase AlgebraicCurve.CurveModel.compactSpace_glued AlgebraicCurve.CurveModel.isIntegral_adjoin_chartRing AlgebraicCurve.CurveModel.isFractionRing_overlap_functionField AlgebraicCurve.CurveModel.isProper_gluedToBase AlgebraicCurve.CurveModel.isOpenImmersion_ιU AlgebraicCurve.CurveModel.isOpenImmersion_f₀ AlgebraicCurve.CurveModel.isOpenImmersion_fInf AlgebraicCurve.CurveModel.isOpenImmersion_ιInf AlgebraicCurve.CurveModel.algebra_overlap_functionField AlgebraicCurve.CurveModel.quasiCompact_gluedToBase AlgebraicCurve.CurveModel.algebraAdjoin AlgebraicCurve.CurveModel.isDedekindDomain_chartRing AlgebraicCurve.CurveModel.isIntegralClosure AlgebraicCurve.CurveModel.finite_chartRing AlgebraicCurve.CurveModel.centre_isPrime"
p2m_attr_erase "instance" "AlgebraicCurve.CurveModel.isFractionRing_chartRing AlgebraicCurve.CurveModel.finiteType_chartRing AlgebraicCurve.CurveModel.isNoetherianRing_chartRing AlgebraicCurve.CurveModel.isScalarTower_base_adjoin AlgebraicCurve.CurveModel.isScalarTower_adjoin AlgebraicCurve.CurveModel.chartRing_finitePresentation AlgebraicGeometry.Scheme.Hom.opensMapFinal AlgebraicGeometry.RelPicard.RigidifiedLineBundle.setoid AlgebraicGeometry.RelPicard.RigidifiedLineBundle.instInhabited AlgebraicGeometry.Scheme.PresheafOfModules.symmetricCategory SheafOfModules.instFaithfulRingSheafPModToPMod SheafOfModules.symmetricCategory AlgebraicGeometry.Scheme.PresheafOfModules.monoidalCategory AlgebraicGeometry.Scheme.PresheafOfModules.monoidalClosed SheafOfModules.instFullRingSheafPModToPMod SheafOfModules.monoidalCategory AlgebraicGeometry.Scheme.Modules.symmetricCategory SheafOfModules.monoidalClosed SheafOfModules.instIsLocalizationPModRingSheafSheafifyFunctorPresheafW SheafOfModules.sheafifyFunctor_monoidal AlgebraicGeometry.Scheme.Modules.monoidalClosed AlgebraicGeometry.instMonoidalPresheafOfModulesModulesSheafify AlgebraicGeometry.Scheme.Modules.monoidalCategory PresheafOfModules.instMonoidalClosed PresheafOfModules.InternalHom.instModuleCarrierObjOppositeCommRingCatSubtypePiFamilyMemAddSubgroupNaturalFamilies PresheafOfModules.InternalHom.instModuleCarrierObjOppositeRingCatCompCommRingCatForget₂RingHomCarrierCarrierAbPresheaf PresheafOfModules.InternalHom.instSMulCarrierObjOppositeCommRingCatSubtypePiFamilyMemAddSubgroupNaturalFamilies AlgebraicGeometry.Scheme.Modules.preservesBinaryProducts_opensMap AlgebraicGeometry.Scheme.Modules.pullback_monoidal AlgebraicGeometry.Scheme.Modules.sheafify_isLocalization' AlgebraicGeometry.Scheme.Modules.preservesTerminal_opensMap AlgebraicGeometry.Scheme.Modules.pullback₀_monoidal AlgebraicGeometry.Scheme.Modules.preservesFiniteProducts_opensMap AlgebraicGeometry.Scheme.Modules.instLiftingPresheafOfModulesSheafifyPresheafWOpensCarrierCarrierCommRingCatGrothendieckTopologyObjFunctorOppositeIsSheafSheafCompPullback₀Pullback PresheafOfModules.PullbackMonoidal.pullback_monoidal PresheafOfModules.PullbackMonoidal.isIso_δ PresheafOfModules.pushforward_laxMonoidal PresheafOfModules.PullbackMonoidal.isIso_η PresheafOfModules.free_monoidal PresheafOfModules.restrictScalars_laxMonoidal"
p2m_attr_erase "instance" "PresheafOfModules.PullbackMonoidal.isIso_δ_gS PresheafOfModules.pullback_oplaxMonoidal PresheafOfModules.PullbackMonoidal.instPreservesColimitsOfSizeCompOppositeCommRingCatRingCatForget₂RingHomCarrierCarrierPb PresheafOfModules.pullback_monoidal' AlgebraicGeometry.RelEffCartierDiv.isIso_subschemeIota_snd_of_degree_one AlgebraicGeometry.isIso_ker_graphOver_subschemeIota_snd AlgebraicGeometry.isClosedImmersion_graphOver AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instNeg AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instSMulInt AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instAddCommGroup AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instAdd AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instSub AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instModuleCarrierObjOppositeOpensCarrierCarrierCommRingCatPresheafOpOpensTop AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instSMulCarrierObjOppositeOpensCarrierCarrierCommRingCatPresheafOpOpensTop AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instSMulNat AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instZero AlgebraicGeometry.SmoothOfRelativeDimension.fiberToSpecResidueField AlgebraicGeometry.SmoothOfRelativeDimension.pullback_snd AlgebraicGeometry.SmoothOfRelativeDimension.pullback_fst AlgebraicGeometry.SmoothOfRelativeDimension.smooth_one AlgebraicGeometry.SmoothProperCurve.isIntegral_pullback_Spec_field AlgebraicGeometry.IsProper.fiberToSpecResidueField TwoChartCech.Sections.M0_moduleA TwoChartCech.Sections.M1_module TwoChartCech.Cover.A01_algebra TwoChartCech.Cover.A0_algebra TwoChartCech.Cover.A1_commRing TwoChartCech.Cover.A1_algebra TwoChartCech.Sections.M01_module TwoChartCech.Sections.M0_addCommGroup TwoChartCech.Sections.M0_tower TwoChartCech.Sections.M01_addCommGroup TwoChartCech.Cover.A0_commRing TwoChartCech.Sections.M1_tower TwoChartCech.Sections.M01_moduleA TwoChartCech.Sections.M0_module TwoChartCech.Sections.M1_moduleA TwoChartCech.Sections.M1_addCommGroup TwoChartCech.Cover.A01_commRing TwoChartCech.Sections.M01_tower"
p2m_attr_erase "instance" "CoherentBaseChange.TwoTermComplex.C0_module CoherentBaseChange.TwoTermComplex.C0_addCommGroup CoherentBaseChange.TwoTermComplex.C1_module CoherentBaseChange.TwoTermComplex.C1_addCommGroup CoherentBaseChange.TwoTermComplex.C0_free CoherentBaseChange.TwoTermComplex.C1_finite CoherentBaseChange.TwoTermComplex.C0_finite CoherentBaseChange.TwoTermComplex.C1_free AlgebraicGeometry.Scheme.LocalRepresentabilityULift.instIsLocallyInjectiveFunUliftYonedaGluedToSheaf AlgebraicGeometry.Scheme.LocalRepresentabilityULift.instIsLocallySurjectiveFunUliftYonedaGluedToSheafOfIsLocallySurjectiveZariskiTopologyDescFunctorOppositeType AlgebraicGeometry.Scheme.LocalRepresentabilityULift.instIsOpenImmersionToGlued AlgebraicGeometry.Scheme.LocalRepresentabilityULift.instIsIsoSheafZariskiTopologyTypeUliftYonedaGluedToSheaf AlgebraicGeometry.RelPicard.instIsOpenImmersionToGlued PresheafOfModules.ExteriorPower.instModulePresheafAb AlgebraicGeometry.RelEffCartierDiv.subsingleton_of_degree_zero AlgebraicGeometry.FGSubalgebra.instIsDirectedLe AlgebraicGeometry.FGSubalgebra.instQuasiSeparatedSpaceCarrierCarrierCommRingCatObjOppositeSchemeSpecDiagram AlgebraicGeometry.FGSubalgebra.instIsCofilteredOpposite AlgebraicGeometry.FGSubalgebra.instIsAffineObjOppositeSchemeSpecDiagram AlgebraicGeometry.FGSubalgebra.instNonempty AlgebraicGeometry.FGSubalgebra.instNonemptySubtypeLeSubalgebraValFG AlgebraicGeometry.FGSubalgebra.instCompactSpaceCarrierCarrierCommRingCatObjOppositeSchemeSpecDiagram AlgebraicGeometry.FGSubalgebra.instIsDirectedSubtypeLeSubalgebraValFG AlgebraicGeometry.FGSubalgebra.instIsAffineHomMapOppositeSchemeSpecDiagram AlgebraicGeometry.FGSubalgebra.instIsFiltered AlgebraicCurve.instHasLocalResidue_of_hasCanonicalLocalResidueK AlgebraicCurve.instHasCanonicalLocalResidueK_of_hasCanonicalLocalResidueKStar AlgebraicCurve.Place.kw_ffgc_finiteDimensional_adicCompletion instAlgebraSubtypeMemValuationSubring_definitions AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersIntegersCompletion ModularCurve.KwF4gRRTate.instAlgebraKAdicCompletionIntegers AlgebraicCurve.Place.kw_ffgc_continuousSMul_adicCompletionComap AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersCompletionCompletion IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions AlgebraicCurve.instHasCanonicalLocalResidueK"
p2m_attr_erase "instance" "AlgebraicCurve.Place.instAlgebra_restrictResidueField AlgebraicCurve.Place.instIsScalarTower_restrictResidueField AlgebraicCurve.instHasLocalResidue AlgebraicCurve.HasSeparableResidue.of_perfectField_of_isCurveOver AlgebraicCurve.HasSeparableResidue.of_perfectField AlgebraicCurve.Place.instIsLocalHom_restrictSubringHom AlgebraicCurve.instHasCanonicalLocalResidueKStar ModularCurve.KwNo6Pin.isLocalRing_completion SheafOfModules.isIso_ihomModelToIhom AlgebraicGeometry.OModulePresheaf.isScalarTower AlgebraicGeometry.Scheme.OrderedAffineCover.instLinearOrder AlgebraicGeometry.OModulePresheaf.module AlgebraicGeometry.Scheme.OrderedAffineCover.instFintype AlgebraicGeometry.Scheme.OrderedAffineCover.instFintypeIdx AlgebraicGeometry.OModulePresheaf.addCommGroup AlgebraicGeometry.Scheme.OrderedAffineCover.instDecidableEqIdx AlgebraicGeometry.OModulePresheaf.moduleSections AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instDecidableEqIdx AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instFintype AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instLinearOrder AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instFintypeIdx AlgebraicGeometry.OModulePresheaf.instSubsingletonObjZero AlgebraicGeometry.OModulePresheaf.Leray.relAltC_scalarTower AlgebraicGeometry.OModulePresheaf.Leray.ker_relAltd_modΓ AlgebraicGeometry.OModulePresheaf.Leray.relAltC_modΓ AlgebraicGeometry.OModulePresheaf.Leray.biC_abGrp AlgebraicGeometry.OModulePresheaf.Leray.relAltH_modΓ AlgebraicGeometry.OModulePresheaf.Leray.ker_relAltd_smul AlgebraicGeometry.OModulePresheaf.Leray.relAltH_scalarTower AlgebraicGeometry.OModulePresheaf.Leray.relAltH_smul AlgebraicGeometry.OModulePresheaf.Leray.biC_module DoubleComplex.instModuleE₂I DoubleComplex.Bounded.modR DoubleComplex.instModuleE₂II DoubleComplex.instAddCommGroupE₂II DoubleComplex.Bounded.abGrp DoubleComplex.instAddCommGroupE₂I AlgebraicGeometry.ChowDatum.hι_closed AlgebraicGeometry.ChowDatumProj.hιN_closed AlgebraicGeometry.ChowDatumProj.hp_proper"
p2m_attr_erase "instance" "AlgebraicGeometry.ChowDatum.hp_isoU AlgebraicGeometry.ChowDatum.hp_proper AlgebraicGeometry.ProjSpace.algebraAway AlgebraicGeometry.ProjSpace.instIsProperProdOverπ AlgebraicGeometry.ChowDatumProj.hp_isoU AlgebraicGeometry.ProjSpace.isProper_π AlgebraicGeometry.ProjSpace.finiteType_mvPolynomial ProjSpaceCech.GradedModule.H.module ProjSpaceCech.GradedModule.H.addCommGroup ProjSpaceCech.GradedModule.sec.instAdd ProjSpaceCech.GradedModule.sec.instNeg ProjSpaceCech.GradedModule.acg ProjSpaceCech.GradedModule.Frac.setoid ProjSpaceCech.GradedModule.modR ProjSpaceCech.GradedModule.sec.instModule ProjSpaceCech.GradedModule.sec.instAddCommGroup ProjSpaceCech.GradedModule.sec.instZero ProjSpaceCech.GradedModule.Presentation.fJ ProjSpaceCech.GradedModule.sec.instSMul ProjSpaceCech.Twist.H.module ProjSpaceCech.Idx.instFintype ProjSpaceCech.Twist.H.addCommGroup ProjSpaceCech.Idx.instDecidableEq ProjSpaceCech.Twist.Mon.instDecidableEq ProjSpaceCech.Twist.cochain.instAddCommGroup ProjSpaceCech.Twist.cochain.instModule AlgebraicGeometry.FGSubalgebra.tensorStage_directedSystem AlgebraicGeometry.RelEffCartierDiv.isClosedImmersion_subschemeι_resProdMap AlgebraicGeometry.RelEffCartierDiv.isOpenImmersion_resProdMap kmfloorsGlue_int_three_isPrime kmfloorsGlue_int_bot_isPrime instTopologicallyFGOfFiniteType"
p2m_attr_erase "simp" "AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal AlgebraicCurve.Pic.baseChange_mk AlgebraicCurve.Place.forgetConstants_toValuationSubring AlgebraicCurve.Place.constantFieldEquiv_symm_apply AlgebraicCurve.Place.ord_forgetConstants AlgebraicCurve.Place.extendConstants_toValuationSubring AlgebraicCurve.Place.constantFieldEquiv_apply_toValuationSubring AlgebraicCurve.Place.mem_fiberConstants AlgebraicCurve.Place.restrictConstants_toValuationSubring AlgebraicCurve.IsFrobeniusEndo.frobNormRingHom_apply ModularCurve.frobeniusPushforwardGeomLevelPic0_mk ModularCurve.coe_frobeniusGeomLevelEquiv_apply ModularCurve.coe_frobeniusPushforwardGeomLevelDegZero ModularCurve.heckeFibreGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusGeomLevel_apply_coe ModularCurve.frobeniusPullbackGeomLevelPic0OfIsCurveOver_mk ModularCurve.coe_heckeFibreGeomLevelDegZero ModularCurve.coe_frobeniusPullbackGeomLevelDegZero ModularCurve.frobeniusPullbackGeomLevelPic0_mk ModularCurve.frobeniusPullbackGeomLevel_single ModularCurve.heckeFibreGeomLevelPic0_mk ModularCurve.frobeniusPushforwardGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusPushforwardGeomLevel_single ModularCurve.qExpandAlgC_apply AlgebraicCurve.Place.congrEquiv_symm_apply AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply AlgebraicCurve.RationalFunctionField.deg_placeOfPoint ModularCurve.jqNModC_one ModularCurve.qExpand_coeff_mul ModularCurve.qExpandₐ_apply ModularCurve.jqN_one ModularCurve.qExpand_single ModularCurve.dedekindPsi_one"
p2m_attr_erase "simp" "ModularCurve.ModularPolynomialData.mk.sizeOf_spec ModularCurve.evalAtJ_X ModularCurve.ModularPolynomialData.mk.injEq ModularCurve.constantCoeff_jNum ModularCurve.constantCoeff_eisenstein4 ModularCurve.qExpand_C ModularCurve.coeff_jq_neg_one ModularCurve.constantCoeff_jNumQ ModularCurve.reduceModBivar_C_X ModularCurve.laurentMap_coeff ModularCurve.reduceModBivar_X ModularCurve.laurentMap_single ModularCurve.evalAtJInt_X ModularCurve.evalAtJMod_X ModularCurve.jqNMod_one ModularCurve.aeval_heckeGen ModularCurve.coe_mTorsionGaloisRep_apply ModularCurve.eisensteinSystem_of_dvd ModularCurve.eisensteinSystem_of_not_dvd FreyPackage.mk.sizeOf_spec FreyPackage.mk.injEq WeierstrassCurve.Affine.Point.galoisRepModuleEnd_apply AlgebraicCurve.RationalFunctionField.placeInfty_toValuationSubring AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none AlgebraicCurve.Divisor.evalFun_zero AlgebraicCurve.Place.evalAt_one AlgebraicCurve.TranscendenceTower.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.injEq AlgebraicCurve.TranscendenceTower.mk.injEq AlgebraicCurve.PoleDivisorPackage.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.sizeOf_spec AlgebraicCurve.PoleDivisorPackage.mk.injEq AlgebraicCurve.Divisor.congr_single AlgebraicCurve.Pic0.coe_degZeroCongr_symm AlgebraicCurve.Divisor.degree_congr AlgebraicCurve.Divisor.degree_congr_symm AlgebraicCurve.Pic0.coe_degZeroCongr"
p2m_attr_erase "simp" "AlgebraicCurve.CurveModel.mk.injEq AlgebraicCurve.CurveModel.mk.sizeOf_spec AlgebraicCurve.CurveModel.coe_gInf AlgebraicCurve.CurveModel.coe_tInvChart AlgebraicCurve.CurveModel.ιInf_gluedToBase_assoc AlgebraicCurve.CurveModel.ιInf_gluedToBase AlgebraicCurve.CurveModel.primeOfι₀_asIdeal AlgebraicCurve.CurveModel.coe_tChart AlgebraicCurve.CurveModel.ι₀_gluedToBase_assoc AlgebraicCurve.CurveModel.primeOfιInf_asIdeal AlgebraicCurve.CurveModel.ι₀_gluedToBase AlgebraicCurve.CurveModel.coe_tma AlgebraicCurve.CurveModel.coe_primeEquivChartPlaces GoodReductionJacobian.RelativePic0Designation.mk.sizeOf_spec GoodReductionJacobian.AvatarSchemeBridge.mk.injEq MilneJVScheme.JacobianSchemeData.mk.injEq GoodReductionJacobian.AvatarSchemeBridge.mk.sizeOf_spec MilneJVScheme.JacobianSchemeData.mk.sizeOf_spec GoodReductionJacobian.RelativePic0Designation.mk.injEq NeronModelInfra.specGenericFibreInclusion_eq NeronModelInfra.genericFibreRestrict_coe_comp_snd NeronModelInfra.genericFibreRestrict_coe_comp_fst GoodReductionJacobian.schemeHomOverComp_coe NeronModelInfra.schemeHomOverEquivOverHom_apply GoodReductionJacobian.RelativeGroupLaw.mk.sizeOf_spec NeronModelInfra.schemeHomOverEquivOverHom_symm_apply NeronModelInfra.overHomToSchemeHomOver_coe GoodReductionJacobian.RelativeGroupLaw.mk.injEq NeronModelInfra.overHomToSchemeHomOver_schemeHomOverToOverHom NeronModelInfra.schemeHomOverToOverHom_left NeronModelInfra.schemeHomOverToOverHom_overHomToSchemeHomOver GoodReductionJacobian.RelativeGroupLaw.nsmul_zero GoodReductionJacobian.RelativeGroupLaw.mem_torsionSubset GoodReductionJacobian.RelativeGroupLaw.nsmul_succ AlgebraicGeometry.RelPicard.SubPicGroupCondition.mk.injEq AlgebraicGeometry.RelPicard.SubPicGroupCondition.mk.sizeOf_spec AlgebraicGeometry.RelPicard.RigidifiedLineBundle.mk.sizeOf_spec AlgebraicGeometry.RelPicard.RigidifiedLineBundle.mk.injEq AlgebraicGeometry.RelPicard.RepresentsRelSubPic.mk.injEq AlgebraicGeometry.RelPicard.SubPicCondition.mk.injEq"
p2m_attr_erase "simp" "AlgebraicGeometry.RelPicard.SubPicCondition.mk.sizeOf_spec AlgebraicGeometry.RelPicard.RepresentsRelSubPic.mk.sizeOf_spec AlgebraicGeometry.RelPicard.SubPicCondition.onClasses_mk AlgebraicGeometry.RelPicard.relSubPicPresheaf_map_coe GoodReductionJacobian.relativeGroupLawOfGrpObj_inv GoodReductionJacobian.relativeGroupLawOfGrpObj_mul GoodReductionJacobian.overHomEquivSchemeHomOver_apply_coe GoodReductionJacobian.relativeGroupLawOfGrpObj_one GoodReductionJacobian.overHomEquivSchemeHomOver_symm_apply_left SheafOfModules.tensorUnit_eq AlgebraicGeometry.Scheme.Modules.tensorUnit_eq PresheafOfModules.InternalHom.presheaf_map_apply PresheafOfModules.InternalHom.curryFamily_app PresheafOfModules.InternalHom.add_app PresheafOfModules.InternalHom.smul_app PresheafOfModules.InternalHom.zero_app PresheafOfModules.ihomObj_map_val PresheafOfModules.ihomFunctor_map PresheafOfModules.InternalHom.restrict_app PresheafOfModules.InternalHom.postcomp_app PresheafOfModules.InternalHom.neg_app PresheafOfModules.curry'_app_val PresheafOfModules.InternalHom.presheaf_obj PresheafOfModules.ihomFunctor_obj PresheafOfModules.ihomObj_obj PresheafOfModules.InternalHom.sub_app PresheafOfModules.ihomMap_app_val PresheafOfModules.freeεIso_hom_app PresheafOfModules.freeμIso_hom_app AlgebraicGeometry.RelPicard.algEquivZeroGroupCut_toSubPicCondition AlgebraicGeometry.RelEffCartierDiv.toRelEffDivisor_ofRelEffDivisor AlgebraicGeometry.RelEffCartierDiv.toRelEffDivisor_I AlgebraicGeometry.mapOnProdOver_fst_assoc AlgebraicGeometry.RelEffCartierDiv.mk.sizeOf_spec AlgebraicGeometry.RelEffCartierDiv.mk.injEq AlgebraicGeometry.mapOnProdOver_snd AlgebraicGeometry.mapOnProdOver_fst AlgebraicGeometry.mapOnProdOver_snd_assoc AlgebraicGeometry.mapOnProdOver_id AlgebraicCurve.RelEffDivisor.mk.sizeOf_spec"
p2m_attr_erase "simp" "AlgebraicCurve.mapOnProd_fst AlgebraicCurve.mapOnProd_fst_assoc AlgebraicCurve.mapOnProd_snd AlgebraicCurve.UnivDivisorPack.mk.injEq AlgebraicCurve.RelEffDivisor.mk.injEq AlgebraicCurve.UnivDivisorPack.mk.sizeOf_spec AlgebraicCurve.mapOnProd_snd_assoc AlgebraicGeometry.graphOver_fst_assoc AlgebraicGeometry.RelEffCartierDiv.toPoint_comp AlgebraicGeometry.RelEffCartierDiv.toPoint_comp_assoc AlgebraicGeometry.graphOver_fst AlgebraicGeometry.RelEffCartierDiv.ofPoint_I AlgebraicGeometry.graphOver_snd AlgebraicGeometry.graphOver_snd_assoc AlgebraicGeometry.RelPicard.fst_toProdSpec AlgebraicGeometry.RelPicard.toProdSpec_fst_assoc AlgebraicGeometry.RelPicard.pointsSubBasepointModule_cons AlgebraicGeometry.RelPicard.pointsSubBasepointModule_nil AlgebraicGeometry.RelPicard.fst_toProdSpec_assoc AlgebraicGeometry.RelPicard.toProdSpec_fst AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.sub_app AlgebraicGeometry.Scheme.IdealSheafData.sres_sresTop AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.add_app AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.mk.sizeOf_spec AlgebraicGeometry.Scheme.IdealSheafData.coe_resLE AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.smul_app AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.coe_ofLE_app AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.ideal_range AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.zero_app AlgebraicGeometry.Scheme.IdealSheafData.sres_sres AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.comp_app AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.neg_app AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.id_app AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.coe_mulRight_app AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.nsmul_app AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.mk.injEq AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.zsmul_app AlgebraicGeometry.SmoothProperCurve.sectionBaseChange_coe_snd AlgebraicGeometry.SmoothProperCurve.sectionBaseChange_coe_fst AlgebraicGeometry.SmoothProperCurve.FiniteMapData.twoAffineOpenCover_U1"
p2m_attr_erase "simp" "AlgebraicGeometry.SmoothProperCurve.FiniteMapData.mk.injEq AlgebraicGeometry.SmoothProperCurve.FiniteMapData.mk.sizeOf_spec AlgebraicGeometry.SmoothProperCurve.FiniteMapData.twoAffineOpenCover_U0 AlgebraicGeometry.Scheme.TwoAffineOpenCover.mk.injEq AlgebraicGeometry.Scheme.TwoAffineOpenCover.mk.sizeOf_spec AlgebraicGeometry.Scheme.TwoAffineOpenCover.pullback_U1 AlgebraicGeometry.Scheme.TwoAffineOpenCover.pullback_U0 TwoChartCech.Sections.mk.injEq TwoChartCech.Cover.mk.injEq TwoChartCech.GrothendieckComplex.mk.injEq TwoChartCech.Sections.mk.sizeOf_spec TwoChartCech.Cover.mk.sizeOf_spec TwoChartCech.Cover.lineBundle_r0_apply TwoChartCech.GrothendieckComplex.mk.sizeOf_spec TwoChartCech.Cover.lineBundle_r1_apply CoherentBaseChange.TwoTermComplex.mk.sizeOf_spec CoherentBaseChange.TwoTermComplex.mk.injEq CategoryTheory.Functor.OverTotal.ofFibre_fst CategoryTheory.Functor.overTotal_map_fst AlgebraicGeometry.Scheme.LocalRepresentabilityULift.glueData_J AlgebraicGeometry.Scheme.LocalRepresentabilityULift.uliftYoneda_toGlued_uliftYonedaGluedToSheaf AlgebraicGeometry.Scheme.LocalRepresentabilityULift.glueData_t' AlgebraicGeometry.Scheme.LocalRepresentabilityULift.uliftYoneda_toGlued_uliftYonedaGluedToSheaf_assoc AlgebraicGeometry.Scheme.LocalRepresentabilityULift.uliftYonedaGluedToSheaf_app_toGlued AlgebraicGeometry.Scheme.LocalRepresentabilityULift.glueData_openCover_map AlgebraicGeometry.Scheme.LocalRepresentabilityULift.uliftYonedaGluedToSheaf_app_comp AlgebraicGeometry.Scheme.LocalRepresentabilityULift.glueData_V AlgebraicGeometry.Scheme.LocalRepresentabilityULift.glueData_t AlgebraicGeometry.Scheme.LocalRepresentabilityULift.glueData_U AlgebraicGeometry.Scheme.LocalRepresentabilityULift.glueData_f AlgebraicGeometry.RelPicard.designationOfRepresentableBy_P AlgebraicGeometry.RelPicard.designationOfRepresentableBy_toBase AlgebraicGeometry.RelPicard.rigSection_snd AlgebraicGeometry.RelPicard.RigidifiedLineBundle.ofInvertible_L AlgebraicGeometry.RelPicard.rigSection_snd_assoc AlgebraicCurve.coe_cechH0Equiv_apply AlgebraicCurve.cechH1ToH1_mk AlgebraicCurve.lSpaceOn_univ AlgebraicCurve.lSpaceOn_empty AlgebraicGeometry.RelPicard.thetaBundle_def"
p2m_attr_erase "simp" "AlgebraicGeometry.RelPicard.picardBundle_def AlgebraicGeometry.Scheme.Modules.exteriorPower_obj PresheafOfModules.exteriorPower_map_ιMulti PresheafOfModules.ExteriorPower.appₗ_apply AlgebraicGeometry.prodKerGraph_one AlgebraicGeometry.fibrePowOver.proj_comp AlgebraicGeometry.prodKerGraph_zero AlgebraicGeometry.RelEffCartierDiv.empty_I AlgebraicGeometry.fibrePowOver.proj_comp_assoc AlgebraicCurve.SymmetricPowerPackage.mk.sizeOf_spec AlgebraicCurve.SymmetricPowerPackage.mk.injEq AlgebraicGeometry.FGSubalgebra.cocone_ι_app_apply AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.sizeOf_spec AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.injEq AlgebraicCurve.adeleSingle_coe AlgebraicCurve.kaehlerResidueTermKFam_apply AlgebraicCurve.Place.LocalResidueData.mk.injEq AlgebraicCurve.Place.LocalResidueData.mk.sizeOf_spec AlgebraicCurve.Place.kw_ffgc_adicCompletionComapIntegers_coe AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.sizeOf_spec AlgebraicCurve.Place.mem_simplePoleSubmodule AlgebraicCurve.Place.coe_uniformizerSubring ModularCurve.Lg37.Lg37CompletionSection.mk.injEq AlgebraicCurve.Place.CoefficientFieldSection.mk.injEq AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.injEq ModularCurve.Lg37.Lg37CompletionSection.mk.sizeOf_spec AlgebraicCurve.Place.CoefficientFieldSection.mk.sizeOf_spec AlgebraicCurve.Place.poleSubmodule_one AlgebraicCurve.Place.mem_poleSubmodule AlgebraicGeometry.Scheme.Modules.toUnitSection_ofUnitSection AlgebraicGeometry.Scheme.Modules.pullbackSection_def AlgebraicGeometry.Scheme.Modules.ofUnitSection_toUnitSection PresheafOfModules.InternalHom.IsSheafAux.appAt_toPresheafHom SheafOfModules.ihomSectionsEquivFamily_unit AlgebraicGeometry.Scheme.Modules.restrictHomEquivFamily_apply SheafOfModules.ihomEval_unit_app AlgebraicGeometry.Scheme.Modules.ihomEval_zero_right AlgebraicGeometry.Scheme.Modules.ihomEval_zero_left AlgebraicGeometry.Scheme.Modules.homOfFamily_app_apply SheafOfModules.unit_ihomSectionsEquivFamily"
p2m_attr_erase "simp" "AlgebraicGeometry.Scheme.Modules.familyOfHom_app AlgebraicGeometry.Scheme.Modules.restrictUnitIso_hom_app_apply AlgebraicGeometry.Scheme.Modules.restrictUnitIso_inv_app_apply AlgebraicGeometry.Scheme.Modules.restrictHomOfFamily_app_apply AlgebraicGeometry.Scheme.Modules.restrictHomEquivFamily_symm_apply AlgebraicGeometry.Scheme.Modules.tensorSections_zero_right AlgebraicGeometry.Scheme.Modules.map_unitSection AlgebraicGeometry.Scheme.Modules.tensorSectionsBilin_apply AlgebraicGeometry.Scheme.Modules.tensorPowSection_zero AlgebraicGeometry.Scheme.Modules.tensorSections_zero_left AlgebraicGeometry.Scheme.Modules.tensorPow_zero AlgebraicGeometry.Scheme.Modules.tensorPow_succ AlgebraicGeometry.Scheme.OrderedAffineCover.mk.injEq AlgebraicGeometry.OModulePresheaf.mk.sizeOf_spec AlgebraicGeometry.Scheme.OrderedAffineCover.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.mk.injEq AlgebraicGeometry.Scheme.Modules.pullbackLocalSection_neg AlgebraicGeometry.Scheme.Modules.pullbackLocalSection_zero AlgebraicGeometry.Scheme.Modules.pullbackLocalSection_sub AlgebraicGeometry.Scheme.Modules.pullbackLocalSection_add AlgebraicGeometry.Scheme.OrderedAffineCover.toCoverOf_U AlgebraicGeometry.Scheme.OrderedAffineCoverOf.mk.sizeOf_spec AlgebraicGeometry.Scheme.OrderedAffineCoverOf.mk.injEq AlgebraicGeometry.Scheme.OrderedAffineCover.restrict_U AlgebraicGeometry.OModulePresheaf.Hom.mk.injEq AlgebraicGeometry.OModulePresheaf.Hom.id_app AlgebraicGeometry.OModulePresheaf.AffHom.appSections_apply AlgebraicGeometry.OModulePresheaf.AffHom.comp_app AlgebraicGeometry.OModulePresheaf.AffSES.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.AffHom.kerMap_coe AlgebraicGeometry.OModulePresheaf.AffHom.id_app AlgebraicGeometry.OModulePresheaf.Hom.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.Hom.toAffHom_app AlgebraicGeometry.OModulePresheaf.SES.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.AffHom.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.Hom.comp_app AlgebraicGeometry.OModulePresheaf.SES.mk.injEq AlgebraicGeometry.OModulePresheaf.AffHom.mk.injEq AlgebraicGeometry.OModulePresheaf.Hom.appSections_apply AlgebraicGeometry.OModulePresheaf.AffSES.mk.injEq"
p2m_attr_erase "simp" "AlgebraicGeometry.OModulePresheaf.prod_obj AlgebraicGeometry.OModulePresheaf.restrOpen_obj AlgebraicGeometry.OModulePresheaf.DevissageStep.mk.injEq AlgebraicGeometry.OModulePresheaf.pushforward_obj AlgebraicGeometry.OModulePresheaf.im_obj AlgebraicGeometry.OModulePresheaf.pow_obj AlgebraicGeometry.OModulePresheaf.fstHom_app AlgebraicGeometry.OModulePresheaf.ker_obj AlgebraicGeometry.OModulePresheaf.coker_obj AlgebraicGeometry.OModulePresheaf.DevissageStep.mk.sizeOf_spec AlgebraicGeometry.Scheme.OrderedAffineCover.preimage_U AlgebraicGeometry.OModulePresheaf.sndHom_app AlgebraicGeometry.OModulePresheaf.Leray.restrictToPreimage_U DoubleComplex.Bounded.mk.injEq DoubleComplex.Bounded.mk.sizeOf_spec DoubleComplex.Convergence.mk.injEq DoubleComplex.Convergence.mk.sizeOf_spec DoubleComplex.SubQuot.mk.sizeOf_spec DoubleComplex.SubQuot.mk.injEq AlgebraicGeometry.ChowDatumProj.mk.sizeOf_spec AlgebraicGeometry.ChowDatum.mk.sizeOf_spec AlgebraicGeometry.ChowDatumProj.mk.injEq AlgebraicGeometry.ChowDatum.mk.injEq ProjSpaceCech.GradedModule.mk.injEq ProjSpaceCech.GradedModule.mk.sizeOf_spec ProjSpaceCech.GradedModule.Frac.mk.sizeOf_spec ProjSpaceCech.GradedModule.Presentation.mk.injEq ProjSpaceCech.GradedModule.Frac.mk.injEq ProjSpaceCech.GradedModule.Presentation.mk.sizeOf_spec ProjSpaceCech.GradedModule.Hom.shift_toLinearMap ProjSpaceCech.GradedModule.Hom.mk.sizeOf_spec ProjSpaceCech.GradedModule.Hom.mk.injEq TwoChartCech.Mumford.dK_apply TwoChartCech.Mumford.ι0_apply TwoChartCech.Mumford.ι1_apply TwoChartCech.KerCoprod.dK_apply TwoChartCech.KerCoprod.ι1_apply TwoChartCech.KerCoprod.ι0_apply AlgebraicGeometry.tilde.functorCompPullbackSpecIso_app AlgebraicGeometry.RelPicard.LFP.stageHom_val"
p2m_attr_erase "simp" "AlgebraicGeometry.RelPicard.BaseChange.relSubPicPresheafRestrictIso_hom_app_coe AlgebraicGeometry.RelPicard.BaseChange.relSubPicPresheafRestrictIso_inv_app_coe AlgebraicGeometry.RelPicard.BaseChange.restrict_P AlgebraicGeometry.RelEffCartierDiv.IsUniversal.lift_comp AlgebraicGeometry.RelEffCartierDiv.functor_map_fst AlgebraicGeometry.RelEffCartierDiv.IsUniversal.homEquiv_apply AlgebraicGeometry.RelEffCartierDiv.IsUniversal.lift_pullbackAlong AlgebraicGeometry.RelEffCartierDiv.IsUniversal.homEquiv_symm_apply AlgebraicGeometry.RelEffCartierDiv.IsUniversal.lift_comp_assoc AlgebraicGeometry.RelEffCartierDiv.supportedIn_top AlgebraicGeometry.RelEffCartierDiv.mem_supportedIn_iff AlgebraicGeometry.RelEffCartierDiv.supportedIn_top_eq AlgebraicGeometry.RelEffCartierDiv.restrictAlong_extendAlong AlgebraicGeometry.RelEffCartierDiv.extendAlong_I AlgebraicGeometry.RelEffCartierDiv.resProdMap_snd AlgebraicGeometry.RelEffCartierDiv.restrictAlong_I AlgebraicGeometry.RelEffCartierDiv.extendAlong_restrictAlong AlgebraicGeometry.RelEffCartierDiv.resProdMap_fst_assoc AlgebraicGeometry.RelEffCartierDiv.resProdMap_snd_assoc AlgebraicGeometry.RelEffCartierDiv.resProdMap_fst CoherentBaseChange.FibreH0Family.mk.sizeOf_spec CoherentBaseChange.FibreH0Family.mk.injEq AlgebraicGeometry.Scheme.Modules.ProjPresentation.mk.injEq AlgebraicGeometry.Scheme.Modules.ProjPresentation.mk.sizeOf_spec GoodReductionJacobian.RelativeGroupLaw.fibre_inv GoodReductionJacobian.RelativeGroupLaw.fibrePointToBase_coe GoodReductionJacobian.RelativeGroupLaw.fibrePointOfBase_toBase GoodReductionJacobian.RelativeGroupLaw.fibre_mul GoodReductionJacobian.RelativeGroupLaw.fibrePointToBase_ofBase GoodReductionJacobian.RelativeGroupLaw.fibre_one GoodReductionJacobian.RelativeGroupLaw.fibrePointOfBase_coe AlgebraicGeometry.schemeFibreEndo_snd AlgebraicGeometry.schemeFibreEndo_fst RegularLocalRingQuotientAscent.dualNumberFst_apply AlgebraicCurve.KwCfx.kw_cfx_tau_coe AlgebraicCurve.kw_hwcd_dlog_zero AlgebraicCurve.kw_hwcd_mem_regularDifferentials_iff AlgebraicCurve.kw_hwcd_dlog_one"

set_option autoImplicit false

noncomputable section

namespace P2mL1FF

section Frobenius

p2m_open "AlgebraicCurve~genus"

theorem char_data (k K F₀ F : Type*) [Field k] [Finite k] [Field K] [Field F₀] [Field F]
    [Algebra k F₀] [Algebra K F] [Algebra F₀ F] :
    ∃ p r : ℕ, p.Prime ∧ CharP k p ∧ Nat.card k = p ^ r ∧ 0 < r ∧ CharP F p ∧ CharP K p := by
  letI := Fintype.ofFinite k
  obtain ⟨n, hp, hcard⟩ := FiniteField.card k (ringChar k)
  haveI : CharP F₀ (ringChar k) := charP_of_injective_algebraMap (algebraMap k F₀).injective _
  haveI hF : CharP F (ringChar k) := charP_of_injective_algebraMap (algebraMap F₀ F).injective _
  haveI : CharP K (ringChar k) := ((algebraMap K F).charP_iff_charP (ringChar k)).mpr hF
  exact ⟨ringChar k, n, hp, inferInstance, by rw [Nat.card_eq_fintype_card, hcard], n.pos, hF,
    inferInstance⟩

set_option linter.unusedSectionVars false

variable {k K F₀ F : Type*} [Field k] [Finite k] [Field K] [IsAlgClosed K] [Field F₀] [Field F]
  [Algebra k F₀] [Algebra K F] [Algebra F₀ F]

variable (hgen : IntermediateField.adjoin K (Set.range (algebraMap F₀ F)) = ⊤)
  (φ : F →ₐ[K] F) (hφi : φ.toRingHom.IsIntegral)
  (hφ : ∀ x : F₀, φ (algebraMap F₀ F x) = algebraMap F₀ F (x ^ Nat.card k))

theorem card_ne_zero {p r : ℕ} [Fact p.Prime] (hq : Nat.card k = p ^ r) : Nat.card k ≠ 0 := by
  rw [hq]; exact pow_ne_zero _ (Fact.out : p.Prime).ne_zero

theorem add_pow_card {p r : ℕ} [Fact p.Prime] [CharP F p] (hq : Nat.card k = p ^ r) (x y : F) :
    (x + y) ^ Nat.card k = x ^ Nat.card k + y ^ Nat.card k := by
  rw [hq]; exact add_pow_char_pow x y p r

theorem pow_card_injective {p r : ℕ} [Fact p.Prime] [CharP F p] (hq : Nat.card k = p ^ r) :
    Function.Injective fun x : F => x ^ Nat.card k := by
  intro x y hxy
  have : (x - y) ^ Nat.card k = 0 := by
    simp only at hxy
    rw [hq, sub_pow_char_pow, ← hq, hxy, sub_self]
  exact sub_eq_zero.mp (pow_eq_zero_iff (card_ne_zero (k := k) hq) |>.mp this)

include hgen hφ in

theorem isFrobeniusEndo : IsFrobeniusEndo (Nat.card k) φ := by
  obtain ⟨p, r, hp, _, hq, hr, hFp, hKp⟩ := char_data k K F₀ F
  haveI := Fact.mk hp
  haveI := hFp
  haveI := hKp
  have hq0 : 0 < Nat.card k := by rw [hq]; exact pow_pos hp.pos r
  have hφ' : ∀ x : F₀, φ (algebraMap F₀ F x) = (algebraMap F₀ F x) ^ Nat.card k := by
    intro x; rw [hφ, map_pow]
  have hmem : ∀ y : F, y ∈ IntermediateField.adjoin K (Set.range (algebraMap F₀ F)) := by
    intro y; rw [hgen]; exact IntermediateField.mem_top
  constructor
  ·
    intro x
    refine IntermediateField.adjoin_induction (F := K)
      (p := fun x _ => ∃ y : F, φ y = x ^ Nat.card k) ?_ ?_ ?_ ?_ ?_ (hmem x)
    · rintro _ ⟨x₀, rfl⟩
      exact ⟨algebraMap F₀ F x₀, hφ' x₀⟩
    · intro c
      exact ⟨algebraMap K F (c ^ Nat.card k), by rw [AlgHom.commutes, map_pow]⟩
    · rintro x y - - ⟨a, ha⟩ ⟨b, hb⟩
      exact ⟨a + b, by rw [map_add, ha, hb, add_pow_card (k := k) hq]⟩
    · rintro x - ⟨a, ha⟩
      exact ⟨a⁻¹, by rw [map_inv₀, ha, inv_pow]⟩
    · rintro x y - - ⟨a, ha⟩ ⟨b, hb⟩
      exact ⟨a * b, by rw [map_mul, ha, hb, mul_pow]⟩
  ·
    intro y
    refine IntermediateField.adjoin_induction (F := K)
      (p := fun y _ => ∃ x : F, φ y = x ^ Nat.card k) ?_ ?_ ?_ ?_ ?_ (hmem y)
    · rintro _ ⟨x₀, rfl⟩
      exact ⟨algebraMap F₀ F x₀, hφ' x₀⟩
    · intro c
      obtain ⟨z, hz⟩ := IsAlgClosed.exists_pow_nat_eq c hq0
      exact ⟨algebraMap K F z, by rw [AlgHom.commutes, ← map_pow, hz]⟩
    · rintro x y - - ⟨a, ha⟩ ⟨b, hb⟩
      exact ⟨a + b, by rw [map_add, ha, hb, add_pow_card (k := k) hq]⟩
    · rintro x - ⟨a, ha⟩
      exact ⟨a⁻¹, by rw [map_inv₀, ha, inv_pow]⟩
    · rintro x y - - ⟨a, ha⟩ ⟨b, hb⟩
      exact ⟨a * b, by rw [map_mul, ha, hb, mul_pow]⟩

def rootTwist (h : IsFrobeniusEndo (Nat.card k) φ) {p r : ℕ} [Fact p.Prime] [CharP F p]
    (hq : Nat.card k = p ^ r) : F →+* F where
  toFun y := (h.mem_range_pow y).choose
  map_one' := by
    apply pow_card_injective (k := k) hq
    simp only
    rw [← (h.mem_range_pow 1).choose_spec, map_one, one_pow]
  map_mul' a b := by
    apply pow_card_injective (k := k) hq
    simp only
    rw [← (h.mem_range_pow (a * b)).choose_spec, map_mul, mul_pow,
      ← (h.mem_range_pow a).choose_spec, ← (h.mem_range_pow b).choose_spec]
  map_zero' := by
    apply pow_card_injective (k := k) hq
    simp only
    rw [← (h.mem_range_pow 0).choose_spec, map_zero, zero_pow (card_ne_zero (k := k) hq)]
  map_add' a b := by
    apply pow_card_injective (k := k) hq
    simp only
    rw [← (h.mem_range_pow (a + b)).choose_spec, map_add, add_pow_card (k := k) hq,
      ← (h.mem_range_pow a).choose_spec, ← (h.mem_range_pow b).choose_spec]

theorem rootTwist_pow (h : IsFrobeniusEndo (Nat.card k) φ) {p r : ℕ} [Fact p.Prime] [CharP F p]
    (hq : Nat.card k = p ^ r) (y : F) : (rootTwist φ h hq y) ^ Nat.card k = φ y :=
  (h.mem_range_pow y).choose_spec.symm

theorem rootTwist_bijective (h : IsFrobeniusEndo (Nat.card k) φ) {p r : ℕ} [Fact p.Prime]
    [CharP F p] (hq : Nat.card k = p ^ r) : Function.Bijective (rootTwist φ h hq) := by
  constructor
  · exact (rootTwist φ h hq).injective
  · intro z
    obtain ⟨y, hy⟩ := h.pow_mem_range z
    refine ⟨y, pow_card_injective (k := k) hq ?_⟩
    simp only
    rw [rootTwist_pow, hy]

def rootTwistEquiv (h : IsFrobeniusEndo (Nat.card k) φ) {p r : ℕ} [Fact p.Prime] [CharP F p]
    (hq : Nat.card k = p ^ r) : F ≃+* F :=
  RingEquiv.ofBijective (rootTwist φ h hq) (rootTwist_bijective φ h hq)

theorem rootTwistEquiv_apply (h : IsFrobeniusEndo (Nat.card k) φ) {p r : ℕ} [Fact p.Prime]
    [CharP F p] (hq : Nat.card k = p ^ r) (y : F) : rootTwistEquiv φ h hq y = rootTwist φ h hq y :=
  rfl

def basePow {p r : ℕ} [Fact p.Prime] [CharP K p] (_hq : Nat.card k = p ^ r) : K ≃+* K :=
  haveI : ExpChar K p := ExpChar.prime Fact.out
  RingEquiv.ofBijective (iterateFrobenius K p r) ⟨(iterateFrobenius K p r).injective, fun x => by
    obtain ⟨z, hz⟩ := IsAlgClosed.exists_pow_nat_eq x (pow_pos (Fact.out : p.Prime).pos r)
    exact ⟨z, by rw [iterateFrobenius_def, hz]⟩⟩

theorem basePow_apply {p r : ℕ} [Fact p.Prime] [CharP K p] (hq : Nat.card k = p ^ r) (x : K) :
    basePow (k := k) (K := K) hq x = x ^ Nat.card k := by
  haveI : ExpChar K p := ExpChar.prime Fact.out
  rw [hq]
  exact iterateFrobenius_def p r x

def twistSL (h : IsFrobeniusEndo (Nat.card k) φ) {p r : ℕ} [Fact p.Prime] [CharP F p] [CharP K p]
    (hq : Nat.card k = p ^ r) : SemilinearAut K F :=
  ⟨(rootTwistEquiv φ h hq, (basePow (k := k) (K := K) hq).symm), fun a => by
    change rootTwistEquiv φ h hq (algebraMap K F a) = algebraMap K F ((basePow (k := k) hq).symm a)
    apply pow_card_injective (k := k) hq
    simp only
    rw [rootTwistEquiv_apply, rootTwist_pow, AlgHom.commutes, ← map_pow, ← basePow_apply (K := K) hq,
      RingEquiv.apply_symm_apply]⟩

theorem twistSL_smul (h : IsFrobeniusEndo (Nat.card k) φ) {p r : ℕ} [Fact p.Prime] [CharP F p]
    [CharP K p] (hq : Nat.card k = p ^ r) (x : F) : twistSL φ h hq • x = rootTwist φ h hq x := rfl

theorem twistSL_inv_smul (h : IsFrobeniusEndo (Nat.card k) φ) {p r : ℕ} [Fact p.Prime] [CharP F p]
    [CharP K p] (hq : Nat.card k = p ^ r) (x : F) :
    (twistSL φ h hq)⁻¹ • x = (rootTwistEquiv φ h hq).symm x := rfl

theorem restrictAlong_twist_smul (h : IsFrobeniusEndo (Nat.card k) φ) {p r : ℕ} [Fact p.Prime]
    [CharP F p] [CharP K p] (hq : Nat.card k = p ^ r) (v : Place K F) :
    (twistSL φ h hq • v).restrictAlong φ hφi = v := by
  apply Place.ext
  ext x
  change φ x ∈ (twistSL φ h hq • v).toValuationSubring ↔ x ∈ v.toValuationSubring
  rw [SemilinearAut.smul_toValuationSubring, ValuationSubring.mem_pointwise_smul_iff_inv_smul_mem,
    ← rootTwist_pow φ h hq x, ← twistSL_smul φ h hq x, smul_pow', inv_smul_smul]
  exact v.toValuationSubring.pow_mem_iff (card_ne_zero (k := k) hq) x

include hgen hφ in
theorem restrictAlong_surjective : Function.Surjective (Place.restrictAlong φ hφi) := by
  obtain ⟨p, r, hp, _, hq, hr, hFp, hKp⟩ := char_data k K F₀ F
  haveI := Fact.mk hp
  haveI := hFp
  haveI := hKp
  intro v
  exact ⟨twistSL φ (isFrobeniusEndo hgen φ hφ) hq • v,
    restrictAlong_twist_smul φ hφi (isFrobeniusEndo hgen φ hφ) hq v⟩

theorem inertiaDegAlong_eq_one [IsCurveOver K F] (w : Place K F) : w.inertiaDegAlong φ hφi = 1 := by
  letI := algebraAlong φ
  haveI := isScalarTower_along φ
  haveI := isIntegral_along φ hφi
  have h := w.deg_restrict_mul_inertiaDeg (F := F)
  rw [IsCurveOver.deg_eq_one_of_isAlgClosed, IsCurveOver.deg_eq_one_of_isAlgClosed, one_mul] at h
  exact h

variable [IsCurveOver K F]

include hgen hφ in

theorem isPrincipal_pushforwardAlong {D : Divisor K F} (hD : D.IsPrincipal) :
    (Divisor.pushforwardAlong φ hφi D).IsPrincipal := by
  classical
  have hFr := isFrobeniusEndo hgen φ hφ
  have hq0 : Nat.card k ≠ 0 := Nat.card_pos.ne'
  obtain ⟨f, hf, hDf⟩ := hD
  refine ⟨hFr.frobNorm f, hFr.frobNorm_ne_zero hf, fun v => ?_⟩
  obtain ⟨w₀, hw₀⟩ := restrictAlong_surjective hgen φ hφi hφ v
  letI := algebraAlong φ
  haveI := isScalarTower_along φ
  haveI := isIntegral_along φ hφi
  change Divisor.pushforward F D v = _
  rw [Divisor.pushforward_apply]
  have hw₀' : Place.restrict F w₀ = v := hw₀
  have hf1 : (Place.inertiaDeg F w₀ : ℤ) = 1 := by
    exact_mod_cast (show Place.inertiaDeg F w₀ = 1 from inertiaDegAlong_eq_one φ hφi w₀)
  have hcollapse : (∑ w ∈ D.support,
      if Place.restrict F w = v then D w * (Place.inertiaDeg F w : ℤ) else 0)
        = D w₀ * (Place.inertiaDeg F w₀ : ℤ) := by
    refine (Finset.sum_eq_single w₀ ?_ ?_).trans (if_pos hw₀')
    · intro w _ hwne
      rw [if_neg]
      intro hwv
      exact hwne (hFr.restrictAlong_injective hq0 hφi
        ((show Place.restrictAlong φ hφi w = v from hwv).trans hw₀.symm))
    · intro hw₀mem
      rw [Finsupp.notMem_support_iff.mp hw₀mem, zero_mul, ite_self]
  rw [hcollapse, hDf w₀, hf1, mul_one, ← hw₀]
  exact (hFr.ord_restrictAlong_frobNorm hq0 hφi w₀ f).symm

def frDegZero : Divisor.degZero (K := K) (F := F) →+ Divisor.degZero (K := K) (F := F) :=
  ((Divisor.pushforwardAlong φ hφi).domRestrict (Divisor.degZero (K := K) (F := F))).codRestrict _
    (fun D => Divisor.pushforwardAlong_mem_degZero φ hφi D.2)

@[scoped simp]
theorem coe_frDegZero (D : Divisor.degZero (K := K) (F := F)) :
    (frDegZero (K := K) φ hφi D : Divisor K F) = Divisor.pushforwardAlong φ hφi (D : Divisor K F) := rfl

def frPic0 : Pic0 K F →+ Pic0 K F :=
  QuotientAddGroup.map _ _ (frDegZero (K := K) φ hφi) (by
    rintro ⟨D, hD0⟩ hD
    simp only [AddSubgroup.mem_addSubgroupOf] at hD ⊢
    exact isPrincipal_pushforwardAlong hgen φ hφi hφ hD)

theorem frPic0_mk (D : Divisor.degZero (K := K) (F := F)) :
    frPic0 hgen φ hφi hφ (Pic0.mk D) = Pic0.mk (frDegZero (K := K) φ hφi D) := rfl

end Frobenius

section Main

p2m_open "AlgebraicCurve~genus Polynomial"

set_option linter.unusedSectionVars false

variable {k K F₀ F : Type*} [Field k] [Finite k] [Field K] [IsAlgClosed K] [Field F₀] [Field F]
  [Algebra k F₀] [Algebra K F] [Algebra F₀ F]
  [IsCurveOver k F₀] [IsCurveOver K F]
  (hfg : ∃ s : Finset F₀, IntermediateField.adjoin k (s : Set F₀) = ⊤)
  (hgen : IntermediateField.adjoin K (Set.range (algebraMap F₀ F)) = ⊤)
  (φ : F →ₐ[K] F) (hφi : φ.toRingHom.IsIntegral)
  (hφ : ∀ x : F₀, φ (algebraMap F₀ F x) = algebraMap F₀ F (x ^ Nat.card k))

include hfg hgen in

theorem essFiniteType : Algebra.EssFiniteType K F := by
  classical
  obtain ⟨p, r, hp, _, hq, hr, hFp, hKp⟩ := char_data k K F₀ F
  obtain ⟨s, hs⟩ := hfg
  rw [← IntermediateField.fg_top_iff]
  refine ⟨s.image (algebraMap F₀ F), ?_⟩
  rw [Finset.coe_image]
  apply top_le_iff.mp
  rw [← hgen]
  apply IntermediateField.adjoin_le_iff.mpr
  rintro _ ⟨x, rfl⟩
  have hx : x ∈ IntermediateField.adjoin k (s : Set F₀) := by rw [hs]; exact IntermediateField.mem_top
  refine IntermediateField.adjoin_induction (F := k)
    (p := fun x _ => algebraMap F₀ F x ∈ IntermediateField.adjoin K (algebraMap F₀ F '' (s : Set F₀)))
    ?_ ?_ ?_ ?_ ?_ hx
  · intro x hx
    exact IntermediateField.subset_adjoin _ _ ⟨x, hx, rfl⟩
  · intro c

    letI := Fintype.ofFinite k
    set y := algebraMap F₀ F (algebraMap k F₀ c)
    have hy : y ^ Nat.card k = y := by
      simp only [y, ← map_pow, Nat.card_eq_fintype_card, FiniteField.pow_card]
    have hq1 : 1 < Nat.card k := by rw [hq]; exact Nat.one_lt_pow hr.ne' hp.one_lt
    have hint : IsIntegral K y := by
      refine ⟨X ^ Nat.card k - X, (Polynomial.monic_X_pow _).sub_of_left (by
        rw [degree_X_pow, degree_X]; exact_mod_cast hq1), ?_⟩
      rw [eval₂_sub, eval₂_X_pow, eval₂_X, hy, sub_self]
    have hdeg := IsAlgClosed.degree_eq_one_of_irreducible K (minpoly.irreducible hint)
    obtain ⟨c', hc'⟩ := minpoly.mem_range_of_degree_eq_one K y hdeg
    rw [← hc']
    exact IntermediateField.algebraMap_mem _ c'
  · intro x y _ _ hx hy
    rw [map_add]; exact add_mem hx hy
  · intro x _ hx
    rw [map_inv₀]; exact inv_mem hx
  · intro x y _ _ hx hy
    rw [map_mul]; exact mul_mem hx hy

def iterHom {A : Type*} [AddCommGroup A] (T : A →+ A) : ℕ → (A →+ A)
  | 0 => AddMonoidHom.id A
  | n + 1 => (iterHom T n).comp T

theorem coe_iterHom {A : Type*} [AddCommGroup A] (T : A →+ A) (n : ℕ) :
    ⇑(iterHom T n) = (⇑T)^[n] := by
  induction n with
  | zero => rfl
  | succ n ih =>
    ext x
    show iterHom T n (T x) = T^[n + 1] x
    rw [ih, Function.iterate_succ_apply]

include hfg hgen hφ in
theorem main (halg : ∀ a : K, ∃ n : ℕ, 0 < n ∧ a ^ Nat.card k ^ n = a)
    (ℓ : ℕ) [hℓ : Fact ℓ.Prime] (hℓK : (ℓ : K) ≠ 0) :
    AbelJacobiCard K F ℓ (genusFF K F) := by
  classical
  obtain ⟨p, r, hp, _, hq, hr, hFp, hKp⟩ := char_data k K F₀ F
  haveI := hKp
  haveI := hFp
  haveI := Fact.mk hp
  have hFr := isFrobeniusEndo hgen φ hφ
  have hφi : φ.toRingHom.IsIntegral := hFr.isIntegral (card_ne_zero (k := k) hq)
  have hℓp : ℓ ≠ p := by
    intro h; apply hℓK; rw [h]; exact CharP.cast_eq_zero K p
  set g := genusFF K F with hgdef

  have hC : ConstantsAreBase k F₀ :=
    AlgebraicCurve.constantsAreBase_of_apply_algebraMap_eq_pow_card k K F₀ F hfg hgen φ hφ

  set T : Pic0 K F →+ Pic0 K F := frPic0 hgen φ hφi hφ with hTdef
  have hT : ∀ D : Divisor.degZero (K := K) (F := F),
      T (Pic0.mk D) = Pic0.mk ⟨Divisor.pushforwardAlong φ hφi D,
        Divisor.pushforwardAlong_mem_degZero φ hφi D.2⟩ := fun D => rfl
  set G : AddSubgroup (Pic0 K F) := AddCommGroup.primaryComponent (Pic0 K F) ℓ with hGdef

  obtain ⟨P, hPmonic, hPdeg, hP0, -, hfixT⟩ :=
    Pic0.exists_monic_natCard_fixedPoints_iterate_eq_resultant_of_pushforwardAlong_frobenius
      k K F₀ F hfg hC hgen halg φ hφi hφ T hT

  have hres : ∀ n : ℕ, 0 < n → (X ^ n - 1 : ℤ[X]).resultant P ≠ 0 := by
    intro n hn
    obtain ⟨hfin, -, hreseq, -⟩ := hfixT n hn
    rw [hreseq]
    haveI : Finite (Function.fixedPoints (⇑T)^[n]) := hfin.to_subtype
    haveI : Nonempty (Function.fixedPoints (⇑T)^[n]) :=
      ⟨⟨0, Function.IsFixedPt.iterate (map_zero T) n⟩⟩
    exact_mod_cast (Nat.card_pos (α := Function.fixedPoints (⇑T)^[n])).ne'

  have hℓP0 : ¬ ((ℓ : ℤ) ∣ P.coeff 0) := by
    rw [hP0, hq]
    intro h
    push_cast at h
    rw [← pow_mul] at h
    have h'' : ℓ ∣ p ^ (r * genusFF K F) := by exact_mod_cast h
    exact hℓp ((Nat.prime_dvd_prime_iff_eq hℓ.out hp).mp (hℓ.out.dvd_of_dvd_pow h''))

  have hcount : ∀ n : ℕ, 0 < n →
      Finite {x : Pic0 K F // x ∈ G ∧ (⇑T)^[n] x = x} ∧
      Nat.card {x : Pic0 K F // x ∈ G ∧ (⇑T)^[n] x = x} =
        ℓ ^ (((X ^ n - 1 : ℤ[X]).resultant P).natAbs.factorization ℓ) := by
    intro n hn
    obtain ⟨-, -, -, hprim⟩ := hfixT n hn
    have hcard := hprim ℓ
    set Φ := (Polynomial.aeval (R := ℤ) T.toIntLinearMap (X ^ n - 1 : ℤ[X])) with hΦdef
    have hΦ : ∀ x : Pic0 K F, Φ x = (⇑T)^[n] x - x := by
      intro x
      rw [hΦdef, map_sub, map_pow, aeval_X, map_one, LinearMap.sub_apply, Module.End.one_apply,
        Module.End.pow_apply, AddMonoidHom.coe_toIntLinearMap]
    have hmemker : ∀ x : Pic0 K F, x ∈ Φ.toAddMonoidHom.ker ↔ (⇑T)^[n] x = x := by
      intro x
      rw [AddMonoidHom.mem_ker, LinearMap.toAddMonoidHom_coe, hΦ, sub_eq_zero]
    have e : {x : Pic0 K F // x ∈ G ∧ (⇑T)^[n] x = x} ≃
        AddCommGroup.primaryComponent Φ.toAddMonoidHom.ker ℓ :=
      { toFun := fun x => ⟨⟨x.1, (hmemker x.1).mpr x.2.2⟩, by
          obtain ⟨j, hj⟩ := (AddCommGroup.mem_primaryComponent).mp x.2.1
          exact (AddCommGroup.mem_primaryComponent).mpr ⟨j, Subtype.ext (by simpa using hj)⟩⟩
        invFun := fun y => ⟨(y.1 : Pic0 K F), by
          obtain ⟨j, hj⟩ := (AddCommGroup.mem_primaryComponent).mp y.2
          exact (AddCommGroup.mem_primaryComponent).mpr ⟨j, by
            have := congrArg Subtype.val hj; simpa using this⟩, (hmemker _).mp y.1.2⟩
        left_inv := fun x => rfl
        right_inv := fun y => rfl }
    have hcard' : Nat.card {x : Pic0 K F // x ∈ G ∧ (⇑T)^[n] x = x} =
        ℓ ^ (((X ^ n - 1 : ℤ[X]).resultant P).natAbs.factorization ℓ) := by
      rw [Nat.card_congr e, hcard]
    exact ⟨Nat.finite_of_card_ne_zero (by rw [hcard']; exact pow_ne_zero _ hℓ.out.ne_zero), hcard'⟩

  obtain ⟨m₀, hm₀, c, hc⟩ :=
    Polynomial.exists_factorization_resultant_X_pow_sub_one_eq_mul_add_of_not_dvd P hPmonic ℓ hℓP0 hres
  have hcnt : ∀ j e : ℕ, 0 < j → ¬ ℓ ∣ j →
      Finite {x : Pic0 K F // x ∈ G ∧ (⇑T)^[m₀ * j * ℓ ^ e] x = x} ∧
      Nat.card {x : Pic0 K F // x ∈ G ∧ (⇑T)^[m₀ * j * ℓ ^ e] x = x} = ℓ ^ (2 * g * e + c) := by
    intro j e hj hjℓ
    obtain ⟨hfin, hcard⟩ := hcount (m₀ * j * ℓ ^ e) (Nat.mul_pos (Nat.mul_pos hm₀ hj) (pow_pos hℓ.out.pos e))
    rw [hc j hj hjℓ e, hPdeg] at hcard
    exact ⟨hfin, hcard⟩

  set τ : Pic0 K F →+ Pic0 K F := iterHom T m₀ with hτdef
  have hτcoe : ⇑τ = (⇑T)^[m₀] := coe_iterHom T m₀
  have hτpow : ∀ (e : ℕ) (x : Pic0 K F), (⇑τ)^[ℓ ^ e] x = (⇑T)^[m₀ * 1 * ℓ ^ e] x := by
    intro e x
    rw [hτcoe, mul_one, Function.iterate_mul]
  have eτ : ∀ e : ℕ, {x : Pic0 K F // x ∈ G ∧ (⇑τ)^[ℓ ^ e] x = x} ≃
      {x : Pic0 K F // x ∈ G ∧ (⇑T)^[m₀ * 1 * ℓ ^ e] x = x} := fun e =>
    Equiv.subtypeEquivRight (fun x => by rw [hτpow])
  have hℓ1 : ¬ ℓ ∣ 1 := fun h => hℓ.out.one_lt.ne' (Nat.dvd_one.mp h)

  obtain ⟨-, -, horb⟩ :=
    Pic0.exists_iterate_apply_eq_self_of_pushforwardAlong_frobenius_of_isAlgebraic
      k K F₀ F hfg hgen halg φ hφi hφ T hT
  have hexh : ∀ x ∈ G, ∃ e : ℕ, (⇑τ)^[ℓ ^ e] x = x := by
    intro x hx
    obtain ⟨N, hN, hNx⟩ := horb x
    obtain ⟨e, j, hjℓ, hNej⟩ := Nat.exists_eq_pow_mul_and_not_dvd hN.ne' ℓ hℓ.out.one_lt.ne'
    have hj : 0 < j := Nat.pos_of_ne_zero (by rintro rfl; rw [mul_zero] at hNej; omega)

    have hxbig : (⇑T)^[m₀ * j * ℓ ^ e] x = x := by
      rw [show m₀ * j * ℓ ^ e = N * m₀ by rw [hNej]; ring, Function.iterate_mul]
      exact Function.iterate_fixed hNx m₀

    obtain ⟨hfinS, hcardS⟩ := hcnt 1 e one_pos hℓ1
    obtain ⟨hfinB, hcardB⟩ := hcnt j e hj hjℓ
    haveI := hfinB
    haveI := hfinS
    set ι : {x : Pic0 K F // x ∈ G ∧ (⇑T)^[m₀ * 1 * ℓ ^ e] x = x} →
        {x : Pic0 K F // x ∈ G ∧ (⇑T)^[m₀ * j * ℓ ^ e] x = x} := fun y => ⟨y.1, y.2.1, by
          rw [show m₀ * j * ℓ ^ e = m₀ * 1 * ℓ ^ e * j by ring, Function.iterate_mul]
          exact Function.iterate_fixed y.2.2 j⟩ with hιdef
    have hιinj : Function.Injective ι := by
      intro a b hab
      have := congrArg Subtype.val hab
      exact Subtype.ext this
    have hιbij : Function.Bijective ι :=
      hιinj.bijective_of_nat_card_le (by rw [hcardS, hcardB])
    obtain ⟨y, hy⟩ := hιbij.2 ⟨x, hx, hxbig⟩
    have hyx : (y : Pic0 K F) = x := congrArg Subtype.val hy
    refine ⟨e, ?_⟩
    rw [hτpow, ← hyx]
    exact y.2.2

  have hfix' : ∃ c' : ℕ, ∀ e : ℕ,
      Finite {x : Pic0 K F // x ∈ G ∧ (⇑τ)^[ℓ ^ e] x = x} ∧
      Nat.card {x : Pic0 K F // x ∈ G ∧ (⇑τ)^[ℓ ^ e] x = x} ≤ ℓ ^ (2 * g * e + c') := by
    refine ⟨c, fun e => ?_⟩
    obtain ⟨hfinS, hcardS⟩ := hcnt 1 e one_pos hℓ1
    haveI := hfinS
    exact ⟨Finite.of_equiv _ (eτ e).symm, by rw [Nat.card_congr (eτ e), hcardS]⟩

  haveI : Algebra.EssFiniteType K F := essFiniteType hfg hgen
  obtain ⟨t, ht, htfin, -⟩ := IsCurveOver.exists_separating_transcendental (K := K) (F := F)
  have hdiv : ∀ x ∈ G, ∃ y : Pic0 K F, ℓ • y = x := fun x _ =>
    Pic0.exists_nsmul_eq_of_charP K F p ⟨t, ht, htfin⟩ ℓ hℓ.out.ne_zero x

  obtain ⟨hfin, hle⟩ :=
    AddCommGroup.finite_and_natCard_torsionBy_le_of_natCard_fixed_primaryComponent_le_of_divisible
      ℓ (2 * g) τ hexh hfix' hdiv

  haveI := hfin
  have hmemG1 : ∀ x : Pic0 K F, ℓ • x = 0 → x ∈ G := fun x hx =>
    (AddCommGroup.mem_primaryComponent).mpr ⟨1, by rw [pow_one]; exact hx⟩
  choose kx hkx using fun x : Submodule.torsionBy ℤ (Pic0 K F) (ℓ : ℤ) =>
    hexh x (hmemG1 x (by
      have := (Submodule.mem_torsionBy_iff _ _).mp x.2
      rwa [← natCast_zsmul]))
  obtain ⟨k₁, hk₁⟩ := (Set.finite_range kx).bddAbove
  have hθ : ∀ x : Pic0 K F, ℓ • x = 0 → (⇑τ)^[ℓ ^ k₁] x = x := by
    intro x hx
    have hxmem : x ∈ Submodule.torsionBy ℤ (Pic0 K F) (ℓ : ℤ) := by
      rw [Submodule.mem_torsionBy_iff, natCast_zsmul]; exact hx
    have h1 := hkx ⟨x, hxmem⟩
    have h2 : kx ⟨x, hxmem⟩ ≤ k₁ := hk₁ ⟨⟨x, hxmem⟩, rfl⟩
    obtain ⟨d, hd⟩ := Nat.exists_eq_add_of_le h2
    rw [hd, pow_add, Function.iterate_mul]
    exact Function.iterate_fixed h1 _
  set σ : Pic0 K F →+ Pic0 K F := iterHom T (m₀ * ℓ ^ k₁) with hσdef
  have hσ : ⇑σ = (⇑τ)^[ℓ ^ k₁] := by
    rw [hσdef, coe_iterHom, hτcoe, ← Function.iterate_mul]
  set τ' : Pic0 K F →+ Pic0 K F := iterHom T (m₀ * ℓ ^ (k₁ + 1)) with hτ'def
  have hτ'σ : ⇑τ' = (⇑σ)^[ℓ] := by
    rw [hτ'def, coe_iterHom, hσ, hτcoe, ← Function.iterate_mul, ← Function.iterate_mul, pow_succ]
  have hτ' : ∀ x : Pic0 K F, ℓ ^ 2 • x = 0 → τ' x = x := by
    intro x hx
    set e := σ x - x with hedef
    have hℓx : ℓ • (ℓ • x) = 0 := by rw [← mul_nsmul', ← pow_two, hx]
    have hσℓx : σ (ℓ • x) = ℓ • x := by rw [hσ]; exact hθ _ hℓx
    have hℓe : ℓ • e = 0 := by rw [hedef, nsmul_sub, ← map_nsmul, hσℓx, sub_self]
    have hσe : σ e = e := by rw [hσ]; exact hθ e hℓe
    have hxe : σ x = x + e := by rw [hedef]; abel
    have hiter : ∀ i : ℕ, (⇑σ)^[i] x = x + i • e := by
      intro i
      induction i with
      | zero => rw [Function.iterate_zero_apply, zero_nsmul, add_zero]
      | succ i ih2 =>
        rw [Function.iterate_succ_apply', ih2, map_add, map_nsmul, hσe, hxe, add_nsmul, one_nsmul]
        abel
    rw [hτ'σ, hiter ℓ, hℓe, add_zero]

  have hfinℓ : Finite (Submodule.torsionBy ℤ (Pic0 K F) (ℓ : ℤ)) := hfin
  have hτ'pow : ∀ (kk : ℕ) (x : Pic0 K F),
      (⇑τ')^[ℓ ^ (0 + kk)] x = (⇑T)^[m₀ * 1 * ℓ ^ (k₁ + 1 + kk)] x := by
    intro kk x
    rw [hτ'def, coe_iterHom, ← Function.iterate_mul, zero_add, mul_one, pow_add _ (k₁ + 1) kk,
      mul_assoc]
  have hfix : ∀ kk : ℕ,
      Nat.card {x : Pic0 K F // x ∈ AddCommGroup.primaryComponent (Pic0 K F) ℓ ∧
        (⇑τ')^[ℓ ^ (0 + kk)] x = x} = ℓ ^ (2 * g * kk + (2 * g * (k₁ + 1) + c)) := by
    intro kk
    obtain ⟨-, hcardS⟩ := hcnt 1 (k₁ + 1 + kk) one_pos hℓ1
    have e' : {x : Pic0 K F // x ∈ AddCommGroup.primaryComponent (Pic0 K F) ℓ ∧
        (⇑τ')^[ℓ ^ (0 + kk)] x = x} ≃
        {x : Pic0 K F // x ∈ G ∧ (⇑T)^[m₀ * 1 * ℓ ^ (k₁ + 1 + kk)] x = x} :=
      Equiv.subtypeEquivRight (fun x => by rw [hτ'pow])
    rw [Nat.card_congr e', hcardS]
    ring_nf
  have hA := AddCommGroup.natCard_torsionBy_pow_eq_pow_of_natCard_fixed_primaryComponent
    ℓ (2 * g) τ' hfinℓ hle hτ' ⟨2 * g * (k₁ + 1) + c, 0, hfix⟩

  intro n
  rw [← hA n]
  exact Nat.card_congr (Equiv.subtypeEquivRight (fun x => Iff.rfl))

end Main

end P2mL1FF
p2m_reactivate "P2MW.S_AlgebraicCurve_Pic0_abelJacobiCard_genusFF_of_frobenius_of_isAlgebraic.P2mL1FF"

end
p2m_reactivate "P2MW.S_AlgebraicCurve_Pic0_abelJacobiCard_genusFF_of_frobenius_of_isAlgebraic.P2mL1FF"

p2m_open "AlgebraicCurve~genus" in
theorem solution
    (k K F₀ F : Type*) [Field k] [Finite k] [Field K] [IsAlgClosed K] [Field F₀] [Field F]
    [Algebra k F₀] [Algebra K F] [Algebra F₀ F]
    [AlgebraicCurve.IsCurveOver k F₀] [AlgebraicCurve.IsCurveOver K F]
    (hfg : ∃ s : Finset F₀, IntermediateField.adjoin k (s : Set F₀) = ⊤)
    (hgen : IntermediateField.adjoin K (Set.range (algebraMap F₀ F)) = ⊤)
    (halg : ∀ a : K, ∃ n : ℕ, 0 < n ∧ a ^ Nat.card k ^ n = a)
    (φ : F →ₐ[K] F)
    (hφ : ∀ x : F₀, φ (algebraMap F₀ F x) = algebraMap F₀ F (x ^ Nat.card k))
    (ℓ : ℕ) [Fact ℓ.Prime] (hℓ : (ℓ : K) ≠ 0) :
    AlgebraicCurve.AbelJacobiCard K F ℓ (AlgebraicCurve.genusFF K F) :=
  P2mL1FF.main hfg hgen φ hφ halg ℓ hℓ

end S_AlgebraicCurve_Pic0_abelJacobiCard_genusFF_of_frobenius_of_isAlgebraic
end P2MW
export P2MW.S_AlgebraicCurve_Pic0_abelJacobiCard_genusFF_of_frobenius_of_isAlgebraic (solution)
