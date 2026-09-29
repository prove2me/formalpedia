-- Prove2me | solution 1 for AlgebraicGeometry.Scheme.TwoAffineOpenCover.finrank_H1_sectionsOf_unit_eq_genusFF_of_curveModel
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.122355+00:00
-- url     : https://prove2.me/submissions/79db56f6-1d50-50bc-885f-3de901b3c816

import Mathlib
import Definitions.Def_AlgebraicGeometry_NeronModelPropertyBundleCarrier
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import Definitions.Def_AlgebraicGeometry_RepresentsRelSubPic
import Definitions.Def_AlgebraicGeometry_RelPicardAlgEquivZeroCut
import Definitions.Def_AlgebraicGeometry_TwoAffineOpenCover
import Definitions.Def_AlgebraicGeometry_TwoChartCechSectionsOf
import Definitions.Def_SheafOfModules_Monoidal
import Definitions.Def_AlgebraicGeometry_IdealSheafModule
import Definitions.Def_AlgebraicGeometry_SmoothProperCurveBase
import Definitions.Def_AlgebraicGeometry_RelPicardChartSections
import Definitions.Def_AlgebraicGeometry_ModulesSectionZeroScheme
import Definitions.Def_AlgebraicCurve_CurveModel
import Definitions.Def_AlgebraicCurve_AdelicIndex
import Definitions.Def_AlgebraicCurve_Repartitions
import Theorems.Thm_AlgebraicGeometry_TwoGluedCurves_eulerChar_sectionsOf_eq_add_sub_natCard_of_isInvertible
import Theorems.Thm_AlgebraicGeometry_Scheme_TwoAffineOpenCover_exists_linearEquiv_sectionsOf_of_iso
import Theorems.Thm_AlgebraicGeometry_Scheme_TwoAffineOpenCover_finrank_H1_sectionsOf_unit_eq_and_finrank_H0_eq_one
import Theorems.Thm_AlgebraicGeometry_SmoothProperCurve_exists_curveModel_riemannRoch_of_isAlgClosed
import Theorems.Thm_AlgebraicCurve_CurveModel_eq_genusFF_of_forall_ell_sub_ell_eq
import Theorems.Thm_AlgebraicCurve_nonempty_algEquiv_functionField_of_iso
import Theorems.Thm_AlgebraicCurve_genusFF_eq_of_algEquiv
import Theorems.Thm_AlgebraicGeometry_Scheme_TwoAffineOpenCover_finrank_cechDiff_baseChange_of_isAlgClosed
import Theorems.Thm_AlgebraicGeometry_geometricallyIntegral_of_isAlgClosed
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_Scheme_TwoAffineOpenCover_finrank_H1_sectionsOf_unit_eq_genusFF_of_curveModel
p2m_attr_erase "instance" "AlgebraicGeometry.OModulePresheaf.isScalarTower AlgebraicGeometry.Scheme.OrderedAffineCover.instLinearOrder AlgebraicGeometry.OModulePresheaf.module AlgebraicGeometry.Scheme.OrderedAffineCover.instFintype AlgebraicGeometry.Scheme.OrderedAffineCover.instFintypeIdx AlgebraicGeometry.OModulePresheaf.addCommGroup AlgebraicGeometry.Scheme.OrderedAffineCover.instDecidableEqIdx AlgebraicGeometry.OModulePresheaf.moduleSections AlgebraicGeometry.OModulePresheaf.instSubsingletonObjZero AlgebraicGeometry.OModulePresheaf.Leray.relAltC_scalarTower AlgebraicGeometry.OModulePresheaf.Leray.ker_relAltd_modΓ AlgebraicGeometry.OModulePresheaf.Leray.relAltC_modΓ AlgebraicGeometry.OModulePresheaf.Leray.biC_abGrp AlgebraicGeometry.OModulePresheaf.Leray.relAltH_modΓ AlgebraicGeometry.OModulePresheaf.Leray.ker_relAltd_smul AlgebraicGeometry.OModulePresheaf.Leray.relAltH_scalarTower AlgebraicGeometry.OModulePresheaf.Leray.relAltH_smul AlgebraicGeometry.OModulePresheaf.Leray.biC_module AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instDecidableEqIdx AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instFintype AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instLinearOrder AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instFintypeIdx DoubleComplex.instModuleE₂I DoubleComplex.Bounded.modR DoubleComplex.instModuleE₂II DoubleComplex.instAddCommGroupE₂II DoubleComplex.Bounded.abGrp DoubleComplex.instAddCommGroupE₂I AlgebraicGeometry.ChowDatum.hι_closed AlgebraicGeometry.ChowDatumProj.hιN_closed AlgebraicGeometry.ChowDatumProj.hp_proper AlgebraicGeometry.ChowDatum.hp_isoU AlgebraicGeometry.ChowDatum.hp_proper AlgebraicGeometry.ProjSpace.algebraAway AlgebraicGeometry.ProjSpace.instIsProperProdOverπ AlgebraicGeometry.ChowDatumProj.hp_isoU AlgebraicGeometry.ProjSpace.isProper_π AlgebraicGeometry.ProjSpace.finiteType_mvPolynomial ProjSpaceCech.GradedModule.H.module ProjSpaceCech.GradedModule.H.addCommGroup"
p2m_attr_erase "instance" "ProjSpaceCech.GradedModule.sec.instAdd ProjSpaceCech.GradedModule.sec.instNeg ProjSpaceCech.GradedModule.acg ProjSpaceCech.GradedModule.Frac.setoid ProjSpaceCech.GradedModule.modR ProjSpaceCech.GradedModule.sec.instModule ProjSpaceCech.GradedModule.sec.instAddCommGroup ProjSpaceCech.GradedModule.sec.instZero ProjSpaceCech.GradedModule.Presentation.fJ ProjSpaceCech.GradedModule.sec.instSMul ProjSpaceCech.Twist.H.module ProjSpaceCech.Idx.instFintype ProjSpaceCech.Twist.H.addCommGroup ProjSpaceCech.Idx.instDecidableEq ProjSpaceCech.Twist.Mon.instDecidableEq ProjSpaceCech.Twist.cochain.instAddCommGroup ProjSpaceCech.Twist.cochain.instModule PresheafOfModules.PullbackMonoidal.pullback_monoidal PresheafOfModules.PullbackMonoidal.isIso_δ PresheafOfModules.pushforward_laxMonoidal PresheafOfModules.PullbackMonoidal.isIso_η PresheafOfModules.free_monoidal PresheafOfModules.restrictScalars_laxMonoidal PresheafOfModules.PullbackMonoidal.isIso_δ_gS PresheafOfModules.pullback_oplaxMonoidal PresheafOfModules.PullbackMonoidal.instPreservesColimitsOfSizeCompOppositeCommRingCatRingCatForget₂RingHomCarrierCarrierPb PresheafOfModules.pullback_monoidal' AlgebraicGeometry.Scheme.Modules.preservesBinaryProducts_opensMap AlgebraicGeometry.Scheme.Modules.pullback_monoidal AlgebraicGeometry.Scheme.Modules.sheafify_isLocalization' AlgebraicGeometry.Scheme.Modules.preservesTerminal_opensMap AlgebraicGeometry.Scheme.Modules.pullback₀_monoidal AlgebraicGeometry.Scheme.Modules.preservesFiniteProducts_opensMap AlgebraicGeometry.Scheme.Modules.instLiftingPresheafOfModulesSheafifyPresheafWOpensCarrierCarrierCommRingCatGrothendieckTopologyObjFunctorOppositeIsSheafSheafCompPullback₀Pullback SheafOfModules.isIso_ihomModelToIhom AlgebraicCurve.IsCurveOver.instNontrivialKaehler AlgebraicCurve.IsCurveOver.instFreeKaehler AlgebraicCurve.IsCurveOver.toHasPrincipalDivisors AlgebraicCurve.IsCurveOver.instFiniteResidue AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation"
p2m_attr_erase "instance" "AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.instFundamentalIdentityOfSumRamificationInertia AlgebraicCurve.Place.instIsScalarTowerResidueFieldRestrictPushforward AlgebraicCurve.Place.instAlgebraResidueFieldRestrictPushforward AlgebraicCurve.Place.instIsLocalHomRestrictInclusion AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.SemilinearAut.instDistribMulActionSubtypeProdRingAutMemSubgroupPic0 AlgebraicCurve.SemilinearAut.instDistribMulActionSubtypeProdRingAutMemSubgroupDivisor AlgebraicCurve.Pic0.instModuleZModTorsion AlgebraicCurve.SemilinearAut.instSMulSubtypeProdRingAutMemSubgroupPlace AlgebraicCurve.SemilinearAut.instDistribMulActionTorsion AlgebraicCurve.SemilinearAut.instSMulSubtypeProdRingAutMemSubgroupPic0 AlgebraicCurve.SemilinearAut.instSMulTorsion AlgebraicCurve.SemilinearAut.instMulActionSubtypeProdRingAutMemSubgroupPlace AlgebraicCurve.SemilinearAut.instSMulCommClassZModTorsion AlgebraicCurve.SemilinearAut.instMulSemiringActionSubtypeProdRingAutMemSubgroup instDecEqAlgebraicClosureRat WeierstrassCurve.Affine.Point.instDistribMulActionAlgEquiv WeierstrassCurve.Affine.Point.instModuleZModTorsionBy WeierstrassCurve.Affine.Point.instSMulTorsionBy WeierstrassCurve.Affine.Point.instDistribMulActionTorsionBy WeierstrassCurve.Affine.Point.instSMulAlgEquiv WeierstrassCurve.Affine.Point.instSMulCommClassAlgEquivZModTorsionBy AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions AlgebraicCurve.instHasLocalResidue_of_hasCanonicalLocalResidueK AlgebraicCurve.instHasCanonicalLocalResidueK_of_hasCanonicalLocalResidueKStar AlgebraicCurve.Place.kw_ffgc_finiteDimensional_adicCompletion instAlgebraSubtypeMemValuationSubring_definitions AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersIntegersCompletion ModularCurve.KwF4gRRTate.instAlgebraKAdicCompletionIntegers AlgebraicCurve.Place.kw_ffgc_continuousSMul_adicCompletionComap AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersCompletionCompletion IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions"
p2m_attr_erase "instance" "IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions AlgebraicCurve.instHasCanonicalLocalResidueK AlgebraicCurve.Place.instAlgebra_restrictResidueField AlgebraicCurve.Place.instIsScalarTower_restrictResidueField AlgebraicCurve.instHasLocalResidue AlgebraicCurve.HasSeparableResidue.of_perfectField_of_isCurveOver AlgebraicCurve.HasSeparableResidue.of_perfectField AlgebraicCurve.Place.instIsLocalHom_restrictSubringHom AlgebraicCurve.instHasCanonicalLocalResidueKStar ModularCurve.KwNo6Pin.isLocalRing_completion"
p2m_attr_erase "simp" "AlgebraicGeometry.Scheme.OrderedAffineCover.mk.injEq AlgebraicGeometry.OModulePresheaf.mk.sizeOf_spec AlgebraicGeometry.Scheme.OrderedAffineCover.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.mk.injEq AlgebraicGeometry.OModulePresheaf.prod_obj AlgebraicGeometry.OModulePresheaf.restrOpen_obj AlgebraicGeometry.OModulePresheaf.DevissageStep.mk.injEq AlgebraicGeometry.OModulePresheaf.pushforward_obj AlgebraicGeometry.OModulePresheaf.im_obj AlgebraicGeometry.OModulePresheaf.pow_obj AlgebraicGeometry.OModulePresheaf.fstHom_app AlgebraicGeometry.OModulePresheaf.ker_obj AlgebraicGeometry.OModulePresheaf.coker_obj AlgebraicGeometry.OModulePresheaf.DevissageStep.mk.sizeOf_spec AlgebraicGeometry.Scheme.OrderedAffineCover.preimage_U AlgebraicGeometry.OModulePresheaf.sndHom_app AlgebraicGeometry.OModulePresheaf.Hom.mk.injEq AlgebraicGeometry.OModulePresheaf.Hom.id_app AlgebraicGeometry.OModulePresheaf.AffHom.appSections_apply AlgebraicGeometry.OModulePresheaf.AffHom.comp_app AlgebraicGeometry.OModulePresheaf.AffSES.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.AffHom.kerMap_coe AlgebraicGeometry.OModulePresheaf.AffHom.id_app AlgebraicGeometry.OModulePresheaf.Hom.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.Hom.toAffHom_app AlgebraicGeometry.OModulePresheaf.SES.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.AffHom.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.Hom.comp_app AlgebraicGeometry.OModulePresheaf.SES.mk.injEq AlgebraicGeometry.OModulePresheaf.AffHom.mk.injEq AlgebraicGeometry.OModulePresheaf.Hom.appSections_apply AlgebraicGeometry.OModulePresheaf.AffSES.mk.injEq AlgebraicGeometry.OModulePresheaf.Leray.restrictToPreimage_U AlgebraicGeometry.Scheme.OrderedAffineCover.toCoverOf_U AlgebraicGeometry.Scheme.OrderedAffineCoverOf.mk.sizeOf_spec AlgebraicGeometry.Scheme.OrderedAffineCoverOf.mk.injEq AlgebraicGeometry.Scheme.OrderedAffineCover.restrict_U DoubleComplex.Bounded.mk.injEq DoubleComplex.Bounded.mk.sizeOf_spec DoubleComplex.Convergence.mk.injEq"
p2m_attr_erase "simp" "DoubleComplex.Convergence.mk.sizeOf_spec DoubleComplex.SubQuot.mk.sizeOf_spec DoubleComplex.SubQuot.mk.injEq AlgebraicGeometry.ChowDatumProj.mk.sizeOf_spec AlgebraicGeometry.ChowDatum.mk.sizeOf_spec AlgebraicGeometry.ChowDatumProj.mk.injEq AlgebraicGeometry.ChowDatum.mk.injEq ProjSpaceCech.GradedModule.mk.injEq ProjSpaceCech.GradedModule.mk.sizeOf_spec ProjSpaceCech.GradedModule.Frac.mk.sizeOf_spec ProjSpaceCech.GradedModule.Presentation.mk.injEq ProjSpaceCech.GradedModule.Frac.mk.injEq ProjSpaceCech.GradedModule.Presentation.mk.sizeOf_spec ProjSpaceCech.GradedModule.Hom.shift_toLinearMap ProjSpaceCech.GradedModule.Hom.mk.sizeOf_spec ProjSpaceCech.GradedModule.Hom.mk.injEq PresheafOfModules.freeεIso_hom_app PresheafOfModules.freeμIso_hom_app AlgebraicGeometry.Scheme.Modules.tensorPow_zero AlgebraicGeometry.Scheme.Modules.tensorPow_succ AlgebraicGeometry.Scheme.Modules.tensorSections_zero_right AlgebraicGeometry.Scheme.Modules.map_unitSection AlgebraicGeometry.Scheme.Modules.tensorSectionsBilin_apply AlgebraicGeometry.Scheme.Modules.tensorPowSection_zero AlgebraicGeometry.Scheme.Modules.tensorSections_zero_left AlgebraicGeometry.Scheme.Modules.pullbackLocalSection_neg AlgebraicGeometry.Scheme.Modules.pullbackLocalSection_zero AlgebraicGeometry.Scheme.Modules.pullbackLocalSection_sub AlgebraicGeometry.Scheme.Modules.pullbackLocalSection_add PresheafOfModules.InternalHom.IsSheafAux.appAt_toPresheafHom SheafOfModules.ihomSectionsEquivFamily_unit AlgebraicGeometry.Scheme.Modules.restrictHomEquivFamily_apply SheafOfModules.ihomEval_unit_app AlgebraicGeometry.Scheme.Modules.ihomEval_zero_right AlgebraicGeometry.Scheme.Modules.ihomEval_zero_left AlgebraicGeometry.Scheme.Modules.homOfFamily_app_apply SheafOfModules.unit_ihomSectionsEquivFamily AlgebraicGeometry.Scheme.Modules.familyOfHom_app AlgebraicGeometry.Scheme.Modules.restrictUnitIso_hom_app_apply AlgebraicGeometry.Scheme.Modules.restrictUnitIso_inv_app_apply"
p2m_attr_erase "simp" "AlgebraicGeometry.Scheme.Modules.restrictHomOfFamily_app_apply AlgebraicGeometry.Scheme.Modules.restrictHomEquivFamily_symm_apply AlgebraicCurve.coe_cechH0Equiv_apply AlgebraicCurve.cechH1ToH1_mk AlgebraicCurve.lSpaceOn_univ AlgebraicCurve.lSpaceOn_empty AlgebraicCurve.Place.congrEquiv_symm_apply AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply AlgebraicCurve.RationalFunctionField.deg_placeOfPoint AlgebraicCurve.Divisor.mapRestrict_single AlgebraicCurve.Divisor.pushforward_single AlgebraicCurve.Place.coe_restrictInclusion AlgebraicCurve.Place.mem_fiber AlgebraicCurve.Place.restrict_toValuationSubring AlgebraicCurve.Divisor.degree_pushforward AlgebraicCurve.Place.restrictResidueMap_residue AlgebraicCurve.Pic0.coe_pushforwardDegZeroHom AlgebraicCurve.Pic0.coe_pullbackDegZeroHom AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal AlgebraicCurve.IsFrobeniusEndo.frobNormRingHom_apply ModularCurve.frobeniusPushforwardGeomLevelPic0_mk ModularCurve.coe_frobeniusGeomLevelEquiv_apply ModularCurve.coe_frobeniusPushforwardGeomLevelDegZero ModularCurve.heckeFibreGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusGeomLevel_apply_coe ModularCurve.frobeniusPullbackGeomLevelPic0OfIsCurveOver_mk ModularCurve.coe_heckeFibreGeomLevelDegZero ModularCurve.coe_frobeniusPullbackGeomLevelDegZero ModularCurve.frobeniusPullbackGeomLevelPic0_mk ModularCurve.frobeniusPullbackGeomLevel_single ModularCurve.heckeFibreGeomLevelPic0_mk ModularCurve.frobeniusPushforwardGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusPushforwardGeomLevel_single"
p2m_attr_erase "simp" "ModularCurve.qExpandAlgC_apply AlgebraicCurve.Divisor.degree_pushforwardAlong AlgebraicCurve.Pic0.coe_degZeroCorrespondence AlgebraicCurve.Place.mem_fiberAlong AlgebraicCurve.SemilinearAut.toRingAut_inv AlgebraicCurve.SemilinearAut.smul_def AlgebraicCurve.SemilinearAut.smul_single AlgebraicCurve.SemilinearAut.smul_toValuationSubring AlgebraicCurve.SemilinearAut.baseAut_inv AlgebraicCurve.SemilinearAut.baseAut_ofAlgAut AlgebraicCurve.SemilinearAut.toRingAut_ofAlgAut AlgebraicCurve.SemilinearAut.torsionRep_apply AlgebraicCurve.SemilinearAut.toRingAut_one AlgebraicCurve.SemilinearAut.deg_smul AlgebraicCurve.SemilinearAut.degree_smul AlgebraicCurve.SemilinearAut.coe_degZeroSMulHom AlgebraicCurve.SemilinearAut.baseAut_mul AlgebraicCurve.SemilinearAut.coe_smulValuationSubringEquiv_apply AlgebraicCurve.SemilinearAut.baseAut_one AlgebraicCurve.SemilinearAut.ofAlgAut_smul AlgebraicCurve.SemilinearAut.coe_torsion_smul AlgebraicCurve.SemilinearAut.toRingAut_mul AlgebraicCurve.coe_frobeniusPushforwardDegZero AlgebraicCurve.IsFrobeniusEndo.coe_frobeniusPullbackDegZero ModularCurve.jqNModC_one ModularCurve.qExpand_coeff_mul ModularCurve.qExpandₐ_apply ModularCurve.jqN_one ModularCurve.qExpand_single ModularCurve.dedekindPsi_one ModularCurve.ModularPolynomialData.mk.sizeOf_spec ModularCurve.evalAtJ_X ModularCurve.ModularPolynomialData.mk.injEq ModularCurve.constantCoeff_jNum ModularCurve.constantCoeff_eisenstein4 ModularCurve.qExpand_C ModularCurve.coeff_jq_neg_one ModularCurve.constantCoeff_jNumQ ModularCurve.reduceModBivar_C_X ModularCurve.laurentMap_coeff"
p2m_attr_erase "simp" "ModularCurve.reduceModBivar_X ModularCurve.laurentMap_single ModularCurve.evalAtJInt_X ModularCurve.evalAtJMod_X ModularCurve.jqNMod_one ModularCurve.aeval_heckeGen ModularCurve.coe_mTorsionGaloisRep_apply ModularCurve.eisensteinSystem_of_dvd ModularCurve.eisensteinSystem_of_not_dvd FreyPackage.mk.sizeOf_spec FreyPackage.mk.injEq WeierstrassCurve.Affine.Point.galoisRepModuleEnd_apply AlgebraicCurve.RationalFunctionField.placeInfty_toValuationSubring AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none AlgebraicCurve.Divisor.evalFun_zero AlgebraicCurve.Place.evalAt_one AlgebraicCurve.Place.differentialCoeff_zero AlgebraicCurve.Place.differentialCoeff_dCoord AlgebraicCurve.TranscendenceTower.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.injEq AlgebraicCurve.TranscendenceTower.mk.injEq AlgebraicCurve.PoleDivisorPackage.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.sizeOf_spec AlgebraicCurve.PoleDivisorPackage.mk.injEq AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.sizeOf_spec AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.injEq AlgebraicCurve.adeleSingle_coe AlgebraicCurve.kaehlerResidueTermKFam_apply AlgebraicCurve.Place.LocalResidueData.mk.injEq AlgebraicCurve.Place.LocalResidueData.mk.sizeOf_spec AlgebraicCurve.Place.kw_ffgc_adicCompletionComapIntegers_coe AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.sizeOf_spec AlgebraicCurve.Place.mem_simplePoleSubmodule AlgebraicCurve.Place.coe_uniformizerSubring ModularCurve.Lg37.Lg37CompletionSection.mk.injEq AlgebraicCurve.Place.CoefficientFieldSection.mk.injEq AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.injEq"
p2m_attr_erase "simp" "ModularCurve.Lg37.Lg37CompletionSection.mk.sizeOf_spec AlgebraicCurve.Place.CoefficientFieldSection.mk.sizeOf_spec AlgebraicCurve.Place.poleSubmodule_one AlgebraicCurve.Place.mem_poleSubmodule"

set_option autoImplicit false

universe u

p2m_open "CategoryTheory CategoryTheory.Limits AlgebraicGeometry P2MW.S_AlgebraicGeometry_Scheme_TwoAffineOpenCover_finrank_H1_sectionsOf_unit_eq_genusFF_of_curveModel.AlgebraicGeometry AlgebraicGeometry.RelPicard NeronModelInfra CategoryTheory.MonoidalCategory AlgebraicGeometry.SmoothProperCurve TensorProduct AlgebraicCurve~genus~cechDiff"

noncomputable section

namespace AlgebraicGeometry
p2m_export "AlgebraicGeometry" "SmoothOfRelativeDimension IsProper GeometricallyIntegral Spec IsIntegral Spec.map Scheme Spec.map_id Scheme.Modules.pullbackId Scheme.Modules IsIntegral.of_isIso geometrically Scheme.TwoAffineOpenCover Scheme.TwoAffineOpenCover.specMap Scheme.TwoAffineOpenCover.exists_linearEquiv_sectionsOf_of_iso Scheme.TwoAffineOpenCover.finrank_H1_sectionsOf_unit_eq_and_finrank_H0_eq_one Scheme.TwoAffineOpenCover.finrank_cechDiff_baseChange_of_isAlgClosed geometricallyIntegral_of_isAlgClosed"
namespace GGImpl
namespace WDisGenus
p2m_open "AlgebraicGeometry"

section Generic

variable {R : Type u} [CommRing R] {𝒰 𝒰' : TwoChartCech.Cover.{u, u} R}
  (S : TwoChartCech.Sections.{u, u, u} 𝒰) (S' : TwoChartCech.Sections.{u, u, u} 𝒰')

theorem h0h1_of_equiv (g0 : S.M0 ≃ₗ[R] S'.M0) (g1 : S.M1 ≃ₗ[R] S'.M1) (g01 : S.M01 ≃ₗ[R] S'.M01)
    (h0 : ∀ m, S'.r0 (g0 m) = g01 (S.r0 m)) (h1 : ∀ m, S'.r1 (g1 m) = g01 (S.r1 m)) :
    Nonempty (S.H0 ≃ₗ[R] S'.H0) ∧ Nonempty (S.H1 ≃ₗ[R] S'.H1) := by
  let G : (S.M0 × S.M1) ≃ₗ[R] (S'.M0 × S'.M1) := g0.prodCongr g1
  have hG : ∀ p : S.M0 × S.M1, G p = (g0 p.1, g1 p.2) := fun p => rfl
  have hd : ∀ p, S'.cechDiff (G p) = g01 (S.cechDiff p) := by
    intro p
    rw [hG, TwoChartCech.Sections.cechDiff_apply, TwoChartCech.Sections.cechDiff_apply, map_sub, h0, h1]
  refine ⟨⟨LinearEquiv.ofSubmodules G S.H0 S'.H0 ?_⟩, ⟨Submodule.Quotient.equiv _ _ g01 ?_⟩⟩
  · ext q
    simp only [Submodule.mem_map, LinearMap.mem_ker, LinearEquiv.coe_coe]
    constructor
    · rintro ⟨p, hp, rfl⟩
      rw [hd, hp, map_zero]
    · intro hq
      refine ⟨G.symm q, ?_, G.apply_symm_apply q⟩
      apply g01.injective
      rw [← hd, G.apply_symm_apply, hq, map_zero]
  · ext y
    simp only [Submodule.mem_map, LinearMap.mem_range, LinearEquiv.coe_coe]
    constructor
    · rintro ⟨_, ⟨p, rfl⟩, rfl⟩
      exact ⟨G p, hd p⟩
    · rintro ⟨q, rfl⟩
      exact ⟨S.cechDiff (G.symm q), ⟨_, rfl⟩, by rw [← hd, G.apply_symm_apply]⟩

end Generic

section UnitEq

variable {R : Type u} [CommRing R] {X : Scheme.{u}} (𝒱 : X.TwoAffineOpenCover) (x : X ⟶ Spec (.of R))

noncomputable def idEquiv0 :
    (𝒱.sectionsOf x (SheafOfModules.unit X.ringCatSheaf : X.Modules)).M0 ≃ₗ[R] (𝒱.structureSheafSections x).M0 :=
  { toFun := fun m => (show Γ(X, 𝒱.U0) from m)
    invFun := fun a => (show Γ((SheafOfModules.unit X.ringCatSheaf : X.Modules), 𝒱.U0) from a)
    map_add' := fun a b => rfl
    map_smul' := fun r m => rfl
    left_inv := fun m => rfl
    right_inv := fun a => rfl }

noncomputable def idEquiv1 :
    (𝒱.sectionsOf x (SheafOfModules.unit X.ringCatSheaf : X.Modules)).M1 ≃ₗ[R] (𝒱.structureSheafSections x).M1 :=
  { toFun := fun m => (show Γ(X, 𝒱.U1) from m)
    invFun := fun a => (show Γ((SheafOfModules.unit X.ringCatSheaf : X.Modules), 𝒱.U1) from a)
    map_add' := fun a b => rfl
    map_smul' := fun r m => rfl
    left_inv := fun m => rfl
    right_inv := fun a => rfl }

noncomputable def idEquiv01 :
    (𝒱.sectionsOf x (SheafOfModules.unit X.ringCatSheaf : X.Modules)).M01 ≃ₗ[R]
      (𝒱.structureSheafSections x).M01 :=
  { toFun := fun m => (show Γ(X, 𝒱.U0 ⊓ 𝒱.U1) from m)
    invFun := fun a => (show Γ((SheafOfModules.unit X.ringCatSheaf : X.Modules), 𝒱.U0 ⊓ 𝒱.U1) from a)
    map_add' := fun a b => rfl
    map_smul' := fun r m => rfl
    left_inv := fun m => rfl
    right_inv := fun a => rfl }

theorem unit_equiv :
    Nonempty ((𝒱.sectionsOf x (SheafOfModules.unit X.ringCatSheaf : X.Modules)).H0 ≃ₗ[R]
        (𝒱.structureSheafSections x).H0) ∧
      Nonempty ((𝒱.sectionsOf x (SheafOfModules.unit X.ringCatSheaf : X.Modules)).H1 ≃ₗ[R]
        (𝒱.structureSheafSections x).H1) := by
  refine h0h1_of_equiv _ _ (idEquiv0 𝒱 x) (idEquiv1 𝒱 x)
    (idEquiv01 𝒱 x) ?_ ?_
  · intro m; rfl
  · intro m
    show (1 : Γ(X, 𝒱.U0 ⊓ 𝒱.U1)) * _ = _
    rw [one_mul]; rfl

end UnitEq

theorem finrank_baseChange_self {K : Type u} [Field K] {A B : Type u} [AddCommGroup A] [Module K A]
    [AddCommGroup B] [Module K B] (d : A →ₗ[K] B) :
    Module.finrank K (LinearMap.ker (d.baseChange K)) = Module.finrank K (LinearMap.ker d) ∧
      Module.finrank K ((K ⊗[K] B) ⧸ LinearMap.range (d.baseChange K)) =
        Module.finrank K (B ⧸ LinearMap.range d) := by
  let eA := TensorProduct.lid K A
  let eB := TensorProduct.lid K B
  have hd : ∀ z, eB (d.baseChange K z) = d (eA z) := by
    intro z
    induction z using TensorProduct.induction_on with
    | zero => simp
    | tmul a m => simp [eA, eB, LinearMap.baseChange_tmul, TensorProduct.lid_tmul]
    | add z w hz hw => rw [map_add, map_add, hz, hw, map_add, map_add]
  constructor
  · refine (LinearEquiv.ofSubmodules eA (LinearMap.ker (d.baseChange K)) (LinearMap.ker d) ?_).finrank_eq
    ext q
    simp only [Submodule.mem_map, LinearMap.mem_ker, LinearEquiv.coe_coe]
    constructor
    · rintro ⟨p, hp, rfl⟩
      rw [← hd, hp, map_zero]
    · intro hq
      refine ⟨eA.symm q, ?_, eA.apply_symm_apply q⟩
      apply eB.injective
      rw [hd, eA.apply_symm_apply, hq, map_zero]
  · refine (Submodule.Quotient.equiv _ _ eB ?_).finrank_eq
    ext y
    simp only [Submodule.mem_map, LinearMap.mem_range, LinearEquiv.coe_coe]
    constructor
    · rintro ⟨_, ⟨p, rfl⟩, rfl⟩
      exact ⟨eA p, (hd p).symm⟩
    · rintro ⟨q, rfl⟩
      exact ⟨d.baseChange K (eA.symm q), ⟨_, rfl⟩, by rw [hd, eA.apply_symm_apply]⟩

theorem rr_of_cech (K : Type u) [Field K] [IsAlgClosed K] {X : Scheme.{u}} (x : X ⟶ Spec (CommRingCat.of K))
    [IsIntegral X] [IsProper x] [SmoothOfRelativeDimension 1 x]
    (g : ℕ) (𝒱 : X.TwoAffineOpenCover)
    (hg : Module.finrank K (𝒱.sectionsOf x (SheafOfModules.unit X.ringCatSheaf : X.Modules)).H1 = g) :
    (∀ (L : Type u) [Field L] [Algebra K L] (M : CurveModel K L) (e : M.C ≅ X)
      (_ : e.hom ≫ x = M.toBase) (Kc : Divisor K L) (g' : ℕ),
      (∀ D : Divisor K L, (ell D : ℤ) - ell (Kc - D) = Divisor.degree D + 1 - g') → g' = g) ∧
    ∃ (L : Type u) (_ : Field L) (_ : Algebra K L) (M : CurveModel K L) (e : M.C ≅ X)
      (_ : e.hom ≫ x = M.toBase) (Kc : Divisor K L),
      ∀ D : Divisor K L, (ell D : ℤ) - ell (Kc - D) = Divisor.degree D + 1 - g := by
  classical

  obtain ⟨-, ⟨eH1⟩⟩ := unit_equiv 𝒱 x
  rw [eH1.finrank_eq] at hg

  haveI : GeometricallyIntegral x := AlgebraicGeometry.geometricallyIntegral_of_isAlgClosed x
  haveI : IsIntegral (pullback x (Scheme.TwoAffineOpenCover.specMap K K)) := inferInstance
  obtain ⟨-, -, hk1⟩ := Scheme.TwoAffineOpenCover.finrank_cechDiff_baseChange_of_isAlgClosed 𝒱 x K
  obtain ⟨-, hb1⟩ := finrank_baseChange_self (𝒱.structureSheafSections x).cechDiff

  have hG : (by
      letI := (baseToFunctionField
        (pullback.snd x (Scheme.TwoAffineOpenCover.specMap K K))).toAlgebra
      exact genusFF K (pullback x (Scheme.TwoAffineOpenCover.specMap K K)).functionField) = g := by
    rw [← hk1, hb1]
    exact hg

  have hspec : Scheme.TwoAffineOpenCover.specMap K K = 𝟙 _ := by
    show Spec.map (CommRingCat.ofHom (algebraMap K K)) = 𝟙 _
    rw [Algebra.algebraMap_self, CommRingCat.ofHom_id]
    exact Spec.map_id _
  have sq : IsPullback (𝟙 X) x x (Scheme.TwoAffineOpenCover.specMap K K) := by
    rw [hspec]; exact IsPullback.of_horiz_isIso ⟨by simp⟩
  let eX : X ≅ pullback x (Scheme.TwoAffineOpenCover.specMap K K) := sq.isoPullback
  have heX : eX.hom ≫ pullback.snd x (Scheme.TwoAffineOpenCover.specMap K K) = x := sq.isoPullback_hom_snd
  have heX' : eX.inv ≫ x = pullback.snd x (Scheme.TwoAffineOpenCover.specMap K K) := by
    rw [Iso.inv_comp_eq]; exact heX.symm

  have huniq : ∀ (L : Type u) [Field L] [Algebra K L] (M : CurveModel K L) (e : M.C ≅ X)
      (_ : e.hom ≫ x = M.toBase) (Kc : Divisor K L) (g' : ℕ),
      (∀ D : Divisor K L, (ell D : ℤ) - ell (Kc - D) = Divisor.degree D + 1 - g') → g' = g := by
    intro L _ _ M e he Kc g' hRR
    have h1 : g' = genusFF K L := CurveModel.eq_genusFF_of_forall_ell_sub_ell_eq M hRR
    have he2 : (e ≪≫ eX).hom ≫ pullback.snd x (Scheme.TwoAffineOpenCover.specMap K K) = M.toBase := by
      simp only [Iso.trans_hom, Category.assoc]
      rw [heX]; exact he
    have h2 : genusFF K L = (by
        letI := (baseToFunctionField
          (pullback.snd x (Scheme.TwoAffineOpenCover.specMap K K))).toAlgebra
        exact genusFF K (pullback x (Scheme.TwoAffineOpenCover.specMap K K)).functionField) := by
      letI := M.functionFieldAlgebra
      letI := (baseToFunctionField
        (pullback.snd x (Scheme.TwoAffineOpenCover.specMap K K))).toAlgebra
      obtain ⟨φ⟩ := nonempty_algEquiv_functionField_of_iso M.toBase
        (pullback.snd x (Scheme.TwoAffineOpenCover.specMap K K)) (e ≪≫ eX) he2
      exact (genusFF_eq_of_algEquiv M.ffAlgEquiv).trans (genusFF_eq_of_algEquiv φ)
    rw [h1, h2, hG]
  refine ⟨huniq, ?_⟩

  obtain ⟨L, _, _, M, e, he, Kc, g₀, hRR⟩ :=
    exists_curveModel_riemannRoch_of_isAlgClosed K x K (Scheme.TwoAffineOpenCover.specMap K K)
  have he' : (e ≪≫ eX.symm).hom ≫ x = M.toBase := by
    simp only [Iso.trans_hom, Iso.symm_hom, Category.assoc]
    rw [heX']; exact he
  have h3 : g₀ = g := huniq L M (e ≪≫ eX.symm) he' Kc g₀ hRR
  subst h3
  exact ⟨L, inferInstance, inferInstance, M, e ≪≫ eX.symm, he', Kc, hRR⟩

end AlgebraicGeometry.GGImpl.WDisGenus

namespace AlgebraicGeometry
p2m_export "AlgebraicGeometry" "SmoothOfRelativeDimension IsProper GeometricallyIntegral Spec IsIntegral Spec.map Scheme Spec.map_id Scheme.Modules.pullbackId Scheme.Modules IsIntegral.of_isIso geometrically Scheme.TwoAffineOpenCover Scheme.TwoAffineOpenCover.specMap Scheme.TwoAffineOpenCover.exists_linearEquiv_sectionsOf_of_iso Scheme.TwoAffineOpenCover.finrank_H1_sectionsOf_unit_eq_and_finrank_H0_eq_one Scheme.TwoAffineOpenCover.finrank_cechDiff_baseChange_of_isAlgClosed geometricallyIntegral_of_isAlgClosed"
namespace GGImpl
namespace GenusImpl
p2m_open "AlgebraicGeometry"

theorem cover_ext {X : Scheme.{u}} {𝒱 𝒱' : X.TwoAffineOpenCover}
    (h0 : 𝒱.U0 = 𝒱'.U0) (h1 : 𝒱.U1 = 𝒱'.U1) : 𝒱 = 𝒱' := by
  cases 𝒱; cases 𝒱'; cases h0; cases h1; rfl

theorem finrank_H0_H1_congr {k : Type u} [Field k] {X : Scheme.{u}} (x : X ⟶ Spec (CommRingCat.of k))
    (𝒱 : X.TwoAffineOpenCover) {M M' : X.Modules} (e : M ≅ M') :
    Module.finrank k (𝒱.sectionsOf x M).H0 = Module.finrank k (𝒱.sectionsOf x M').H0 ∧
      Module.finrank k (𝒱.sectionsOf x M).H1 = Module.finrank k (𝒱.sectionsOf x M').H1 := by
  obtain ⟨𝒱₂, h0, h1, ⟨e0⟩, ⟨e1⟩⟩ :=
    Scheme.TwoAffineOpenCover.exists_linearEquiv_sectionsOf_of_iso x x (Iso.refl X) (Category.id_comp x)
      𝒱 M' M (e ≪≫ ((Scheme.Modules.pullbackId X).app M').symm)
  obtain rfl : 𝒱₂ = 𝒱 := cover_ext h0 h1
  exact ⟨e0.finrank_eq, e1.finrank_eq⟩

theorem finrank_H0_unit_eq_one (k : Type u) [Field k] [IsAlgClosed k] {C : Scheme.{u}} (c : C ⟶ Spec (CommRingCat.of k))
    [IsProper c] [SmoothOfRelativeDimension 1 c] [GeometricallyIntegral c] (𝒱 : C.TwoAffineOpenCover) :
    Module.finrank k (𝒱.sectionsOf c (SheafOfModules.unit C.ringCatSheaf)).H0 = 1 := by
  haveI : IsIntegral C :=
    haveI : IsIntegral (pullback c (𝟙 (Spec (CommRingCat.of k)))) := inferInstance
    IsIntegral.of_isIso (pullback.fst c (𝟙 (Spec (CommRingCat.of k))))
  exact (Scheme.TwoAffineOpenCover.finrank_H1_sectionsOf_unit_eq_and_finrank_H0_eq_one k c _
    (AlgebraicGeometry.GGImpl.WDisGenus.rr_of_cech k c _ 𝒱 rfl).1 𝒱).2

end AlgebraicGeometry.GGImpl.GenusImpl

end

open AlgebraicGeometry.GGImpl.GenusImpl AlgebraicGeometry.GGImpl.WDisGenus in
theorem solution
    {k : Type u} [Field k] [IsAlgClosed k] {C : Scheme.{u}} (c : C ⟶ Spec (CommRingCat.of k))
    [IsProper c] [SmoothOfRelativeDimension 1 c] [GeometricallyIntegral c]
    (F : Type u) [Field F] [Algebra k F] (Mdl : AlgebraicCurve.CurveModel k F) (e : Mdl.C ≅ C)
    (he : e.hom ≫ c = Mdl.toBase)
    (𝒲 : C.TwoAffineOpenCover) :
    Module.finrank k (𝒲.sectionsOf c (SheafOfModules.unit C.ringCatSheaf)).H1 = AlgebraicCurve.genusFF k F := by
  classical
  haveI : IsIntegral C :=
    haveI : IsIntegral (pullback c (𝟙 (Spec (CommRingCat.of k)))) := inferInstance
    IsIntegral.of_isIso (pullback.fst c (𝟙 (Spec (CommRingCat.of k))))

  obtain ⟨-, L, _, _, M, e', he', Kc, hRR⟩ := rr_of_cech k c _ 𝒲 rfl
  have h1 := AlgebraicCurve.CurveModel.eq_genusFF_of_forall_ell_sub_ell_eq M hRR

  letI := M.functionFieldAlgebra
  letI := Mdl.functionFieldAlgebra
  letI := (baseToFunctionField c).toAlgebra
  obtain ⟨φ⟩ := AlgebraicCurve.nonempty_algEquiv_functionField_of_iso M.toBase c e' he'
  obtain ⟨ψ⟩ := AlgebraicCurve.nonempty_algEquiv_functionField_of_iso Mdl.toBase c e he
  have h2 : genusFF k L = genusFF k C.functionField :=
    (genusFF_eq_of_algEquiv M.ffAlgEquiv).trans (genusFF_eq_of_algEquiv φ)
  have h3 : genusFF k F = genusFF k C.functionField :=
    (genusFF_eq_of_algEquiv Mdl.ffAlgEquiv).trans (genusFF_eq_of_algEquiv ψ)
  rw [h1, h2, ← h3]

end S_AlgebraicGeometry_Scheme_TwoAffineOpenCover_finrank_H1_sectionsOf_unit_eq_genusFF_of_curveModel
end P2MW
export P2MW.S_AlgebraicGeometry_Scheme_TwoAffineOpenCover_finrank_H1_sectionsOf_unit_eq_genusFF_of_curveModel (solution)
