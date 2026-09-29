-- Prove2me | solution 1 for AlgebraicGeometry.RelPicard.isLFPSurj_relSubPicPresheaf_algEquivZeroCut_baseChange_of_twoGluedSmoothCurveDegenerations
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:03.589526+00:00
-- url     : https://prove2.me/submissions/d8ab8273-c599-5737-a38d-4d8a7e31e44e

import Mathlib
import Definitions.Def_AlgebraicGeometry_NeronModelPropertyBundleCarrier
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import Definitions.Def_AlgebraicGeometry_RepresentsRelSubPic
import Definitions.Def_AlgebraicGeometry_RelPicardAlgEquivZeroCut
import Definitions.Def_AlgebraicGeometry_RelSubPicPresheaf
import Definitions.Def_CategoryTheory_OverTotalPresheaf
import Definitions.Def_AlgebraicGeometry_LocalRepresentabilityULift
import Definitions.Def_AlgebraicGeometry_AffineLimit
import Definitions.Def_AlgebraicGeometry_RelPicardThetaBundle
import Definitions.Def_AlgebraicGeometry_TwoAffineOpenCover
import Definitions.Def_AlgebraicGeometry_TwoChartCechSectionsOf
import Definitions.Def_AlgebraicGeometry_RelEffCartierDiv
import Definitions.Def_AlgebraicGeometry_RelEffCartierDivSupportedIn
import Definitions.Def_AlgebraicGeometry_RelEffCartierDivFunctor
import Definitions.Def_AlgebraicGeometry_RelEffCartierDivRestrict
import Definitions.Def_AlgebraicGeometry_IdealSheafModule
import Definitions.Def_SheafOfModules_Monoidal
import Definitions.Def_AlgebraicGeometry_RelEffCartierDivTwist2
import Definitions.Def_AlgebraicGeometry_ModulesSectionZeroScheme

import Definitions.Def_AlgebraicGeometry_SmoothProperCurveBase
import Definitions.Def_AlgebraicGeometry_RelEffCartierDivSum
import Definitions.Def_AlgebraicGeometry_RelPicardChartSections

import Definitions.Def_AlgebraicGeometry_ModulesPullbackMonoidal
import Theorems.Thm_AlgebraicGeometry_RelPicard_exists_fibreIso_hom_comp_eq
import Theorems.Thm_AlgebraicGeometry_Scheme_TwoAffineOpenCover_exists_linearEquiv_sectionsOf_of_iso
import Theorems.Thm_AlgebraicGeometry_geometricallyIntegral_of_bijective_algebraMap_sections_of_smooth
import Theorems.Thm_AlgebraicGeometry_smoothOfRelativeDimension_of_irreducibleSpace
import Theorems.Thm_AlgebraicGeometry_exists_mem_and_smoothOfRelativeDimension_one_of_smoothOfRelativeDimension_pullback_snd
import Theorems.Thm_AlgebraicGeometry_RelPicard_IsAlgEquivZero_eulerChar_sectionsOf_tensor_eq
import Theorems.Thm_AlgebraicGeometry_RelPicard_isAlgEquivZero_iff_eulerChar_sectionsOf_eq
import Theorems.Thm_AlgebraicGeometry_RelPicard_isOpen_setOf_isAlgEquivZero_fibre_of_twoStrata
import Theorems.Thm_AlgebraicGeometry_RelPicard_isLFPSurj_relSubPicPresheaf_algEquivZeroCut_of_isOpen_setOf_isAlgEquivZero
import Theorems.Thm_AlgebraicGeometry_RelPicard_isAlgEquivZero_fibre_of_range_subset_singleton_of_twoGluedSmoothCurveDegenerations
import Theorems.Thm_AlgebraicGeometry_RelPicard_exists_isOpen_inter_preimage_eq_setOf_isAlgEquivZero_fibre_of_smoothLocus_of_twoGluedSmoothCurveDegenerations
import Theorems.Thm_AlgebraicGeometry_RelPicard_twoGluedSmoothCurveDegenerations_baseChange
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_RelPicard_isLFPSurj_relSubPicPresheaf_algEquivZeroCut_baseChange_of_twoGluedSmoothCurveDegenerations
p2m_attr_erase "instance" "AlgebraicGeometry.OModulePresheaf.isScalarTower AlgebraicGeometry.Scheme.OrderedAffineCover.instLinearOrder AlgebraicGeometry.OModulePresheaf.module AlgebraicGeometry.Scheme.OrderedAffineCover.instFintype AlgebraicGeometry.Scheme.OrderedAffineCover.instFintypeIdx AlgebraicGeometry.OModulePresheaf.addCommGroup AlgebraicGeometry.Scheme.OrderedAffineCover.instDecidableEqIdx AlgebraicGeometry.OModulePresheaf.moduleSections AlgebraicGeometry.OModulePresheaf.instSubsingletonObjZero AlgebraicGeometry.OModulePresheaf.Leray.relAltC_scalarTower AlgebraicGeometry.OModulePresheaf.Leray.ker_relAltd_modΓ AlgebraicGeometry.OModulePresheaf.Leray.relAltC_modΓ AlgebraicGeometry.OModulePresheaf.Leray.biC_abGrp AlgebraicGeometry.OModulePresheaf.Leray.relAltH_modΓ AlgebraicGeometry.OModulePresheaf.Leray.ker_relAltd_smul AlgebraicGeometry.OModulePresheaf.Leray.relAltH_scalarTower AlgebraicGeometry.OModulePresheaf.Leray.relAltH_smul AlgebraicGeometry.OModulePresheaf.Leray.biC_module AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instDecidableEqIdx AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instFintype AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instLinearOrder AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instFintypeIdx DoubleComplex.instModuleE₂I DoubleComplex.Bounded.modR DoubleComplex.instModuleE₂II DoubleComplex.instAddCommGroupE₂II DoubleComplex.Bounded.abGrp DoubleComplex.instAddCommGroupE₂I AlgebraicGeometry.ChowDatum.hι_closed AlgebraicGeometry.ChowDatumProj.hιN_closed AlgebraicGeometry.ChowDatumProj.hp_proper AlgebraicGeometry.ChowDatum.hp_isoU AlgebraicGeometry.ChowDatum.hp_proper AlgebraicGeometry.ProjSpace.algebraAway AlgebraicGeometry.ProjSpace.instIsProperProdOverπ AlgebraicGeometry.ChowDatumProj.hp_isoU AlgebraicGeometry.ProjSpace.isProper_π AlgebraicGeometry.ProjSpace.finiteType_mvPolynomial ProjSpaceCech.GradedModule.H.module ProjSpaceCech.GradedModule.H.addCommGroup"
p2m_attr_erase "instance" "ProjSpaceCech.GradedModule.sec.instAdd ProjSpaceCech.GradedModule.sec.instNeg ProjSpaceCech.GradedModule.acg ProjSpaceCech.GradedModule.Frac.setoid ProjSpaceCech.GradedModule.modR ProjSpaceCech.GradedModule.sec.instModule ProjSpaceCech.GradedModule.sec.instAddCommGroup ProjSpaceCech.GradedModule.sec.instZero ProjSpaceCech.GradedModule.Presentation.fJ ProjSpaceCech.GradedModule.sec.instSMul ProjSpaceCech.Twist.H.module ProjSpaceCech.Idx.instFintype ProjSpaceCech.Twist.H.addCommGroup ProjSpaceCech.Idx.instDecidableEq ProjSpaceCech.Twist.Mon.instDecidableEq ProjSpaceCech.Twist.cochain.instAddCommGroup ProjSpaceCech.Twist.cochain.instModule AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instNeg AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instSMulInt AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instAddCommGroup AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instAdd AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instSub AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instModuleCarrierObjOppositeOpensCarrierCarrierCommRingCatPresheafOpOpensTop AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instSMulCarrierObjOppositeOpensCarrierCarrierCommRingCatPresheafOpOpensTop AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instSMulNat AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instZero AlgebraicCurve.IsCurveOver.instNontrivialKaehler AlgebraicCurve.IsCurveOver.instFreeKaehler AlgebraicCurve.IsCurveOver.toHasPrincipalDivisors AlgebraicCurve.IsCurveOver.instFiniteResidue AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.instFundamentalIdentityOfSumRamificationInertia AlgebraicCurve.Place.instIsScalarTowerResidueFieldRestrictPushforward AlgebraicCurve.Place.instAlgebraResidueFieldRestrictPushforward AlgebraicCurve.Place.instIsLocalHomRestrictInclusion AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt"
p2m_attr_erase "instance" "AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.SemilinearAut.instDistribMulActionSubtypeProdRingAutMemSubgroupPic0 AlgebraicCurve.SemilinearAut.instDistribMulActionSubtypeProdRingAutMemSubgroupDivisor AlgebraicCurve.Pic0.instModuleZModTorsion AlgebraicCurve.SemilinearAut.instSMulSubtypeProdRingAutMemSubgroupPlace AlgebraicCurve.SemilinearAut.instDistribMulActionTorsion AlgebraicCurve.SemilinearAut.instSMulSubtypeProdRingAutMemSubgroupPic0 AlgebraicCurve.SemilinearAut.instSMulTorsion AlgebraicCurve.SemilinearAut.instMulActionSubtypeProdRingAutMemSubgroupPlace AlgebraicCurve.SemilinearAut.instSMulCommClassZModTorsion AlgebraicCurve.SemilinearAut.instMulSemiringActionSubtypeProdRingAutMemSubgroup instDecEqAlgebraicClosureRat WeierstrassCurve.Affine.Point.instDistribMulActionAlgEquiv WeierstrassCurve.Affine.Point.instModuleZModTorsionBy WeierstrassCurve.Affine.Point.instSMulTorsionBy WeierstrassCurve.Affine.Point.instDistribMulActionTorsionBy WeierstrassCurve.Affine.Point.instSMulAlgEquiv WeierstrassCurve.Affine.Point.instSMulCommClassAlgEquivZModTorsionBy AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions AlgebraicCurve.instHasLocalResidue_of_hasCanonicalLocalResidueK AlgebraicCurve.instHasCanonicalLocalResidueK_of_hasCanonicalLocalResidueKStar AlgebraicCurve.Place.kw_ffgc_finiteDimensional_adicCompletion instAlgebraSubtypeMemValuationSubring_definitions AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersIntegersCompletion ModularCurve.KwF4gRRTate.instAlgebraKAdicCompletionIntegers AlgebraicCurve.Place.kw_ffgc_continuousSMul_adicCompletionComap AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersCompletionCompletion IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions AlgebraicCurve.instHasCanonicalLocalResidueK AlgebraicCurve.Place.instAlgebra_restrictResidueField AlgebraicCurve.Place.instIsScalarTower_restrictResidueField AlgebraicCurve.instHasLocalResidue AlgebraicCurve.HasSeparableResidue.of_perfectField_of_isCurveOver AlgebraicCurve.HasSeparableResidue.of_perfectField AlgebraicCurve.Place.instIsLocalHom_restrictSubringHom"
p2m_attr_erase "instance" "AlgebraicCurve.instHasCanonicalLocalResidueKStar ModularCurve.KwNo6Pin.isLocalRing_completion SheafOfModules.isIso_ihomModelToIhom AlgebraicGeometry.FGSubalgebra.instIsDirectedLe AlgebraicGeometry.FGSubalgebra.instQuasiSeparatedSpaceCarrierCarrierCommRingCatObjOppositeSchemeSpecDiagram AlgebraicGeometry.FGSubalgebra.instIsCofilteredOpposite AlgebraicGeometry.FGSubalgebra.instIsAffineObjOppositeSchemeSpecDiagram AlgebraicGeometry.FGSubalgebra.instNonempty AlgebraicGeometry.FGSubalgebra.instNonemptySubtypeLeSubalgebraValFG AlgebraicGeometry.FGSubalgebra.instCompactSpaceCarrierCarrierCommRingCatObjOppositeSchemeSpecDiagram AlgebraicGeometry.FGSubalgebra.instIsDirectedSubtypeLeSubalgebraValFG AlgebraicGeometry.FGSubalgebra.instIsAffineHomMapOppositeSchemeSpecDiagram AlgebraicGeometry.FGSubalgebra.instIsFiltered AlgebraicGeometry.FGSubalgebra.tensorStage_directedSystem"
p2m_attr_erase "simp" "RegularLocalRingQuotientAscent.dualNumberFst_apply AlgebraicGeometry.Scheme.OrderedAffineCover.mk.injEq AlgebraicGeometry.OModulePresheaf.mk.sizeOf_spec AlgebraicGeometry.Scheme.OrderedAffineCover.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.mk.injEq TwoChartCech.Mumford.dK_apply TwoChartCech.Mumford.ι0_apply TwoChartCech.Mumford.ι1_apply TwoChartCech.KerCoprod.dK_apply TwoChartCech.KerCoprod.ι1_apply TwoChartCech.KerCoprod.ι0_apply AlgebraicGeometry.tilde.functorCompPullbackSpecIso_app AlgebraicGeometry.OModulePresheaf.prod_obj AlgebraicGeometry.OModulePresheaf.restrOpen_obj AlgebraicGeometry.OModulePresheaf.DevissageStep.mk.injEq AlgebraicGeometry.OModulePresheaf.pushforward_obj AlgebraicGeometry.OModulePresheaf.im_obj AlgebraicGeometry.OModulePresheaf.pow_obj AlgebraicGeometry.OModulePresheaf.fstHom_app AlgebraicGeometry.OModulePresheaf.ker_obj AlgebraicGeometry.OModulePresheaf.coker_obj AlgebraicGeometry.OModulePresheaf.DevissageStep.mk.sizeOf_spec AlgebraicGeometry.Scheme.OrderedAffineCover.preimage_U AlgebraicGeometry.OModulePresheaf.sndHom_app AlgebraicGeometry.OModulePresheaf.Hom.mk.injEq AlgebraicGeometry.OModulePresheaf.Hom.id_app AlgebraicGeometry.OModulePresheaf.AffHom.appSections_apply AlgebraicGeometry.OModulePresheaf.AffHom.comp_app AlgebraicGeometry.OModulePresheaf.AffSES.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.AffHom.kerMap_coe AlgebraicGeometry.OModulePresheaf.AffHom.id_app AlgebraicGeometry.OModulePresheaf.Hom.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.Hom.toAffHom_app AlgebraicGeometry.OModulePresheaf.SES.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.AffHom.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.Hom.comp_app AlgebraicGeometry.OModulePresheaf.SES.mk.injEq AlgebraicGeometry.OModulePresheaf.AffHom.mk.injEq AlgebraicGeometry.OModulePresheaf.Hom.appSections_apply AlgebraicGeometry.OModulePresheaf.AffSES.mk.injEq"
p2m_attr_erase "simp" "AlgebraicGeometry.OModulePresheaf.Leray.restrictToPreimage_U AlgebraicGeometry.Scheme.OrderedAffineCover.toCoverOf_U AlgebraicGeometry.Scheme.OrderedAffineCoverOf.mk.sizeOf_spec AlgebraicGeometry.Scheme.OrderedAffineCoverOf.mk.injEq AlgebraicGeometry.Scheme.OrderedAffineCover.restrict_U DoubleComplex.Bounded.mk.injEq DoubleComplex.Bounded.mk.sizeOf_spec DoubleComplex.Convergence.mk.injEq DoubleComplex.Convergence.mk.sizeOf_spec DoubleComplex.SubQuot.mk.sizeOf_spec DoubleComplex.SubQuot.mk.injEq AlgebraicGeometry.ChowDatumProj.mk.sizeOf_spec AlgebraicGeometry.ChowDatum.mk.sizeOf_spec AlgebraicGeometry.ChowDatumProj.mk.injEq AlgebraicGeometry.ChowDatum.mk.injEq ProjSpaceCech.GradedModule.mk.injEq ProjSpaceCech.GradedModule.mk.sizeOf_spec ProjSpaceCech.GradedModule.Frac.mk.sizeOf_spec ProjSpaceCech.GradedModule.Presentation.mk.injEq ProjSpaceCech.GradedModule.Frac.mk.injEq ProjSpaceCech.GradedModule.Presentation.mk.sizeOf_spec ProjSpaceCech.GradedModule.Hom.shift_toLinearMap ProjSpaceCech.GradedModule.Hom.mk.sizeOf_spec ProjSpaceCech.GradedModule.Hom.mk.injEq AlgebraicGeometry.RelPicard.fst_toProdSpec AlgebraicGeometry.RelPicard.toProdSpec_fst_assoc AlgebraicGeometry.RelPicard.pointsSubBasepointModule_cons AlgebraicGeometry.RelPicard.pointsSubBasepointModule_nil AlgebraicGeometry.RelPicard.fst_toProdSpec_assoc AlgebraicGeometry.RelPicard.toProdSpec_fst AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.sub_app AlgebraicGeometry.Scheme.IdealSheafData.sres_sresTop AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.add_app AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.mk.sizeOf_spec AlgebraicGeometry.Scheme.IdealSheafData.coe_resLE AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.smul_app AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.coe_ofLE_app AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.ideal_range AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.zero_app AlgebraicGeometry.Scheme.IdealSheafData.sres_sres"
p2m_attr_erase "simp" "AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.comp_app AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.neg_app AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.id_app AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.coe_mulRight_app AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.nsmul_app AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.mk.injEq AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.zsmul_app AlgebraicCurve.coe_cechH0Equiv_apply AlgebraicCurve.cechH1ToH1_mk AlgebraicCurve.lSpaceOn_univ AlgebraicCurve.lSpaceOn_empty AlgebraicCurve.Place.congrEquiv_symm_apply AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply AlgebraicCurve.RationalFunctionField.deg_placeOfPoint AlgebraicCurve.Divisor.mapRestrict_single AlgebraicCurve.Divisor.pushforward_single AlgebraicCurve.Place.coe_restrictInclusion AlgebraicCurve.Place.mem_fiber AlgebraicCurve.Place.restrict_toValuationSubring AlgebraicCurve.Divisor.degree_pushforward AlgebraicCurve.Place.restrictResidueMap_residue AlgebraicCurve.Pic0.coe_pushforwardDegZeroHom AlgebraicCurve.Pic0.coe_pullbackDegZeroHom AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal AlgebraicCurve.IsFrobeniusEndo.frobNormRingHom_apply ModularCurve.frobeniusPushforwardGeomLevelPic0_mk ModularCurve.coe_frobeniusGeomLevelEquiv_apply ModularCurve.coe_frobeniusPushforwardGeomLevelDegZero ModularCurve.heckeFibreGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusGeomLevel_apply_coe ModularCurve.frobeniusPullbackGeomLevelPic0OfIsCurveOver_mk ModularCurve.coe_heckeFibreGeomLevelDegZero ModularCurve.coe_frobeniusPullbackGeomLevelDegZero"
p2m_attr_erase "simp" "ModularCurve.frobeniusPullbackGeomLevelPic0_mk ModularCurve.frobeniusPullbackGeomLevel_single ModularCurve.heckeFibreGeomLevelPic0_mk ModularCurve.frobeniusPushforwardGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusPushforwardGeomLevel_single ModularCurve.qExpandAlgC_apply AlgebraicCurve.Divisor.degree_pushforwardAlong AlgebraicCurve.Pic0.coe_degZeroCorrespondence AlgebraicCurve.Place.mem_fiberAlong AlgebraicCurve.SemilinearAut.toRingAut_inv AlgebraicCurve.SemilinearAut.smul_def AlgebraicCurve.SemilinearAut.smul_single AlgebraicCurve.SemilinearAut.smul_toValuationSubring AlgebraicCurve.SemilinearAut.baseAut_inv AlgebraicCurve.SemilinearAut.baseAut_ofAlgAut AlgebraicCurve.SemilinearAut.toRingAut_ofAlgAut AlgebraicCurve.SemilinearAut.torsionRep_apply AlgebraicCurve.SemilinearAut.toRingAut_one AlgebraicCurve.SemilinearAut.deg_smul AlgebraicCurve.SemilinearAut.degree_smul AlgebraicCurve.SemilinearAut.coe_degZeroSMulHom AlgebraicCurve.SemilinearAut.baseAut_mul AlgebraicCurve.SemilinearAut.coe_smulValuationSubringEquiv_apply AlgebraicCurve.SemilinearAut.baseAut_one AlgebraicCurve.SemilinearAut.ofAlgAut_smul AlgebraicCurve.SemilinearAut.coe_torsion_smul AlgebraicCurve.SemilinearAut.toRingAut_mul AlgebraicCurve.coe_frobeniusPushforwardDegZero AlgebraicCurve.IsFrobeniusEndo.coe_frobeniusPullbackDegZero ModularCurve.jqNModC_one ModularCurve.qExpand_coeff_mul ModularCurve.qExpandₐ_apply ModularCurve.jqN_one ModularCurve.qExpand_single ModularCurve.dedekindPsi_one ModularCurve.ModularPolynomialData.mk.sizeOf_spec ModularCurve.evalAtJ_X ModularCurve.ModularPolynomialData.mk.injEq ModularCurve.constantCoeff_jNum ModularCurve.constantCoeff_eisenstein4"
p2m_attr_erase "simp" "ModularCurve.qExpand_C ModularCurve.coeff_jq_neg_one ModularCurve.constantCoeff_jNumQ ModularCurve.reduceModBivar_C_X ModularCurve.laurentMap_coeff ModularCurve.reduceModBivar_X ModularCurve.laurentMap_single ModularCurve.evalAtJInt_X ModularCurve.evalAtJMod_X ModularCurve.jqNMod_one ModularCurve.aeval_heckeGen ModularCurve.coe_mTorsionGaloisRep_apply ModularCurve.eisensteinSystem_of_dvd ModularCurve.eisensteinSystem_of_not_dvd FreyPackage.mk.sizeOf_spec FreyPackage.mk.injEq WeierstrassCurve.Affine.Point.galoisRepModuleEnd_apply AlgebraicCurve.RationalFunctionField.placeInfty_toValuationSubring AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none AlgebraicCurve.Divisor.evalFun_zero AlgebraicCurve.Place.evalAt_one AlgebraicCurve.Place.differentialCoeff_zero AlgebraicCurve.Place.differentialCoeff_dCoord AlgebraicCurve.TranscendenceTower.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.injEq AlgebraicCurve.TranscendenceTower.mk.injEq AlgebraicCurve.PoleDivisorPackage.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.sizeOf_spec AlgebraicCurve.PoleDivisorPackage.mk.injEq AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.sizeOf_spec AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.injEq AlgebraicCurve.adeleSingle_coe AlgebraicCurve.kaehlerResidueTermKFam_apply AlgebraicCurve.Place.LocalResidueData.mk.injEq AlgebraicCurve.Place.LocalResidueData.mk.sizeOf_spec AlgebraicCurve.Place.kw_ffgc_adicCompletionComapIntegers_coe AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.sizeOf_spec"
p2m_attr_erase "simp" "AlgebraicCurve.Place.mem_simplePoleSubmodule AlgebraicCurve.Place.coe_uniformizerSubring ModularCurve.Lg37.Lg37CompletionSection.mk.injEq AlgebraicCurve.Place.CoefficientFieldSection.mk.injEq AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.injEq ModularCurve.Lg37.Lg37CompletionSection.mk.sizeOf_spec AlgebraicCurve.Place.CoefficientFieldSection.mk.sizeOf_spec AlgebraicCurve.Place.poleSubmodule_one AlgebraicCurve.Place.mem_poleSubmodule PresheafOfModules.InternalHom.IsSheafAux.appAt_toPresheafHom SheafOfModules.ihomSectionsEquivFamily_unit AlgebraicGeometry.Scheme.Modules.restrictHomEquivFamily_apply SheafOfModules.ihomEval_unit_app AlgebraicGeometry.Scheme.Modules.ihomEval_zero_right AlgebraicGeometry.Scheme.Modules.ihomEval_zero_left AlgebraicGeometry.Scheme.Modules.homOfFamily_app_apply SheafOfModules.unit_ihomSectionsEquivFamily AlgebraicGeometry.Scheme.Modules.familyOfHom_app AlgebraicGeometry.Scheme.Modules.restrictUnitIso_hom_app_apply AlgebraicGeometry.Scheme.Modules.restrictUnitIso_inv_app_apply AlgebraicGeometry.Scheme.Modules.restrictHomOfFamily_app_apply AlgebraicGeometry.Scheme.Modules.restrictHomEquivFamily_symm_apply AlgebraicGeometry.Scheme.Modules.tensorSections_zero_right AlgebraicGeometry.Scheme.Modules.map_unitSection AlgebraicGeometry.Scheme.Modules.tensorSectionsBilin_apply AlgebraicGeometry.Scheme.Modules.tensorPowSection_zero AlgebraicGeometry.Scheme.Modules.tensorSections_zero_left AlgebraicGeometry.Scheme.Modules.tensorPow_zero AlgebraicGeometry.Scheme.Modules.tensorPow_succ AlgebraicGeometry.Scheme.Modules.pullbackLocalSection_neg AlgebraicGeometry.Scheme.Modules.pullbackLocalSection_zero AlgebraicGeometry.Scheme.Modules.pullbackLocalSection_sub AlgebraicGeometry.Scheme.Modules.pullbackLocalSection_add AlgebraicGeometry.RelPicard.algEquivZeroGroupCut_toSubPicCondition AlgebraicGeometry.RelPicard.SubPicGroupCondition.mk.injEq AlgebraicGeometry.RelPicard.SubPicGroupCondition.mk.sizeOf_spec GoodReductionJacobian.relativeGroupLawOfGrpObj_inv GoodReductionJacobian.relativeGroupLawOfGrpObj_mul GoodReductionJacobian.overHomEquivSchemeHomOver_apply_coe GoodReductionJacobian.relativeGroupLawOfGrpObj_one"
p2m_attr_erase "simp" "GoodReductionJacobian.overHomEquivSchemeHomOver_symm_apply_left AlgebraicGeometry.FGSubalgebra.cocone_ι_app_apply AlgebraicGeometry.RelPicard.LFP.stageHom_val AlgebraicGeometry.RelPicard.rigSection_snd AlgebraicGeometry.RelPicard.RigidifiedLineBundle.ofInvertible_L AlgebraicGeometry.RelPicard.rigSection_snd_assoc AlgebraicGeometry.RelPicard.BaseChange.relSubPicPresheafRestrictIso_hom_app_coe AlgebraicGeometry.RelPicard.BaseChange.relSubPicPresheafRestrictIso_inv_app_coe AlgebraicGeometry.RelPicard.BaseChange.restrict_P CoherentBaseChange.FibreH0Family.mk.sizeOf_spec CoherentBaseChange.FibreH0Family.mk.injEq"

set_option autoImplicit false

universe u

p2m_open "CategoryTheory CategoryTheory.Limits Opposite CategoryTheory.MonoidalCategory AlgebraicGeometry P2MW.S_AlgebraicGeometry_RelPicard_isLFPSurj_relSubPicPresheaf_algEquivZeroCut_baseChange_of_twoGluedSmoothCurveDegenerations.AlgebraicGeometry AlgebraicGeometry.RelPicard P2MW.S_AlgebraicGeometry_RelPicard_isLFPSurj_relSubPicPresheaf_algEquivZeroCut_baseChange_of_twoGluedSmoothCurveDegenerations.AlgebraicGeometry.RelPicard NeronModelInfra"

p2m_open "AlgebraicGeometry.SmoothProperCurve AlgebraicCurve~genus"

namespace AlgebraicGeometry p2m_export "AlgebraicGeometry" "Spec.map_comp Spec.map_preimage Scheme.Hom.preimage_smoothLocus_eq SmoothOfRelativeDimension IsProper Scheme.Modules.pullback Scheme.Hom GeometricallyIntegral Scheme.Hom.smoothLocus_eq_top_iff Scheme.Hom.preimage_inf GeometricallyIrreducible Scheme.Pullback.range_fst IsAffine isPullback_morphismRestrict Scheme.topIso Scheme.homeoOfIso LocallyOfFiniteType Spec IsIntegral Spec.map Scheme Smooth IsOpenImmersion Scheme.Hom.comp_base Scheme.Hom.comp_appTop Flat IsClosedImmersion IsReduced smoothOfRelativeDimension_isStableUnderBaseChange Scheme.Hom.smoothLocus_eq_top Spec.preimage Scheme.Modules.pullbackCongr HasRingHomProperty.iff_of_source_openCover isAffineOpen_top GeometricallyIrreducible.irreducibleSpace_of_subsingleton Scheme.Modules.pullbackId IsAffineOpen Scheme.Hom.preimage_sup Scheme.Modules Scheme.Opens Scheme.Hom.app_eq_appLE LocallyOfFinitePresentation IsAffineHom isReduced_of_isOpenImmersion HasRingHomProperty Scheme.Opens.ι_preimage_self Scheme.Hom.comp_apply geometrically Scheme.Modules.pullbackComp Scheme.ΓSpecIso isIntegral_of_irreducibleSpace_of_isReduced Scheme.Modules.IsInvertible Scheme.Modules.isInvertible_unit AffineLimit.IsLFPSurj Scheme.TwoAffineOpenCover Scheme.TwoAffineOpenCover.specMap Scheme.TwoAffineOpenCover.algebraOfHom Scheme.TwoAffineOpenCover.algebraMap_algebraOfHom Scheme.Modules.pullbackTensorUnitObjIso Scheme.TwoAffineOpenCover.exists_linearEquiv_sectionsOf_of_iso geometricallyIntegral_of_bijective_algebraMap_sections_of_smooth smoothOfRelativeDimension_of_irreducibleSpace exists_mem_and_smoothOfRelativeDimension_one_of_smoothOfRelativeDimension_pullback_snd" end AlgebraicGeometry
p2m_open_scoped "AlgebraicGeometry" in

theorem AlgebraicGeometry.locallyOfFinitePresentation_of_isNoetherianRing
    {R : Type u} [CommRing R] [IsNoetherianRing R] {C : Scheme.{u}} (c : C ⟶ Spec (CommRingCat.of R))
    [LocallyOfFiniteType c] : LocallyOfFinitePresentation c := by
  have hft := (HasRingHomProperty.iff_of_source_openCover (P := @LocallyOfFiniteType) (f := c) C.affineCover).mp
    inferInstance
  refine (HasRingHomProperty.iff_of_source_openCover (P := @LocallyOfFinitePresentation) (f := c) C.affineCover).mpr
    fun i => ?_

  haveI : IsNoetherianRing Γ(Spec (CommRingCat.of R), ⊤) :=
    isNoetherianRing_of_ringEquiv R (Scheme.ΓSpecIso (CommRingCat.of R)).symm.commRingCatIsoToRingEquiv
  exact RingHom.FinitePresentation.of_finiteType.mp (hft i)

namespace AlgebraicGeometry
p2m_export "AlgebraicGeometry" "Spec.map_comp Spec.map_preimage Scheme.Hom.preimage_smoothLocus_eq SmoothOfRelativeDimension IsProper Scheme.Modules.pullback Scheme.Hom GeometricallyIntegral Scheme.Hom.smoothLocus_eq_top_iff Scheme.Hom.preimage_inf GeometricallyIrreducible Scheme.Pullback.range_fst IsAffine isPullback_morphismRestrict Scheme.topIso Scheme.homeoOfIso LocallyOfFiniteType Spec IsIntegral Spec.map Scheme Smooth IsOpenImmersion Scheme.Hom.comp_base Scheme.Hom.comp_appTop Flat IsClosedImmersion IsReduced smoothOfRelativeDimension_isStableUnderBaseChange Scheme.Hom.smoothLocus_eq_top Spec.preimage Scheme.Modules.pullbackCongr HasRingHomProperty.iff_of_source_openCover isAffineOpen_top GeometricallyIrreducible.irreducibleSpace_of_subsingleton Scheme.Modules.pullbackId IsAffineOpen Scheme.Hom.preimage_sup Scheme.Modules Scheme.Opens Scheme.Hom.app_eq_appLE LocallyOfFinitePresentation IsAffineHom isReduced_of_isOpenImmersion HasRingHomProperty Scheme.Opens.ι_preimage_self Scheme.Hom.comp_apply geometrically Scheme.Modules.pullbackComp Scheme.ΓSpecIso isIntegral_of_irreducibleSpace_of_isReduced Scheme.Modules.IsInvertible Scheme.Modules.isInvertible_unit AffineLimit.IsLFPSurj Scheme.TwoAffineOpenCover Scheme.TwoAffineOpenCover.specMap Scheme.TwoAffineOpenCover.algebraOfHom Scheme.TwoAffineOpenCover.algebraMap_algebraOfHom Scheme.Modules.pullbackTensorUnitObjIso Scheme.TwoAffineOpenCover.exists_linearEquiv_sectionsOf_of_iso geometricallyIntegral_of_bijective_algebraMap_sections_of_smooth smoothOfRelativeDimension_of_irreducibleSpace exists_mem_and_smoothOfRelativeDimension_one_of_smoothOfRelativeDimension_pullback_snd"
namespace RelPicard
p2m_export "AlgebraicGeometry.RelPicard" "baseChangeSnd RigidifiedLineBundle fibreAt IsAlgEquivZero algEquivZeroCut relSubPicPresheaf fibreModule sectionFibrePoint exists_fibreIso_hom_comp_eq IsAlgEquivZero.eulerChar_sectionsOf_tensor_eq isAlgEquivZero_iff_eulerChar_sectionsOf_eq isOpen_setOf_isAlgEquivZero_fibre_of_twoStrata isLFPSurj_relSubPicPresheaf_algEquivZeroCut_of_isOpen_setOf_isAlgEquivZero isAlgEquivZero_fibre_of_range_subset_singleton_of_twoGluedSmoothCurveDegenerations exists_isOpen_inter_preimage_eq_setOf_isAlgEquivZero_fibre_of_smoothLocus_of_twoGluedSmoothCurveDegenerations twoGluedSmoothCurveDegenerations_baseChange"
namespace HeadTransport
p2m_open "AlgebraicGeometry.RelPicard AlgebraicGeometry"

variable {R : Type u} [CommRing R] {C : Scheme.{u}} (c : C ⟶ Spec (CommRingCat.of R))
  (A : Type u) [CommRing A] [Algebra R A]

theorem exists_fibreIso_baseChange {k : Type u} [Field k] (x' : Spec (CommRingCat.of k) ⟶ Spec (CommRingCat.of A)) :
    ∃ φ : pullback (baseChange R c A) x' ≅ pullback c (x' ≫ specMap R A),
      φ.hom ≫ pullback.snd c (x' ≫ specMap R A) = pullback.snd (baseChange R c A) x' ∧
      φ.hom ≫ pullback.fst c (x' ≫ specMap R A) = pullback.fst (baseChange R c A) x' ≫ pullback.fst c (specMap R A) := by
  obtain ⟨φ, h1, h2, -⟩ := exists_fibreIso_hom_comp_eq c (specMap R A) x' (x' ≫ specMap R A) rfl
  exact ⟨φ, h1, h2⟩

theorem hgred_baseChange
    (hgred : ∀ (k : Type u) [Field k] [IsAlgClosed k]
      (x : Spec (CommRingCat.of k) ⟶ Spec (CommRingCat.of R)), IsReduced (pullback c x)) :
    ∀ (k : Type u) [Field k] [IsAlgClosed k]
      (x' : Spec (CommRingCat.of k) ⟶ Spec (CommRingCat.of A)), IsReduced (pullback (baseChange R c A) x') := by
  intro k _ _ x'
  obtain ⟨φ, -, -⟩ := exists_fibreIso_baseChange c A x'
  haveI := hgred k (x' ≫ specMap R A)
  exact isReduced_of_isOpenImmersion φ.hom

theorem exists_cutFibreIso_baseChange {k : Type u} [Field k] (x' : Spec (CommRingCat.of k) ⟶ Spec (CommRingCat.of A)) :
    ∃ φ : pullback (pullback.snd c (𝟙 (Spec (CommRingCat.of R)))) (x' ≫ specMap R A) ≅
        pullback (pullback.snd (baseChange R c A) (𝟙 (Spec (CommRingCat.of A)))) x',
      φ.hom ≫ fibreAt (baseChange R c A) (𝟙 _) x' = fibreAt c (𝟙 _) (x' ≫ specMap R A) := by

  obtain ⟨φ₁, h₁, -, -⟩ := exists_fibreIso_hom_comp_eq c (𝟙 (Spec (CommRingCat.of R))) (x' ≫ specMap R A)
    (x' ≫ specMap R A) (Category.comp_id _)
  obtain ⟨φ₂, h₂, -⟩ := exists_fibreIso_baseChange c A x'
  obtain ⟨φ₃, h₃, -, -⟩ := exists_fibreIso_hom_comp_eq (baseChange R c A) (𝟙 (Spec (CommRingCat.of A))) x' x'
    (Category.comp_id _)
  refine ⟨φ₁ ≪≫ φ₂.symm ≪≫ φ₃.symm, ?_⟩
  simp only [Iso.trans_hom, Iso.symm_hom, Category.assoc]
  rw [← h₃, Iso.inv_hom_id_assoc, ← h₂, Iso.inv_hom_id_assoc, h₁]

theorem hg_baseChange (g : ℕ)
    (hg : ∀ (k : Type u) [Field k] [IsAlgClosed k]
      (x : Spec (CommRingCat.of k) ⟶ Spec (CommRingCat.of R))
      (𝒲 : (pullback (pullback.snd c (𝟙 (Spec (CommRingCat.of R)))) x).TwoAffineOpenCover),
      Module.finrank k (𝒲.sectionsOf (fibreAt c (𝟙 _) x)
        (SheafOfModules.unit (pullback (pullback.snd c (𝟙 (Spec (CommRingCat.of R)))) x).ringCatSheaf)).H1 = g) :
    ∀ (k : Type u) [Field k] [IsAlgClosed k]
      (x' : Spec (CommRingCat.of k) ⟶ Spec (CommRingCat.of A))
      (𝒲 : (pullback (pullback.snd (baseChange R c A) (𝟙 (Spec (CommRingCat.of A)))) x').TwoAffineOpenCover),
      Module.finrank k (𝒲.sectionsOf (fibreAt (baseChange R c A) (𝟙 _) x')
        (SheafOfModules.unit (pullback (pullback.snd (baseChange R c A) (𝟙 (Spec (CommRingCat.of A)))) x').ringCatSheaf)).H1 = g := by
  intro k _ _ x' 𝒲
  obtain ⟨φ, hφ⟩ := exists_cutFibreIso_baseChange c A x'
  obtain ⟨𝒱, -, -, -, ⟨e1⟩⟩ := Scheme.TwoAffineOpenCover.exists_linearEquiv_sectionsOf_of_iso
    (fibreAt c (𝟙 _) (x' ≫ specMap R A)) (fibreAt (baseChange R c A) (𝟙 _) x') φ hφ 𝒲
    (𝟙_ _) (𝟙_ _)
    (Scheme.Modules.pullbackTensorUnitObjIso φ.hom).symm
  change Module.finrank k (𝒲.sectionsOf (fibreAt (baseChange R c A) (𝟙 _) x') (𝟙_ _)).H1 = g
  rw [← e1.finrank_eq]
  exact hg k (x' ≫ specMap R A) 𝒱

theorem h0_baseChange (n : ℕ)
    (h0 : ∀ (k : Type u) [Field k] [IsAlgClosed k]
      (x : Spec (CommRingCat.of k) ⟶ Spec (CommRingCat.of R))
      (𝒲 : (pullback (pullback.snd c (𝟙 (Spec (CommRingCat.of R)))) x).TwoAffineOpenCover),
      Module.finrank k ↥(𝒲.sectionsOf (fibreAt c (𝟙 _) x)
        (SheafOfModules.unit (pullback (pullback.snd c (𝟙 (Spec (CommRingCat.of R)))) x).ringCatSheaf)).H0 = n) :
    ∀ (k : Type u) [Field k] [IsAlgClosed k]
      (x' : Spec (CommRingCat.of k) ⟶ Spec (CommRingCat.of A))
      (𝒲 : (pullback (pullback.snd (baseChange R c A) (𝟙 (Spec (CommRingCat.of A)))) x').TwoAffineOpenCover),
      Module.finrank k ↥(𝒲.sectionsOf (fibreAt (baseChange R c A) (𝟙 _) x')
        (SheafOfModules.unit (pullback (pullback.snd (baseChange R c A) (𝟙 (Spec (CommRingCat.of A)))) x').ringCatSheaf)).H0 = n := by
  intro k _ _ x' 𝒲
  obtain ⟨φ, hφ⟩ := exists_cutFibreIso_baseChange c A x'
  obtain ⟨𝒱, -, -, ⟨e0⟩, -⟩ := Scheme.TwoAffineOpenCover.exists_linearEquiv_sectionsOf_of_iso
    (fibreAt c (𝟙 _) (x' ≫ specMap R A)) (fibreAt (baseChange R c A) (𝟙 _) x') φ hφ 𝒲
    (𝟙_ _) (𝟙_ _)
    (Scheme.Modules.pullbackTensorUnitObjIso φ.hom).symm
  change Module.finrank k ↥(𝒲.sectionsOf (fibreAt (baseChange R c A) (𝟙 _) x') (𝟙_ _)).H0 = n
  rw [← e0.finrank_eq]
  exact h0 k (x' ≫ specMap R A) 𝒱

theorem smooth_U_baseChange (U : C.Opens) [SmoothOfRelativeDimension 1 (U.ι ≫ c)] :
    SmoothOfRelativeDimension 1 ((pullback.fst c (specMap R A) ⁻¹ᵁ U).ι ≫ baseChange R c A) := by

  have hsq : IsPullback ((pullback.fst c (specMap R A)) ∣_ U) (pullback.fst c (specMap R A) ⁻¹ᵁ U).ι U.ι
      (pullback.fst c (specMap R A)) := isPullback_morphismRestrict _ _
  have hbig : IsPullback ((pullback.fst c (specMap R A)) ∣_ U)
      ((pullback.fst c (specMap R A) ⁻¹ᵁ U).ι ≫ baseChange R c A) (U.ι ≫ c) (specMap R A) :=
    hsq.paste_vert (IsPullback.of_hasPullback c (specMap R A))
  exact (smoothOfRelativeDimension_isStableUnderBaseChange (n := 1)).of_isPullback hbig inferInstance

theorem hεU_baseChange (U : C.Opens) (ε : SchemeHomOver (𝟙 (Spec (CommRingCat.of R))) c)
    (hεU : Set.range ε.1 ⊆ (U : Set C)) :
    Set.range (sectionBaseChange A ε).1 ⊆ ((pullback.fst c (specMap R A) ⁻¹ᵁ U : (pullback c (specMap R A)).Opens) :
      Set ↥(pullback c (specMap R A))) := by
  rintro _ ⟨z, rfl⟩
  show (pullback.fst c (specMap R A)) ((sectionBaseChange A ε).1 z) ∈ U
  rw [← Scheme.Hom.comp_apply, sectionBaseChange_coe_fst, Scheme.Hom.comp_apply]
  exact hεU ⟨_, rfl⟩

theorem hH0_baseChange
    (hH0 : ∀ (A' : Type u) [CommRing A'] [Algebra R A'],
      letI := Scheme.TwoAffineOpenCover.algebraOfHom
        (Limits.pullback.snd c (Scheme.TwoAffineOpenCover.specMap R A')) ⊤
      Function.Bijective (algebraMap A' Γ(Limits.pullback c (Scheme.TwoAffineOpenCover.specMap R A'), ⊤))) :
    ∀ (A' : Type u) [CommRing A'] [Algebra A A'],
      letI := Scheme.TwoAffineOpenCover.algebraOfHom
        (Limits.pullback.snd (baseChange R c A) (Scheme.TwoAffineOpenCover.specMap A A')) ⊤
      Function.Bijective (algebraMap A' Γ(Limits.pullback (baseChange R c A) (Scheme.TwoAffineOpenCover.specMap A A'), ⊤)) := by
  intro A' _ _

  letI algRA' : Algebra R A' := ((algebraMap A A').comp (algebraMap R A)).toAlgebra
  have hspec : Scheme.TwoAffineOpenCover.specMap A A' ≫ specMap R A = Scheme.TwoAffineOpenCover.specMap R A' := by
    show Spec.map (CommRingCat.ofHom (algebraMap A A')) ≫ Spec.map (CommRingCat.ofHom (algebraMap R A)) =
      Spec.map (CommRingCat.ofHom (algebraMap R A'))
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]

  let ψ : Limits.pullback (baseChange R c A) (Scheme.TwoAffineOpenCover.specMap A A') ≅
      Limits.pullback c (Scheme.TwoAffineOpenCover.specMap R A') :=
    pullbackLeftPullbackSndIso c (specMap R A) (Scheme.TwoAffineOpenCover.specMap A A') ≪≫ pullback.congrHom rfl hspec
  have hψ : ψ.hom ≫ Limits.pullback.snd c (Scheme.TwoAffineOpenCover.specMap R A') =
      Limits.pullback.snd (baseChange R c A) (Scheme.TwoAffineOpenCover.specMap A A') := by
    simp only [ψ, Iso.trans_hom, Category.assoc, pullback.congrHom_hom, pullback.lift_snd, Category.comp_id]
    exact pullbackLeftPullbackSndIso_hom_snd _ _ _

  letI i1 := Scheme.TwoAffineOpenCover.algebraOfHom
    (Limits.pullback.snd c (Scheme.TwoAffineOpenCover.specMap R A')) ⊤
  letI i2 := Scheme.TwoAffineOpenCover.algebraOfHom
    (Limits.pullback.snd (baseChange R c A) (Scheme.TwoAffineOpenCover.specMap A A')) ⊤
  have eTop : ∀ {X Y : Scheme.{u}} (f : X ⟶ Y), f.appLE ⊤ ⊤ le_top = f.appTop := fun f =>
    (Scheme.Hom.app_eq_appLE f).symm
  have key : ∀ a : A', i2.algebraMap a = (ψ.hom.appTop).hom (i1.algebraMap a) := by
    intro a
    rw [Scheme.TwoAffineOpenCover.algebraMap_algebraOfHom, Scheme.TwoAffineOpenCover.algebraMap_algebraOfHom, eTop, eTop,
      ← hψ, Scheme.Hom.comp_appTop]
    rfl
  haveI : IsIso ψ.hom.appTop := (inferInstance : IsIso (ψ.hom.app ⊤))
  have hiso : Function.Bijective (ψ.hom.appTop).hom := ConcreteCategory.bijective_of_isIso ψ.hom.appTop
  show Function.Bijective i2.algebraMap
  have : (i2.algebraMap : A' → _) = (ψ.hom.appTop).hom ∘ i1.algebraMap := funext key
  rw [this]
  exact hiso.comp (hH0 A')

theorem isAlgEquivZero_of_iso {k : Type u} [Field k] {A₁ A₂ : Scheme.{u}}
    (a₁ : A₁ ⟶ Spec (CommRingCat.of k)) (a₂ : A₂ ⟶ Spec (CommRingCat.of k)) (ψ : A₁ ≅ A₂) (hψ : ψ.hom ≫ a₂ = a₁)
    (L : A₂.Modules) (hL : IsAlgEquivZero a₂ L) :
    IsAlgEquivZero a₁ ((Scheme.Modules.pullback ψ.hom).obj L) := by
  obtain ⟨T', h, hlft, hgi, M, hM, t₀, t₁, ⟨e₀⟩, ⟨e₁⟩⟩ := hL

  let Ψ : pullback a₁ h ⟶ pullback a₂ h :=
    pullback.map a₁ h a₂ h ψ.hom (𝟙 T') (𝟙 _) (by rw [Category.comp_id, hψ]) (by simp)
  let Ψ₀ : pullback a₁ (𝟙 (Spec (CommRingCat.of k))) ⟶ pullback a₂ (𝟙 (Spec (CommRingCat.of k))) :=
    pullback.map a₁ (𝟙 _) a₂ (𝟙 _) ψ.hom (𝟙 _) (𝟙 _) (by rw [Category.comp_id, hψ]) (by simp)
  have hcomm : ∀ t : SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) h,
      baseChangeSnd a₁ t ≫ Ψ = Ψ₀ ≫ baseChangeSnd a₂ t := by
    intro t
    apply pullback.hom_ext <;>
      simp only [Ψ, Ψ₀, baseChangeSnd, Category.assoc, pullback.lift_fst, pullback.lift_snd, pullback.lift_fst_assoc,
        pullback.lift_snd_assoc, Category.comp_id, Category.id_comp]
  have hfst : Ψ₀ ≫ pullback.fst a₂ (𝟙 _) = pullback.fst a₁ (𝟙 _) ≫ ψ.hom := by
    simp only [Ψ₀, pullback.lift_fst]
  refine ⟨T', h, hlft, hgi, (Scheme.Modules.pullback Ψ).obj M, hM.pullback Ψ, t₀, t₁, ⟨?_⟩, ⟨?_⟩⟩
  ·
    exact (Scheme.Modules.pullbackComp (baseChangeSnd a₁ t₀) Ψ).app M ≪≫
      (Scheme.Modules.pullbackCongr (hcomm t₀)).app M ≪≫
      ((Scheme.Modules.pullbackComp Ψ₀ (baseChangeSnd a₂ t₀)).app M).symm ≪≫
      (Scheme.Modules.pullback Ψ₀).mapIso e₀ ≪≫ Scheme.Modules.pullbackTensorUnitObjIso Ψ₀
  ·
    exact (Scheme.Modules.pullbackComp (baseChangeSnd a₁ t₁) Ψ).app M ≪≫
      (Scheme.Modules.pullbackCongr (hcomm t₁)).app M ≪≫
      ((Scheme.Modules.pullbackComp Ψ₀ (baseChangeSnd a₂ t₁)).app M).symm ≪≫
      (Scheme.Modules.pullback Ψ₀).mapIso e₁ ≪≫
      (Scheme.Modules.pullbackComp Ψ₀ (pullback.fst a₂ (𝟙 _))).app L ≪≫
      (Scheme.Modules.pullbackCongr hfst).app L ≪≫
      ((Scheme.Modules.pullbackComp (pullback.fst a₁ (𝟙 _)) ψ.hom).app L).symm

theorem hfib_baseChange
    (hfib : ∀ (k : Type u) [Field k] [IsAlgClosed k]
      (x : Spec (CommRingCat.of k) ⟶ Spec (CommRingCat.of R))
      (L : (pullback c x).Modules), Scheme.Modules.IsInvertible L →
      IsAlgEquivZero (pullback.snd c x) L →
      ∀ s : 𝟙_ (pullback c x).Modules ⟶ L, s ≠ 0 → Nonempty (L ≅ 𝟙_ (pullback c x).Modules)) :
    ∀ (k : Type u) [Field k] [IsAlgClosed k]
      (x' : Spec (CommRingCat.of k) ⟶ Spec (CommRingCat.of A))
      (L : (pullback (baseChange R c A) x').Modules), Scheme.Modules.IsInvertible L →
      IsAlgEquivZero (pullback.snd (baseChange R c A) x') L →
      ∀ s : 𝟙_ (pullback (baseChange R c A) x').Modules ⟶ L, s ≠ 0 →
        Nonempty (L ≅ 𝟙_ (pullback (baseChange R c A) x').Modules) := by
  intro k _ _ x' L hL hAE s hs
  obtain ⟨φ, hφ, -⟩ := exists_fibreIso_baseChange c A x'

  let L₀ : (pullback c (x' ≫ specMap R A)).Modules := (Scheme.Modules.pullback φ.inv).obj L
  have hL₀ : Scheme.Modules.IsInvertible L₀ := hL.pullback φ.inv
  have hφ' : φ.inv ≫ pullback.snd (baseChange R c A) x' = pullback.snd c (x' ≫ specMap R A) := by
    rw [← hφ, Iso.inv_hom_id_assoc]
  have hAE₀ : IsAlgEquivZero (pullback.snd c (x' ≫ specMap R A)) L₀ :=
    isAlgEquivZero_of_iso _ _ φ.symm hφ' L hAE

  let u : 𝟙_ _ ≅ (Scheme.Modules.pullback φ.inv).obj (𝟙_ (pullback (baseChange R c A) x').Modules) :=
    (Scheme.Modules.pullbackTensorUnitObjIso φ.inv).symm
  let s₀ : 𝟙_ _ ⟶ L₀ := u.hom ≫ (Scheme.Modules.pullback φ.inv).map s
  have hs₀ : s₀ ≠ 0 := by
    intro h0
    apply hs
    have h1 : (Scheme.Modules.pullback φ.inv).map s = 0 := by
      rw [← Category.id_comp ((Scheme.Modules.pullback φ.inv).map s), ← u.inv_hom_id, Category.assoc]
      change u.inv ≫ s₀ = 0
      rw [h0, Limits.comp_zero]

    have e : (Scheme.Modules.pullback φ.inv ⋙ Scheme.Modules.pullback φ.hom) ≅ 𝟭 _ :=
      Scheme.Modules.pullbackComp φ.hom φ.inv ≪≫ Scheme.Modules.pullbackCongr φ.hom_inv_id ≪≫ Scheme.Modules.pullbackId _
    haveI : (Scheme.Modules.pullback φ.inv).Faithful := Functor.Faithful.of_comp_iso e
    exact (Scheme.Modules.pullback φ.inv).map_injective (h1.trans ((Scheme.Modules.pullback φ.inv).map_zero _ _).symm)
  obtain ⟨e₀⟩ := hfib k (x' ≫ specMap R A) L₀ hL₀ hAE₀ s₀ hs₀

  refine ⟨?_⟩
  exact ((Scheme.Modules.pullbackId _).app L).symm ≪≫ (Scheme.Modules.pullbackCongr φ.hom_inv_id.symm).app L ≪≫
    ((Scheme.Modules.pullbackComp φ.hom φ.inv).app L).symm ≪≫
    (Scheme.Modules.pullback φ.hom).mapIso e₀ ≪≫ Scheme.Modules.pullbackTensorUnitObjIso φ.hom

theorem hcov_baseChange (U : C.Opens)
    (hcov : ∀ (V : (Spec (CommRingCat.of R)).affineOpens) (F : Finset ↥U),
      (∀ x ∈ F, (U.ι ≫ c).base x ∈ (V : (Spec (CommRingCat.of R)).Opens)) →
      ∃ W : (U : Scheme.{u}).Opens, IsAffineOpen W ∧
        W ≤ (U.ι ≫ c) ⁻¹ᵁ (V : (Spec (CommRingCat.of R)).Opens) ∧ ∀ x ∈ F, x ∈ W) :
    ∀ (V : (Spec (CommRingCat.of A)).affineOpens) (F : Finset ↥(pullback.fst c (specMap R A) ⁻¹ᵁ U)),
      (∀ x ∈ F, ((pullback.fst c (specMap R A) ⁻¹ᵁ U).ι ≫ baseChange R c A).base x ∈
        (V : (Spec (CommRingCat.of A)).Opens)) →
      ∃ W : ((pullback.fst c (specMap R A) ⁻¹ᵁ U : (pullback c (specMap R A)).Opens) : Scheme.{u}).Opens,
        IsAffineOpen W ∧
          W ≤ ((pullback.fst c (specMap R A) ⁻¹ᵁ U).ι ≫ baseChange R c A) ⁻¹ᵁ
            (V : (Spec (CommRingCat.of A)).Opens) ∧ ∀ x ∈ F, x ∈ W := by
  classical
  intro V F hF

  let g : ((pullback.fst c (specMap R A) ⁻¹ᵁ U) : Scheme.{u}) ⟶ (U : Scheme.{u}) := (pullback.fst c (specMap R A)) ∣_ U
  have hsq : IsPullback g (pullback.fst c (specMap R A) ⁻¹ᵁ U).ι U.ι (pullback.fst c (specMap R A)) := isPullback_morphismRestrict _ _
  have hbig : IsPullback g ((pullback.fst c (specMap R A) ⁻¹ᵁ U).ι ≫ baseChange R c A) (U.ι ≫ c) (specMap R A) :=
    hsq.paste_vert (IsPullback.of_hasPullback c (specMap R A))
  haveI : IsAffineHom g :=
    MorphismProperty.of_isPullback (P := @IsAffineHom) hbig.flip inferInstance

  obtain ⟨W, hWaff, -, hFW⟩ := hcov ⟨⊤, isAffineOpen_top _⟩ (F.image fun x => g.base x)
    (fun _ _ => trivial)

  let W₁ : ((pullback.fst c (specMap R A) ⁻¹ᵁ U) : Scheme.{u}).Opens := g ⁻¹ᵁ W
  have hW₁aff : IsAffineOpen W₁ := hWaff.preimage g
  have hFW₁ : ∀ x ∈ F, x ∈ W₁ := fun x hx => hFW _ (Finset.mem_image_of_mem _ hx)

  haveI : IsAffine (W₁ : Scheme.{u}) := hW₁aff
  let q : (W₁ : Scheme.{u}) ⟶ Spec (CommRingCat.of A) := W₁.ι ≫ (pullback.fst c (specMap R A) ⁻¹ᵁ U).ι ≫ baseChange R c A
  have hW₂aff' : IsAffineOpen (q ⁻¹ᵁ (V : (Spec (CommRingCat.of A)).Opens)) := V.2.preimage q
  refine ⟨W₁.ι ''ᵁ (q ⁻¹ᵁ (V : (Spec (CommRingCat.of A)).Opens)), hW₂aff'.image_of_isOpenImmersion _, ?_, ?_⟩
  ·
    rintro x ⟨y, hy, rfl⟩
    show (((pullback.fst c (specMap R A) ⁻¹ᵁ U).ι ≫ baseChange R c A).base (W₁.ι.base y)) ∈ (V : (Spec (CommRingCat.of A)).Opens)
    rw [← Scheme.Hom.comp_apply]
    exact hy
  ·
    intro x hx
    refine ⟨⟨x, hFW₁ x hx⟩, ?_, rfl⟩
    show (q.base ⟨x, hFW₁ x hx⟩) ∈ (V : (Spec (CommRingCat.of A)).Opens)
    have : q.base ⟨x, hFW₁ x hx⟩ = ((pullback.fst c (specMap R A) ⁻¹ᵁ U).ι ≫ baseChange R c A).base x := by
      simp only [q, Scheme.Hom.comp_base, TopCat.coe_comp, Function.comp_apply]
      rfl
    rw [this]
    exact hF x hx

noncomputable def twoAffineOpenCoverOfIso {X Y : Scheme.{u}} (φ : X ≅ Y) (𝒲 : Y.TwoAffineOpenCover) :
    X.TwoAffineOpenCover :=
  { U0 := φ.hom ⁻¹ᵁ 𝒲.U0
    U1 := φ.hom ⁻¹ᵁ 𝒲.U1
    isAffineOpen_U0 := 𝒲.isAffineOpen_U0.preimage_of_isIso φ.hom
    isAffineOpen_U1 := 𝒲.isAffineOpen_U1.preimage_of_isIso φ.hom
    sup_eq_top := by rw [← Scheme.Hom.preimage_sup, 𝒲.sup_eq_top]; rfl
    isAffineOpen_inf := by rw [← Scheme.Hom.preimage_inf]; exact 𝒲.isAffineOpen_inf.preimage_of_isIso φ.hom }

theorem hgoodU_of_hUmax [Flat c] [LocallyOfFinitePresentation c] (U : C.Opens)
    (hUmax : ∀ W : C.Opens, SmoothOfRelativeDimension 1 (W.ι ≫ c) → W ≤ U)
    {k : Type u} [Field k] (x : Spec (CommRingCat.of k) ⟶ Spec (CommRingCat.of R))
    (hsm : SmoothOfRelativeDimension 1 (pullback.snd c x)) :
    Set.range (pullback.fst c x).base ⊆ (U : Set C) := by
  intro y hy
  obtain ⟨W, hyW, hW⟩ := exists_mem_and_smoothOfRelativeDimension_one_of_smoothOfRelativeDimension_pullback_snd c x hsm y hy
  exact hUmax W hW hyW

theorem hgoodU_baseChange (U : C.Opens)
    (hgoodU : ∀ (k : Type u) [Field k] [IsAlgClosed k] (x : Spec (CommRingCat.of k) ⟶ Spec (CommRingCat.of R)),
      Smooth (pullback.snd c x) → Set.range (pullback.fst c x).base ⊆ (U : Set C)) :
    ∀ (k : Type u) [Field k] [IsAlgClosed k] (x' : Spec (CommRingCat.of k) ⟶ Spec (CommRingCat.of A)),
      Smooth (pullback.snd (baseChange R c A) x') →
      Set.range (pullback.fst (baseChange R c A) x').base ⊆
        ((pullback.fst c (specMap R A) ⁻¹ᵁ U : (pullback c (specMap R A)).Opens) : Set ↥(pullback c (specMap R A))) := by
  intro k _ _ x' hsm
  obtain ⟨φ, hφ, hφ'⟩ := exists_fibreIso_baseChange c A x'

  have hsm' : Smooth (pullback.snd c (x' ≫ specMap R A)) := by
    have : φ.inv ≫ pullback.snd (baseChange R c A) x' = pullback.snd c (x' ≫ specMap R A) := by
      rw [← hφ, Iso.inv_hom_id_assoc]
    rw [← this]; infer_instance
  rintro _ ⟨z, rfl⟩
  show (pullback.fst c (specMap R A)).base ((pullback.fst (baseChange R c A) x').base z) ∈ U
  have h := hgoodU k (x' ≫ specMap R A) hsm' ⟨φ.hom.base z, rfl⟩
  rw [← Scheme.Hom.comp_apply, ← hφ', Scheme.Hom.comp_apply]
  exact h

theorem geometricallyIrreducible_snd_of_smooth_of_hH0
    (hH0 : ∀ (A' : Type u) [CommRing A'] [Algebra R A'],
      letI := Scheme.TwoAffineOpenCover.algebraOfHom
        (Limits.pullback.snd c (Scheme.TwoAffineOpenCover.specMap R A')) ⊤
      Function.Bijective (algebraMap A' Γ(Limits.pullback c (Scheme.TwoAffineOpenCover.specMap R A'), ⊤)))
    {k : Type u} [Field k] (x : Spec (CommRingCat.of k) ⟶ Spec (CommRingCat.of R)) [Smooth (pullback.snd c x)] :
    GeometricallyIrreducible (pullback.snd c x) := by

  letI : Algebra R k := (Spec.preimage x).hom.toAlgebra
  have hx : specMap R k = x := by
    show Spec.map (CommRingCat.ofHom (algebraMap R k)) = x
    conv_rhs => rw [← Spec.map_preimage x]
    rfl

  let e : pullback c x ≅ pullback c (specMap R k) := pullback.congrHom rfl hx.symm
  have hhom : e.hom ≫ pullback.snd c (specMap R k) = pullback.snd c x := by
    simp only [e, pullback.congrHom, asIso_hom, pullback.map, pullback.lift_snd, Category.comp_id]
  have hinv : e.inv ≫ pullback.snd c x = pullback.snd c (specMap R k) := by
    rw [← hhom, Iso.inv_hom_id_assoc]

  haveI : Smooth (baseChange R c k) := by
    show Smooth (pullback.snd c (specMap R k))
    rw [← hinv]
    infer_instance
  haveI : GeometricallyIntegral (baseChange R c k) :=
    AlgebraicGeometry.geometricallyIntegral_of_bijective_algebraMap_sections_of_smooth (baseChange R c k)
      (hH0_baseChange c k hH0)
  haveI : GeometricallyIrreducible (pullback.snd c (specMap R k)) :=
    show GeometricallyIrreducible (baseChange R c k) from inferInstance
  rw [← hhom]
  infer_instance

theorem range_fst_subset_of_smooth_of_hUmax [IsNoetherianRing R] [IsProper c] [Flat c]
    (U : C.Opens) [SmoothOfRelativeDimension 1 (U.ι ≫ c)]
    (hUmax : ∀ W : C.Opens, SmoothOfRelativeDimension 1 (W.ι ≫ c) → W ≤ U)
    (hH0 : ∀ (A' : Type u) [CommRing A'] [Algebra R A'],
      letI := Scheme.TwoAffineOpenCover.algebraOfHom
        (Limits.pullback.snd c (Scheme.TwoAffineOpenCover.specMap R A')) ⊤
      Function.Bijective (algebraMap A' Γ(Limits.pullback c (Scheme.TwoAffineOpenCover.specMap R A'), ⊤)))
    (ε : SchemeHomOver (𝟙 (Spec (CommRingCat.of R))) c) (hε : Set.range ε.1.base ⊆ (U : Set C)) :
    ∀ (k : Type u) [Field k] [IsAlgClosed k] (x : Spec (CommRingCat.of k) ⟶ Spec (CommRingCat.of R)),
      Smooth (pullback.snd c x) → Set.range (pullback.fst c x).base ⊆ (U : Set C) := by
  intro k _ _ x hsm
  haveI := hsm
  haveI : LocallyOfFinitePresentation c := locallyOfFinitePresentation_of_isNoetherianRing c

  haveI : GeometricallyIrreducible (pullback.snd c x) := geometricallyIrreducible_snd_of_smooth_of_hH0 c hH0 x
  haveI : IrreducibleSpace ↥(pullback c x) :=
    GeometricallyIrreducible.irreducibleSpace_of_subsingleton (f := pullback.snd c x)

  let V : (pullback c x).Opens := pullback.fst c x ⁻¹ᵁ U
  have hVne : (V : Set ↥(pullback c x)).Nonempty := by
    refine ⟨((sectionFibrePoint ε x).1).base (IsLocalRing.closedPoint k), ?_⟩
    show (pullback.fst c x).base (((sectionFibrePoint ε x).1).base (IsLocalRing.closedPoint k)) ∈ U
    rw [← Scheme.Hom.comp_apply]
    have : (sectionFibrePoint ε x).1 ≫ pullback.fst c x = x ≫ ε.1 := pullback.lift_fst _ _ _
    rw [this, Scheme.Hom.comp_apply]
    exact hε ⟨_, rfl⟩
  haveI : SmoothOfRelativeDimension 1 (V.ι ≫ pullback.snd c x) := by
    have hsq : IsPullback ((pullback.fst c x) ∣_ U) V.ι U.ι (pullback.fst c x) := isPullback_morphismRestrict _ _
    have hbig : IsPullback ((pullback.fst c x) ∣_ U) (V.ι ≫ pullback.snd c x) (U.ι ≫ c) x :=
      hsq.paste_vert (IsPullback.of_hasPullback c x)
    exact (smoothOfRelativeDimension_isStableUnderBaseChange (n := 1)).of_isPullback hbig inferInstance
  have hdim : SmoothOfRelativeDimension 1 (pullback.snd c x) :=
    AlgebraicGeometry.smoothOfRelativeDimension_of_irreducibleSpace 1 (pullback.snd c x) V hVne

  rintro _ ⟨y', rfl⟩
  obtain ⟨W, hyW, hW⟩ :=
    AlgebraicGeometry.exists_mem_and_smoothOfRelativeDimension_one_of_smoothOfRelativeDimension_pullback_snd c x hdim
      ((pullback.fst c x).base y') ⟨y', rfl⟩
  exact hUmax W hW hyW

end AlgebraicGeometry.RelPicard.HeadTransport

namespace AlgebraicGeometry
p2m_export "AlgebraicGeometry" "Spec.map_comp Spec.map_preimage Scheme.Hom.preimage_smoothLocus_eq SmoothOfRelativeDimension IsProper Scheme.Modules.pullback Scheme.Hom GeometricallyIntegral Scheme.Hom.smoothLocus_eq_top_iff Scheme.Hom.preimage_inf GeometricallyIrreducible Scheme.Pullback.range_fst IsAffine isPullback_morphismRestrict Scheme.topIso Scheme.homeoOfIso LocallyOfFiniteType Spec IsIntegral Spec.map Scheme Smooth IsOpenImmersion Scheme.Hom.comp_base Scheme.Hom.comp_appTop Flat IsClosedImmersion IsReduced smoothOfRelativeDimension_isStableUnderBaseChange Scheme.Hom.smoothLocus_eq_top Spec.preimage Scheme.Modules.pullbackCongr HasRingHomProperty.iff_of_source_openCover isAffineOpen_top GeometricallyIrreducible.irreducibleSpace_of_subsingleton Scheme.Modules.pullbackId IsAffineOpen Scheme.Hom.preimage_sup Scheme.Modules Scheme.Opens Scheme.Hom.app_eq_appLE LocallyOfFinitePresentation IsAffineHom isReduced_of_isOpenImmersion HasRingHomProperty Scheme.Opens.ι_preimage_self Scheme.Hom.comp_apply geometrically Scheme.Modules.pullbackComp Scheme.ΓSpecIso isIntegral_of_irreducibleSpace_of_isReduced Scheme.Modules.IsInvertible Scheme.Modules.isInvertible_unit AffineLimit.IsLFPSurj Scheme.TwoAffineOpenCover Scheme.TwoAffineOpenCover.specMap Scheme.TwoAffineOpenCover.algebraOfHom Scheme.TwoAffineOpenCover.algebraMap_algebraOfHom Scheme.Modules.pullbackTensorUnitObjIso Scheme.TwoAffineOpenCover.exists_linearEquiv_sectionsOf_of_iso geometricallyIntegral_of_bijective_algebraMap_sections_of_smooth smoothOfRelativeDimension_of_irreducibleSpace exists_mem_and_smoothOfRelativeDimension_one_of_smoothOfRelativeDimension_pullback_snd"
namespace RelPicard
p2m_export "AlgebraicGeometry.RelPicard" "baseChangeSnd RigidifiedLineBundle fibreAt IsAlgEquivZero algEquivZeroCut relSubPicPresheaf fibreModule sectionFibrePoint exists_fibreIso_hom_comp_eq IsAlgEquivZero.eulerChar_sectionsOf_tensor_eq isAlgEquivZero_iff_eulerChar_sectionsOf_eq isOpen_setOf_isAlgEquivZero_fibre_of_twoStrata isLFPSurj_relSubPicPresheaf_algEquivZeroCut_of_isOpen_setOf_isAlgEquivZero isAlgEquivZero_fibre_of_range_subset_singleton_of_twoGluedSmoothCurveDegenerations exists_isOpen_inter_preimage_eq_setOf_isAlgEquivZero_fibre_of_smoothLocus_of_twoGluedSmoothCurveDegenerations twoGluedSmoothCurveDegenerations_baseChange"
namespace HeadCut
p2m_open "AlgebraicGeometry.RelPicard AlgebraicGeometry"

theorem cover_ext {X : Scheme.{u}} {𝒱 𝒱' : X.TwoAffineOpenCover}
    (h0 : 𝒱.U0 = 𝒱'.U0) (h1 : 𝒱.U1 = 𝒱'.U1) : 𝒱 = 𝒱' := by
  cases 𝒱; cases 𝒱'; cases h0; cases h1; rfl

theorem eulerChar_congr {k : Type u} [Field k] {X : Scheme.{u}} (x : X ⟶ Spec (CommRingCat.of k))
    (𝒱 : X.TwoAffineOpenCover) {M M' : X.Modules} (e : M ≅ M') :
    (Module.finrank k (𝒱.sectionsOf x M).H0 : ℤ) - Module.finrank k (𝒱.sectionsOf x M).H1 =
      (Module.finrank k (𝒱.sectionsOf x M').H0 : ℤ) - Module.finrank k (𝒱.sectionsOf x M').H1 := by
  obtain ⟨𝒱₂, h0, h1, ⟨e0⟩, ⟨e1⟩⟩ :=
    Scheme.TwoAffineOpenCover.exists_linearEquiv_sectionsOf_of_iso x x (Iso.refl X) (Category.id_comp x)
      𝒱 M' M (e ≪≫ ((Scheme.Modules.pullbackId X).app M').symm)
  obtain rfl : 𝒱₂ = 𝒱 := cover_ext h0 h1
  rw [e0.finrank_eq, e1.finrank_eq]

variable {R : Type u} [CommRing R] {C : Scheme.{u}} (c : C ⟶ Spec (CommRingCat.of R)) [IsProper c]
  (ε : SchemeHomOver (𝟙 (Spec (CommRingCat.of R))) c)

theorem eulerChar_fibre_eq_of_isAlgEquivZero
    {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) [LocallyOfFiniteType t]
    (L : RigidifiedLineBundle c ε t) (k : Type u) [Field k] [IsAlgClosed k] (s : Spec (CommRingCat.of k) ⟶ T)
    (h : IsAlgEquivZero (fibreAt c t s) (fibreModule c t s L.L)) :
    ∀ 𝒲 : (pullback (pullback.snd c t) s).TwoAffineOpenCover,
      (Module.finrank k (𝒲.sectionsOf (fibreAt c t s) (fibreModule c t s L.L)).H0 : ℤ) -
          Module.finrank k (𝒲.sectionsOf (fibreAt c t s) (fibreModule c t s L.L)).H1 =
        (Module.finrank k (𝒲.sectionsOf (fibreAt c t s) (fibreModule c t s (𝟙_ (pullback c t).Modules))).H0 : ℤ) -
          Module.finrank k (𝒲.sectionsOf (fibreAt c t s) (fibreModule c t s (𝟙_ (pullback c t).Modules))).H1 := by
  intro 𝒲
  haveI : IsProper (fibreAt c t s) := by unfold fibreAt; infer_instance
  have hL : Scheme.Modules.IsInvertible (fibreModule c t s L.L) := L.isInvertible.pullback _

  have key := IsAlgEquivZero.eulerChar_sectionsOf_tensor_eq (fibreAt c t s) 𝒲 (fibreModule c t s L.L) (𝟙_ _)
    hL (Scheme.Modules.isInvertible_unit _) h
  rw [eulerChar_congr (fibreAt c t s) 𝒲 (ρ_ (fibreModule c t s L.L))] at key
  rw [key]

  exact eulerChar_congr (fibreAt c t s) 𝒲 (Scheme.Modules.pullbackTensorUnitObjIso _).symm

section BadLocus

variable {R : Type u} [CommRing R] {C : Scheme.{u}} (c : C ⟶ Spec (CommRingCat.of R))
  [IsProper c] [LocallyOfFinitePresentation c]

def badLocus : Set ↥(Spec (CommRingCat.of R)) := ⇑c '' ((c.smoothLocus : Set C)ᶜ)

theorem isClosed_badLocus : IsClosed (badLocus c) :=
  c.isClosedMap _ c.smoothLocus.isOpen.isClosed_compl

theorem smooth_smoothLocus_ι_comp : Smooth (c.smoothLocus.ι ≫ c) := by
  rw [← Scheme.Hom.smoothLocus_eq_top_iff, ← Scheme.Hom.preimage_smoothLocus_eq]
  exact Scheme.Opens.ι_preimage_self _

theorem smooth_snd_of_not_mem_badLocus {k : Type u} [Field k]
    (s : Spec (CommRingCat.of k) ⟶ Spec (CommRingCat.of R)) (hs : s.base (IsLocalRing.closedPoint k) ∉ badLocus c) :
    Smooth (pullback.snd c s) := by

  have hV : (pullback.fst c s ⁻¹ᵁ c.smoothLocus) = ⊤ := by
    rw [← top_le_iff]
    intro p _
    by_contra hp
    apply hs
    refine ⟨(pullback.fst c s).base p, hp, ?_⟩
    have : (pullback.fst c s).base p ∈ Set.range (pullback.fst c s).base := ⟨p, rfl⟩
    rw [Scheme.Pullback.range_fst] at this
    obtain ⟨q, hq⟩ := this
    rw [Subsingleton.elim q (IsLocalRing.closedPoint k)] at hq
    exact hq.symm

  have hsm : Smooth ((pullback.fst c s ⁻¹ᵁ c.smoothLocus).ι ≫ pullback.snd c s) := by
    have hsq : IsPullback ((pullback.fst c s) ∣_ c.smoothLocus) (pullback.fst c s ⁻¹ᵁ c.smoothLocus).ι c.smoothLocus.ι
        (pullback.fst c s) := isPullback_morphismRestrict _ _
    have hbig : IsPullback ((pullback.fst c s) ∣_ c.smoothLocus) ((pullback.fst c s ⁻¹ᵁ c.smoothLocus).ι ≫ pullback.snd c s)
        (c.smoothLocus.ι ≫ c) s := hsq.paste_vert (IsPullback.of_hasPullback c s)
    exact MorphismProperty.IsStableUnderBaseChange.of_isPullback hbig (smooth_smoothLocus_ι_comp c)
  rw [hV] at hsm
  have := MorphismProperty.RespectsIso.precomp (P := @Smooth) (Scheme.topIso (pullback c s)).inv
    ((⊤ : (pullback c s).Opens).ι ≫ pullback.snd c s) hsm
  simpa using this

variable [Flat c]

theorem smoothOfRelativeDimension_one_snd_of_smooth [IsNoetherianRing R]
    (hH0 : ∀ (A' : Type u) [CommRing A'] [Algebra R A'],
      letI := Scheme.TwoAffineOpenCover.algebraOfHom
        (Limits.pullback.snd c (Scheme.TwoAffineOpenCover.specMap R A')) ⊤
      Function.Bijective (algebraMap A' Γ(Limits.pullback c (Scheme.TwoAffineOpenCover.specMap R A'), ⊤)))
    (U : C.Opens) [SmoothOfRelativeDimension 1 (U.ι ≫ c)]
    (ε : SchemeHomOver (𝟙 (Spec (CommRingCat.of R))) c) (hε : Set.range ε.1.base ⊆ (U : Set C))
    {k : Type u} [Field k] [IsAlgClosed k]
    (s : Spec (CommRingCat.of k) ⟶ Spec (CommRingCat.of R)) [Smooth (pullback.snd c s)] :
    SmoothOfRelativeDimension 1 (pullback.snd c s) := by
  haveI : GeometricallyIrreducible (pullback.snd c s) :=
    AlgebraicGeometry.RelPicard.HeadTransport.geometricallyIrreducible_snd_of_smooth_of_hH0 c hH0 s
  haveI : IrreducibleSpace ↥(pullback c s) :=
    GeometricallyIrreducible.irreducibleSpace_of_subsingleton (f := pullback.snd c s)
  let V : (pullback c s).Opens := pullback.fst c s ⁻¹ᵁ U
  have hVne : (V : Set ↥(pullback c s)).Nonempty := by
    refine ⟨((sectionFibrePoint ε s).1).base (IsLocalRing.closedPoint k), ?_⟩
    show (pullback.fst c s).base (((sectionFibrePoint ε s).1).base (IsLocalRing.closedPoint k)) ∈ U
    rw [← Scheme.Hom.comp_apply]
    have : (sectionFibrePoint ε s).1 ≫ pullback.fst c s = s ≫ ε.1 := pullback.lift_fst _ _ _
    rw [this, Scheme.Hom.comp_apply]
    exact hε ⟨_, rfl⟩
  haveI : SmoothOfRelativeDimension 1 (V.ι ≫ pullback.snd c s) := by
    have hsq : IsPullback ((pullback.fst c s) ∣_ U) V.ι U.ι (pullback.fst c s) := isPullback_morphismRestrict _ _
    have hbig : IsPullback ((pullback.fst c s) ∣_ U) (V.ι ≫ pullback.snd c s) (U.ι ≫ c) s :=
      hsq.paste_vert (IsPullback.of_hasPullback c s)
    exact (smoothOfRelativeDimension_isStableUnderBaseChange (n := 1)).of_isPullback hbig inferInstance
  exact AlgebraicGeometry.smoothOfRelativeDimension_of_irreducibleSpace 1 (pullback.snd c s) V hVne

theorem not_smooth_snd_of_mem_badLocus [IsNoetherianRing R]
    (hH0 : ∀ (A' : Type u) [CommRing A'] [Algebra R A'],
      letI := Scheme.TwoAffineOpenCover.algebraOfHom
        (Limits.pullback.snd c (Scheme.TwoAffineOpenCover.specMap R A')) ⊤
      Function.Bijective (algebraMap A' Γ(Limits.pullback c (Scheme.TwoAffineOpenCover.specMap R A'), ⊤)))
    (U : C.Opens) [SmoothOfRelativeDimension 1 (U.ι ≫ c)]
    (ε : SchemeHomOver (𝟙 (Spec (CommRingCat.of R))) c) (hε : Set.range ε.1.base ⊆ (U : Set C))
    {k : Type u} [Field k] [IsAlgClosed k]
    (s : Spec (CommRingCat.of k) ⟶ Spec (CommRingCat.of R)) (hs : s.base (IsLocalRing.closedPoint k) ∈ badLocus c) :
    ¬ Smooth (pullback.snd c s) := by
  intro hsm
  obtain ⟨y, hyS, hyz⟩ := hs
  haveI := hsm
  have hdim : SmoothOfRelativeDimension 1 (pullback.snd c s) := smoothOfRelativeDimension_one_snd_of_smooth c hH0 U ε hε s

  have hy : y ∈ Set.range (pullback.fst c s).base := by
    rw [Scheme.Pullback.range_fst]
    exact ⟨IsLocalRing.closedPoint k, hyz.symm⟩
  obtain ⟨W, hyW, hW⟩ :=
    AlgebraicGeometry.exists_mem_and_smoothOfRelativeDimension_one_of_smoothOfRelativeDimension_pullback_snd c s hdim y hy
  apply hyS
  haveI := hW
  have h1 : (W.ι ≫ c).smoothLocus = ⊤ := Scheme.Hom.smoothLocus_eq_top _
  rw [← Scheme.Hom.preimage_smoothLocus_eq] at h1
  have : (⟨y, hyW⟩ : ↥W) ∈ (W.ι ⁻¹ᵁ c.smoothLocus) := by rw [h1]; trivial
  exact this

end BadLocus

section Hoff

variable {R : Type u} [CommRing R] [IsNoetherianRing R] {C : Scheme.{u}} (c : C ⟶ Spec (CommRingCat.of R))
  [IsProper c] [Flat c] [LocallyOfFinitePresentation c]

theorem isAlgEquivZero_fibre_of_eulerChar_eq_of_not_mem_badLocus
    (hH0 : ∀ (A' : Type u) [CommRing A'] [Algebra R A'],
      letI := Scheme.TwoAffineOpenCover.algebraOfHom
        (Limits.pullback.snd c (Scheme.TwoAffineOpenCover.specMap R A')) ⊤
      Function.Bijective (algebraMap A' Γ(Limits.pullback c (Scheme.TwoAffineOpenCover.specMap R A'), ⊤)))
    (U : C.Opens) [SmoothOfRelativeDimension 1 (U.ι ≫ c)]
    (ε : SchemeHomOver (𝟙 (Spec (CommRingCat.of R))) c) (hε : Set.range ε.1.base ⊆ (U : Set C))
    (hgred : ∀ (k : Type u) [Field k] [IsAlgClosed k]
      (x : Spec (CommRingCat.of k) ⟶ Spec (CommRingCat.of R)), IsReduced (pullback c x))
    {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) [LocallyOfFiniteType t]
    (L : RigidifiedLineBundle c ε t) (k : Type u) [Field k] [IsAlgClosed k] (s : Spec (CommRingCat.of k) ⟶ T)
    (hs : t.base (s.base (IsLocalRing.closedPoint k)) ∉ badLocus c)
    (𝒲 : (pullback (pullback.snd c t) s).TwoAffineOpenCover)
    (hχ : (Module.finrank k (𝒲.sectionsOf (fibreAt c t s) (fibreModule c t s L.L)).H0 : ℤ) -
        Module.finrank k (𝒲.sectionsOf (fibreAt c t s) (fibreModule c t s L.L)).H1 =
      (Module.finrank k (𝒲.sectionsOf (fibreAt c t s) (fibreModule c t s (𝟙_ (pullback c t).Modules))).H0 : ℤ) -
        Module.finrank k (𝒲.sectionsOf (fibreAt c t s) (fibreModule c t s (𝟙_ (pullback c t).Modules))).H1) :
    IsAlgEquivZero (fibreAt c t s) (fibreModule c t s L.L) := by

  have hsm : Smooth (pullback.snd c (s ≫ t)) :=
    smooth_snd_of_not_mem_badLocus c (s ≫ t) (by rwa [Scheme.Hom.comp_apply])
  haveI := hsm

  haveI : GeometricallyIrreducible (pullback.snd c (s ≫ t)) :=
    AlgebraicGeometry.RelPicard.HeadTransport.geometricallyIrreducible_snd_of_smooth_of_hH0 c hH0 (s ≫ t)
  haveI hirr : IrreducibleSpace ↥(pullback c (s ≫ t)) :=
    GeometricallyIrreducible.irreducibleSpace_of_subsingleton (f := pullback.snd c (s ≫ t))
  have hdim : SmoothOfRelativeDimension 1 (pullback.snd c (s ≫ t)) :=
    smoothOfRelativeDimension_one_snd_of_smooth c hH0 U ε hε (s ≫ t)

  obtain ⟨φ, hφ, -, -⟩ := exists_fibreIso_hom_comp_eq c t s (s ≫ t) rfl
  haveI : IsProper (fibreAt c t s) := by unfold fibreAt; infer_instance
  have hdim' : SmoothOfRelativeDimension 1 (fibreAt c t s) := by
    rw [← hφ]; exact MorphismProperty.RespectsIso.precomp (P := @SmoothOfRelativeDimension 1) φ.hom _ hdim
  haveI := hdim'
  haveI : IsReduced (pullback c (s ≫ t)) := hgred k (s ≫ t)
  haveI : IsReduced (pullback (pullback.snd c t) s) := isReduced_of_isOpenImmersion φ.hom
  haveI : IrreducibleSpace ↥(pullback (pullback.snd c t) s) :=
    (Scheme.homeoOfIso φ).irreducibleSpace_iff.mpr inferInstance
  haveI : IsIntegral (pullback (pullback.snd c t) s) := isIntegral_of_irreducibleSpace_of_isReduced _

  refine (isAlgEquivZero_iff_eulerChar_sectionsOf_eq k (fibreAt c t s) (fibreModule c t s L.L)
    (L.isInvertible.pullback _) 𝒲).mpr ?_
  exact hχ.trans (AlgebraicGeometry.RelPicard.HeadCut.eulerChar_congr (fibreAt c t s) 𝒲
    (Scheme.Modules.pullbackTensorUnitObjIso _))

end Hoff

end AlgebraicGeometry.RelPicard.HeadCut

open AlgebraicGeometry.RelPicard.HeadCut

theorem solution
    {R : Type u} [CommRing R] {C : Scheme.{u}} (c : C ⟶ Spec (CommRingCat.of R)) [IsProper c] [Flat c]
    (𝒱 : C.TwoAffineOpenCover)
    (hH0 : ∀ (A : Type u) [CommRing A] [Algebra R A],
      letI := Scheme.TwoAffineOpenCover.algebraOfHom
        (Limits.pullback.snd c (Scheme.TwoAffineOpenCover.specMap R A)) ⊤
      Function.Bijective (algebraMap A Γ(Limits.pullback c (Scheme.TwoAffineOpenCover.specMap R A), ⊤)))
    (ε : SchemeHomOver (𝟙 (Spec (CommRingCat.of R))) c) (U : C.Opens) [SmoothOfRelativeDimension 1 (U.ι ≫ c)]
    (hεA : Set.range ε.1 ⊆ (U : Set C))
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
    (hbad : ∀ (k : Type u) [Field k] [IsAlgClosed k]
      (s : Spec (CommRingCat.of k) ⟶ Spec (CommRingCat.of R)), ¬ Smooth (pullback.snd c s) →
      ∃ (C₁ C₂ : Scheme.{u}) (c₁ : C₁ ⟶ Spec (CommRingCat.of k)) (c₂ : C₂ ⟶ Spec (CommRingCat.of k))
        (_ : IsProper c₁) (_ : SmoothOfRelativeDimension 1 c₁) (_ : GeometricallyIntegral c₁)
        (_ : IsProper c₂) (_ : SmoothOfRelativeDimension 1 c₂) (_ : GeometricallyIntegral c₂)
        (i₁ : SchemeHomOver c₁ (pullback.snd c s)) (i₂ : SchemeHomOver c₂ (pullback.snd c s))
        (_ : IsClosedImmersion i₁.1) (_ : IsClosedImmersion i₂.1) (n : ℕ),
        (∀ z : ↥(pullback c s), z ∈ Set.range i₁.1.base ∨ z ∈ Set.range i₂.1.base) ∧
        IsReduced (pullback i₁.1 i₂.1) ∧ Nat.card ↥(pullback i₁.1 i₂.1) = n ∧ 0 < n ∧
        ((sectionFibrePoint ε s).1).base (IsLocalRing.closedPoint k) ∈ Set.range i₁.1.base \ Set.range i₂.1.base ∧
        ((pullback.fst c s ⁻¹ᵁ U : (pullback c s).Opens) : Set ↥(pullback c s)) =
          (Set.range (pullback.fst i₁.1 i₂.1 ≫ i₁.1).base)ᶜ ∧
        Set.range i₁.1.base ∩ ((pullback.fst c s ⁻¹ᵁ U : (pullback c s).Opens) : Set ↥(pullback c s)) =
          connectedComponentIn ((pullback.fst c s ⁻¹ᵁ U : (pullback c s).Opens) : Set ↥(pullback c s))
            (((sectionFibrePoint ε s).1).base (IsLocalRing.closedPoint k)) ∧
        Set.range i₂.1.base ∩ ((pullback.fst c s ⁻¹ᵁ U : (pullback c s).Opens) : Set ↥(pullback c s)) =
          ((pullback.fst c s ⁻¹ᵁ U : (pullback c s).Opens) : Set ↥(pullback c s)) \
            connectedComponentIn ((pullback.fst c s ⁻¹ᵁ U : (pullback c s).Opens) : Set ↥(pullback c s))
              (((sectionFibrePoint ε s).1).base (IsLocalRing.closedPoint k)) ∧
        (∃ W₁ : (pullback c s).Opens, (W₁ : Set ↥(pullback c s)) = (Set.range i₂.1.base)ᶜ ∧
          IsOpenImmersion ((i₁.1 ⁻¹ᵁ W₁).ι ≫ i₁.1)) ∧
        (∃ W₂ : (pullback c s).Opens, (W₂ : Set ↥(pullback c s)) = (Set.range i₁.1.base)ᶜ ∧
          IsOpenImmersion ((i₂.1 ⁻¹ᵁ W₂).ι ≫ i₂.1)))
    (A : Type u) [CommRing A] [Algebra R A] [IsNoetherianRing A] :
    AffineLimit.IsLFPSurj (relSubPicPresheaf (baseChange R c A) (sectionBaseChange A ε) (algEquivZeroCut (baseChange R c A) (sectionBaseChange A ε))) := by
  classical

  haveI : LocallyOfFinitePresentation (baseChange R c A) := locallyOfFinitePresentation_of_isNoetherianRing _
  haveI := AlgebraicGeometry.RelPicard.HeadTransport.smooth_U_baseChange c A U
  have hH0A := AlgebraicGeometry.RelPicard.HeadTransport.hH0_baseChange c A hH0
  have hεA' := AlgebraicGeometry.RelPicard.HeadTransport.hεU_baseChange c A U ε hεA
  have hgoodUA := AlgebraicGeometry.RelPicard.HeadTransport.hgoodU_baseChange c A U hgoodU
  have hgredA := AlgebraicGeometry.RelPicard.HeadTransport.hgred_baseChange c A hgred
  have hgA := AlgebraicGeometry.RelPicard.HeadTransport.hg_baseChange c A g hg
  have hbadA := twoGluedSmoothCurveDegenerations_baseChange c A ε U hbad

  have hZ₀ := isClosed_badLocus (baseChange R c A)
  have hZ₀off : ∀ (k : Type u) [Field k] [IsAlgClosed k] (s : Spec (CommRingCat.of k) ⟶ Spec (CommRingCat.of A)),
      s.base (IsLocalRing.closedPoint k) ∉ badLocus (baseChange R c A) → Smooth (pullback.snd (baseChange R c A) s) :=
    fun k _ _ s hs => smooth_snd_of_not_mem_badLocus (baseChange R c A) s hs
  have hZ₀on : ∀ (k : Type u) [Field k] [IsAlgClosed k] (s : Spec (CommRingCat.of k) ⟶ Spec (CommRingCat.of A)),
      s.base (IsLocalRing.closedPoint k) ∈ badLocus (baseChange R c A) → ¬ Smooth (pullback.snd (baseChange R c A) s) :=
    fun k _ _ s hs => not_smooth_snd_of_mem_badLocus (baseChange R c A) hH0A (pullback.fst c (specMap R A) ⁻¹ᵁ U)
      (sectionBaseChange A ε) hεA' s hs

  refine isLFPSurj_relSubPicPresheaf_algEquivZeroCut_of_isOpen_setOf_isAlgEquivZero A (baseChange R c A)
    (𝒱.pullback c A) (sectionBaseChange A ε) ?_
    (isAlgEquivZero_fibre_of_range_subset_singleton_of_twoGluedSmoothCurveDegenerations A (baseChange R c A)
      (𝒱.pullback c A) hH0A (pullback.fst c (specMap R A) ⁻¹ᵁ U) (sectionBaseChange A ε) hεA' hgoodUA hgredA g hgA hbadA)

  intro T t _ L
  exact isOpen_setOf_isAlgEquivZero_fibre_of_twoStrata A (baseChange R c A) (𝒱.pullback c A)
    (sectionBaseChange A ε) (badLocus (baseChange R c A)) hZ₀
    (fun t' _ L' k _ _ s' h 𝒲 =>
      AlgebraicGeometry.RelPicard.HeadCut.eulerChar_fibre_eq_of_isAlgEquivZero (baseChange R c A) (sectionBaseChange A ε) t' L' k s' h 𝒲)
    (fun t' _ L' k _ _ s' hs' 𝒲 hχ =>
      isAlgEquivZero_fibre_of_eulerChar_eq_of_not_mem_badLocus (baseChange R c A) hH0A (pullback.fst c (specMap R A) ⁻¹ᵁ U)
        (sectionBaseChange A ε) hεA' hgredA t' L' k s' hs' 𝒲 hχ)
    (exists_isOpen_inter_preimage_eq_setOf_isAlgEquivZero_fibre_of_smoothLocus_of_twoGluedSmoothCurveDegenerations A (baseChange R c A)
      (𝒱.pullback c A) hH0A (pullback.fst c (specMap R A) ⁻¹ᵁ U) (sectionBaseChange A ε) hεA' hgoodUA hgredA g hgA hbadA
      (badLocus (baseChange R c A)) hZ₀ hZ₀off hZ₀on)
    t L

end S_AlgebraicGeometry_RelPicard_isLFPSurj_relSubPicPresheaf_algEquivZeroCut_baseChange_of_twoGluedSmoothCurveDegenerations
end P2MW
export P2MW.S_AlgebraicGeometry_RelPicard_isLFPSurj_relSubPicPresheaf_algEquivZeroCut_baseChange_of_twoGluedSmoothCurveDegenerations (solution)
