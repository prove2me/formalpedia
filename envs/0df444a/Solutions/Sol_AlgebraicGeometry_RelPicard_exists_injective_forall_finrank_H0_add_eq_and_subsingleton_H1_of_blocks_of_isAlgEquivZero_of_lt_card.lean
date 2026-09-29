-- Prove2me | solution 1 for AlgebraicGeometry.RelPicard.exists_injective_forall_finrank_H0_add_eq_and_subsingleton_H1_of_blocks_of_isAlgEquivZero_of_lt_card
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:03.589526+00:00
-- url     : https://prove2.me/submissions/d71aedf1-b5e3-544b-9727-cc012b886153

import Mathlib
import Definitions.Def_AlgebraicGeometry_NeronModelPropertyBundleCarrier
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import Definitions.Def_AlgebraicGeometry_RepresentsRelSubPic
import Definitions.Def_AlgebraicGeometry_RelPicardAlgEquivZeroCut
import Definitions.Def_AlgebraicGeometry_TwoAffineOpenCover
import Definitions.Def_AlgebraicGeometry_TwoChartCechSectionsOf
import Definitions.Def_AlgebraicCurve_CurveModel
import Definitions.Def_AlgebraicCurve_AdelicIndex
import Definitions.Def_SheafOfModules_Monoidal
import Definitions.Def_AlgebraicGeometry_IdealSheafModule
import Definitions.Def_AlgebraicCurve_RelCartier
import Definitions.Def_AlgebraicCurve_IsCurveOver
import Definitions.Def_AlgebraicCurve_DivisorClassGroup
import Definitions.Def_AlgebraicCurve_Repartitions
import Definitions.Def_AlgebraicGeometry_ModulesSectionZeroScheme
import Definitions.Def_AlgebraicGeometry_RelEffCartierDiv
import Definitions.Def_AlgebraicGeometry_RelEffCartierDivOfPoint
import Definitions.Def_AlgebraicGeometry_RelEffCartierDivSum
import Theorems.Thm_AlgebraicGeometry_Scheme_TwoAffineOpenCover_exists_linearEquiv_sectionsOf_H0
import Theorems.Thm_AlgebraicGeometry_RelEffCartierDiv_exists_I_eq_prodKerGraph_of_isAlgClosed
import Theorems.Thm_AlgebraicGeometry_Scheme_TwoAffineOpenCover_exists_linearEquiv_sectionsOf_of_iso
import Theorems.Thm_AlgebraicGeometry_RelPicard_IsAlgEquivZero_eulerChar_sectionsOf_tensor_eq
import Theorems.Thm_AlgebraicCurve_exists_isAffineOpen_sup_eq_top
import Theorems.Thm_AlgebraicGeometry_Scheme_IdealSheafData_IsInvertible_pow
import Theorems.Thm_AlgebraicCurve_exists_isAffineOpen_forall_mem_of_finset
import Theorems.Thm_AlgebraicGeometry_Scheme_IdealSheafData_IsInvertible_isInvertible_invModule
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_IsInvertible_tensor
import Theorems.Thm_AlgebraicGeometry_Scheme_IdealSheafData_IsInvertible_isInvertible_module
import Theorems.Thm_AlgebraicGeometry_Scheme_TwoAffineOpenCover_finrank_H1_sectionsOf_unit_eq_and_finrank_H0_eq_one
import Theorems.Thm_AlgebraicGeometry_RelEffCartierDiv_exists_I_eq_zeroSchemeIdeal_of_eulerChar_eq
import Theorems.Thm_AlgebraicGeometry_Scheme_Hom_isInvertible_ker_of_comp_eq_id
import Theorems.Thm_AlgebraicCurve_isCurveOver_of_ringEquiv_functionField_of_isIntegral_of_smoothOfRelativeDimension_one
import Theorems.Thm_AlgebraicCurve_CurveModel_finrank_H0_sectionsOf_invModule_prod_ker_tensor_module_prod_ker_eq_ell
import Theorems.Thm_AlgebraicGeometry_subsingleton_H1_and_finrank_H0_sectionsOf_tensor_invModule_pow_ker_of_isAlgEquivZero
import Theorems.Thm_AlgebraicGeometry_GeometricallyIrreducible_of_irreducibleSpace_of_isAlgClosed
import Theorems.Thm_AlgebraicGeometry_Scheme_IdealSheafData_IsInvertible_nonempty_pullback_invModule_iso
import Theorems.Thm_AlgebraicGeometry_RelEffCartierDiv_isInvertible_I
import Theorems.Thm_AlgebraicGeometry_Scheme_IdealSheafData_IsInvertible_eulerChar_sectionsOf_tensor_invModule_eq
import Theorems.Thm_AlgebraicGeometry_Scheme_Hom_isFinite_and_finrank_subschemeIota_ker_pow_of_comp_eq_id
import Theorems.Thm_AlgebraicGeometry_Scheme_IdealSheafData_IsInvertible_isFinite_and_finrank_mul_subscheme_comp_eq_add
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_IsInvertible_dual
import Theorems.Thm_AlgebraicGeometry_SmoothProperCurve_exists_curveModel_riemannRoch_of_isAlgClosed
import Theorems.Thm_AlgebraicCurve_CurveModel_eq_genusFF_of_forall_ell_sub_ell_eq
import Theorems.Thm_AlgebraicCurve_nonempty_algEquiv_functionField_of_iso
import Theorems.Thm_AlgebraicCurve_genusFF_eq_of_algEquiv
import Theorems.Thm_AlgebraicGeometry_Scheme_TwoAffineOpenCover_finrank_cechDiff_baseChange_of_isAlgClosed
import Theorems.Thm_AlgebraicGeometry_geometricallyIntegral_of_isAlgClosed
import Theorems.Thm_AlgebraicCurve_RROpens_exists_injective_forall_forall_mem_ell_sub_sum_single_add_eq_ell_of_lt_card
import Theorems.Thm_AlgebraicGeometry_Scheme_IdealSheafData_IsInvertible_nonempty_module_tensor_invModule_iso
import Theorems.Thm_AlgebraicGeometry_Scheme_IdealSheafData_IsInvertible_nonempty_mul_invModule_iso_tensor
import Theorems.Thm_AlgebraicCurve_ell_eq_zero_of_degree_neg
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_RelPicard_exists_injective_forall_finrank_H0_add_eq_and_subsingleton_H1_of_blocks_of_isAlgEquivZero_of_lt_card
p2m_attr_erase "instance" "AlgebraicGeometry.OModulePresheaf.isScalarTower AlgebraicGeometry.Scheme.OrderedAffineCover.instLinearOrder AlgebraicGeometry.OModulePresheaf.module AlgebraicGeometry.Scheme.OrderedAffineCover.instFintype AlgebraicGeometry.Scheme.OrderedAffineCover.instFintypeIdx AlgebraicGeometry.OModulePresheaf.addCommGroup AlgebraicGeometry.Scheme.OrderedAffineCover.instDecidableEqIdx AlgebraicGeometry.OModulePresheaf.moduleSections AlgebraicGeometry.Scheme.Modules.preservesBinaryProducts_opensMap AlgebraicGeometry.Scheme.Modules.pullback_monoidal AlgebraicGeometry.Scheme.Modules.sheafify_isLocalization' AlgebraicGeometry.Scheme.Modules.preservesTerminal_opensMap AlgebraicGeometry.Scheme.Modules.pullback₀_monoidal AlgebraicGeometry.Scheme.Modules.preservesFiniteProducts_opensMap AlgebraicGeometry.Scheme.Modules.instLiftingPresheafOfModulesSheafifyPresheafWOpensCarrierCarrierCommRingCatGrothendieckTopologyObjFunctorOppositeIsSheafSheafCompPullback₀Pullback PresheafOfModules.PullbackMonoidal.pullback_monoidal PresheafOfModules.PullbackMonoidal.isIso_δ PresheafOfModules.pushforward_laxMonoidal PresheafOfModules.PullbackMonoidal.isIso_η PresheafOfModules.free_monoidal PresheafOfModules.restrictScalars_laxMonoidal PresheafOfModules.PullbackMonoidal.isIso_δ_gS PresheafOfModules.pullback_oplaxMonoidal PresheafOfModules.PullbackMonoidal.instPreservesColimitsOfSizeCompOppositeCommRingCatRingCatForget₂RingHomCarrierCarrierPb PresheafOfModules.pullback_monoidal' AlgebraicGeometry.OModulePresheaf.instSubsingletonObjZero AlgebraicGeometry.OModulePresheaf.Leray.relAltC_scalarTower AlgebraicGeometry.OModulePresheaf.Leray.ker_relAltd_modΓ AlgebraicGeometry.OModulePresheaf.Leray.relAltC_modΓ AlgebraicGeometry.OModulePresheaf.Leray.biC_abGrp AlgebraicGeometry.OModulePresheaf.Leray.relAltH_modΓ AlgebraicGeometry.OModulePresheaf.Leray.ker_relAltd_smul AlgebraicGeometry.OModulePresheaf.Leray.relAltH_scalarTower AlgebraicGeometry.OModulePresheaf.Leray.relAltH_smul AlgebraicGeometry.OModulePresheaf.Leray.biC_module AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instDecidableEqIdx AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instFintype AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instLinearOrder AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instFintypeIdx DoubleComplex.instModuleE₂I"
p2m_attr_erase "instance" "DoubleComplex.Bounded.modR DoubleComplex.instModuleE₂II DoubleComplex.instAddCommGroupE₂II DoubleComplex.Bounded.abGrp DoubleComplex.instAddCommGroupE₂I AlgebraicGeometry.ChowDatum.hι_closed AlgebraicGeometry.ChowDatumProj.hιN_closed AlgebraicGeometry.ChowDatumProj.hp_proper AlgebraicGeometry.ChowDatum.hp_isoU AlgebraicGeometry.ChowDatum.hp_proper AlgebraicGeometry.ProjSpace.algebraAway AlgebraicGeometry.ProjSpace.instIsProperProdOverπ AlgebraicGeometry.ChowDatumProj.hp_isoU AlgebraicGeometry.ProjSpace.isProper_π AlgebraicGeometry.ProjSpace.finiteType_mvPolynomial ProjSpaceCech.GradedModule.H.module ProjSpaceCech.GradedModule.H.addCommGroup ProjSpaceCech.GradedModule.sec.instAdd ProjSpaceCech.GradedModule.sec.instNeg ProjSpaceCech.GradedModule.acg ProjSpaceCech.GradedModule.Frac.setoid ProjSpaceCech.GradedModule.modR ProjSpaceCech.GradedModule.sec.instModule ProjSpaceCech.GradedModule.sec.instAddCommGroup ProjSpaceCech.GradedModule.sec.instZero ProjSpaceCech.GradedModule.Presentation.fJ ProjSpaceCech.GradedModule.sec.instSMul ProjSpaceCech.Twist.H.module ProjSpaceCech.Idx.instFintype ProjSpaceCech.Twist.H.addCommGroup ProjSpaceCech.Idx.instDecidableEq ProjSpaceCech.Twist.Mon.instDecidableEq ProjSpaceCech.Twist.cochain.instAddCommGroup ProjSpaceCech.Twist.cochain.instModule AlgebraicCurve.instFundamentalIdentityOfSumRamificationInertia AlgebraicCurve.Place.instIsScalarTowerResidueFieldRestrictPushforward AlgebraicCurve.Place.instAlgebraResidueFieldRestrictPushforward AlgebraicCurve.Place.instIsLocalHomRestrictInclusion AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt"
p2m_attr_erase "instance" "AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.SemilinearAut.instDistribMulActionSubtypeProdRingAutMemSubgroupPic0 AlgebraicCurve.SemilinearAut.instDistribMulActionSubtypeProdRingAutMemSubgroupDivisor AlgebraicCurve.Pic0.instModuleZModTorsion AlgebraicCurve.SemilinearAut.instSMulSubtypeProdRingAutMemSubgroupPlace AlgebraicCurve.SemilinearAut.instDistribMulActionTorsion AlgebraicCurve.SemilinearAut.instSMulSubtypeProdRingAutMemSubgroupPic0 AlgebraicCurve.SemilinearAut.instSMulTorsion AlgebraicCurve.SemilinearAut.instMulActionSubtypeProdRingAutMemSubgroupPlace AlgebraicCurve.SemilinearAut.instSMulCommClassZModTorsion AlgebraicCurve.SemilinearAut.instMulSemiringActionSubtypeProdRingAutMemSubgroup instDecEqAlgebraicClosureRat WeierstrassCurve.Affine.Point.instDistribMulActionAlgEquiv WeierstrassCurve.Affine.Point.instModuleZModTorsionBy WeierstrassCurve.Affine.Point.instSMulTorsionBy WeierstrassCurve.Affine.Point.instDistribMulActionTorsionBy WeierstrassCurve.Affine.Point.instSMulAlgEquiv WeierstrassCurve.Affine.Point.instSMulCommClassAlgEquivZModTorsionBy AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions AlgebraicCurve.instHasLocalResidue_of_hasCanonicalLocalResidueK AlgebraicCurve.instHasCanonicalLocalResidueK_of_hasCanonicalLocalResidueKStar AlgebraicCurve.Place.kw_ffgc_finiteDimensional_adicCompletion instAlgebraSubtypeMemValuationSubring_definitions AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersIntegersCompletion ModularCurve.KwF4gRRTate.instAlgebraKAdicCompletionIntegers AlgebraicCurve.Place.kw_ffgc_continuousSMul_adicCompletionComap AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersCompletionCompletion IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions AlgebraicCurve.instHasCanonicalLocalResidueK AlgebraicCurve.Place.instAlgebra_restrictResidueField AlgebraicCurve.Place.instIsScalarTower_restrictResidueField"
p2m_attr_erase "instance" "AlgebraicCurve.instHasLocalResidue AlgebraicCurve.HasSeparableResidue.of_perfectField_of_isCurveOver AlgebraicCurve.HasSeparableResidue.of_perfectField AlgebraicCurve.Place.instIsLocalHom_restrictSubringHom AlgebraicCurve.instHasCanonicalLocalResidueKStar ModularCurve.KwNo6Pin.isLocalRing_completion SheafOfModules.isIso_ihomModelToIhom"
p2m_attr_erase "simp" "AlgebraicGeometry.Scheme.OrderedAffineCover.mk.injEq AlgebraicGeometry.OModulePresheaf.mk.sizeOf_spec AlgebraicGeometry.Scheme.OrderedAffineCover.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.mk.injEq PresheafOfModules.freeεIso_hom_app PresheafOfModules.freeμIso_hom_app TwoChartCech.Mumford.dK_apply TwoChartCech.Mumford.ι0_apply TwoChartCech.Mumford.ι1_apply TwoChartCech.KerCoprod.dK_apply TwoChartCech.KerCoprod.ι1_apply TwoChartCech.KerCoprod.ι0_apply AlgebraicGeometry.tilde.functorCompPullbackSpecIso_app AlgebraicGeometry.OModulePresheaf.prod_obj AlgebraicGeometry.OModulePresheaf.restrOpen_obj AlgebraicGeometry.OModulePresheaf.DevissageStep.mk.injEq AlgebraicGeometry.OModulePresheaf.pushforward_obj AlgebraicGeometry.OModulePresheaf.im_obj AlgebraicGeometry.OModulePresheaf.pow_obj AlgebraicGeometry.OModulePresheaf.fstHom_app AlgebraicGeometry.OModulePresheaf.ker_obj AlgebraicGeometry.OModulePresheaf.coker_obj AlgebraicGeometry.OModulePresheaf.DevissageStep.mk.sizeOf_spec AlgebraicGeometry.Scheme.OrderedAffineCover.preimage_U AlgebraicGeometry.OModulePresheaf.sndHom_app AlgebraicGeometry.OModulePresheaf.Hom.mk.injEq AlgebraicGeometry.OModulePresheaf.Hom.id_app AlgebraicGeometry.OModulePresheaf.AffHom.appSections_apply AlgebraicGeometry.OModulePresheaf.AffHom.comp_app AlgebraicGeometry.OModulePresheaf.AffSES.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.AffHom.kerMap_coe AlgebraicGeometry.OModulePresheaf.AffHom.id_app AlgebraicGeometry.OModulePresheaf.Hom.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.Hom.toAffHom_app AlgebraicGeometry.OModulePresheaf.SES.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.AffHom.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.Hom.comp_app AlgebraicGeometry.OModulePresheaf.SES.mk.injEq AlgebraicGeometry.OModulePresheaf.AffHom.mk.injEq AlgebraicGeometry.OModulePresheaf.Hom.appSections_apply"
p2m_attr_erase "simp" "AlgebraicGeometry.OModulePresheaf.AffSES.mk.injEq AlgebraicGeometry.OModulePresheaf.Leray.restrictToPreimage_U AlgebraicGeometry.Scheme.OrderedAffineCover.toCoverOf_U AlgebraicGeometry.Scheme.OrderedAffineCoverOf.mk.sizeOf_spec AlgebraicGeometry.Scheme.OrderedAffineCoverOf.mk.injEq AlgebraicGeometry.Scheme.OrderedAffineCover.restrict_U DoubleComplex.Bounded.mk.injEq DoubleComplex.Bounded.mk.sizeOf_spec DoubleComplex.Convergence.mk.injEq DoubleComplex.Convergence.mk.sizeOf_spec DoubleComplex.SubQuot.mk.sizeOf_spec DoubleComplex.SubQuot.mk.injEq AlgebraicGeometry.ChowDatumProj.mk.sizeOf_spec AlgebraicGeometry.ChowDatum.mk.sizeOf_spec AlgebraicGeometry.ChowDatumProj.mk.injEq AlgebraicGeometry.ChowDatum.mk.injEq ProjSpaceCech.GradedModule.mk.injEq ProjSpaceCech.GradedModule.mk.sizeOf_spec ProjSpaceCech.GradedModule.Frac.mk.sizeOf_spec ProjSpaceCech.GradedModule.Presentation.mk.injEq ProjSpaceCech.GradedModule.Frac.mk.injEq ProjSpaceCech.GradedModule.Presentation.mk.sizeOf_spec ProjSpaceCech.GradedModule.Hom.shift_toLinearMap ProjSpaceCech.GradedModule.Hom.mk.sizeOf_spec ProjSpaceCech.GradedModule.Hom.mk.injEq AlgebraicCurve.Divisor.mapRestrict_single AlgebraicCurve.Divisor.pushforward_single AlgebraicCurve.Place.coe_restrictInclusion AlgebraicCurve.Place.mem_fiber AlgebraicCurve.Place.restrict_toValuationSubring AlgebraicCurve.Divisor.degree_pushforward AlgebraicCurve.Place.restrictResidueMap_residue AlgebraicCurve.Pic0.coe_pushforwardDegZeroHom AlgebraicCurve.Pic0.coe_pullbackDegZeroHom AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal AlgebraicCurve.IsFrobeniusEndo.frobNormRingHom_apply"
p2m_attr_erase "simp" "ModularCurve.frobeniusPushforwardGeomLevelPic0_mk ModularCurve.coe_frobeniusGeomLevelEquiv_apply ModularCurve.coe_frobeniusPushforwardGeomLevelDegZero ModularCurve.heckeFibreGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusGeomLevel_apply_coe ModularCurve.frobeniusPullbackGeomLevelPic0OfIsCurveOver_mk ModularCurve.coe_heckeFibreGeomLevelDegZero ModularCurve.coe_frobeniusPullbackGeomLevelDegZero ModularCurve.frobeniusPullbackGeomLevelPic0_mk ModularCurve.frobeniusPullbackGeomLevel_single ModularCurve.heckeFibreGeomLevelPic0_mk ModularCurve.frobeniusPushforwardGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusPushforwardGeomLevel_single ModularCurve.qExpandAlgC_apply AlgebraicCurve.Place.congrEquiv_symm_apply AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply AlgebraicCurve.RationalFunctionField.deg_placeOfPoint AlgebraicCurve.Divisor.degree_pushforwardAlong AlgebraicCurve.Pic0.coe_degZeroCorrespondence AlgebraicCurve.Place.mem_fiberAlong AlgebraicCurve.SemilinearAut.toRingAut_inv AlgebraicCurve.SemilinearAut.smul_def AlgebraicCurve.SemilinearAut.smul_single AlgebraicCurve.SemilinearAut.smul_toValuationSubring AlgebraicCurve.SemilinearAut.baseAut_inv AlgebraicCurve.SemilinearAut.baseAut_ofAlgAut AlgebraicCurve.SemilinearAut.toRingAut_ofAlgAut AlgebraicCurve.SemilinearAut.torsionRep_apply AlgebraicCurve.SemilinearAut.toRingAut_one AlgebraicCurve.SemilinearAut.deg_smul AlgebraicCurve.SemilinearAut.degree_smul AlgebraicCurve.SemilinearAut.coe_degZeroSMulHom AlgebraicCurve.SemilinearAut.baseAut_mul AlgebraicCurve.SemilinearAut.coe_smulValuationSubringEquiv_apply AlgebraicCurve.SemilinearAut.baseAut_one AlgebraicCurve.SemilinearAut.ofAlgAut_smul AlgebraicCurve.SemilinearAut.coe_torsion_smul"
p2m_attr_erase "simp" "AlgebraicCurve.SemilinearAut.toRingAut_mul AlgebraicCurve.coe_frobeniusPushforwardDegZero AlgebraicCurve.IsFrobeniusEndo.coe_frobeniusPullbackDegZero ModularCurve.jqNModC_one ModularCurve.qExpand_coeff_mul ModularCurve.qExpandₐ_apply ModularCurve.jqN_one ModularCurve.qExpand_single ModularCurve.dedekindPsi_one ModularCurve.ModularPolynomialData.mk.sizeOf_spec ModularCurve.evalAtJ_X ModularCurve.ModularPolynomialData.mk.injEq ModularCurve.constantCoeff_jNum ModularCurve.constantCoeff_eisenstein4 ModularCurve.qExpand_C ModularCurve.coeff_jq_neg_one ModularCurve.constantCoeff_jNumQ ModularCurve.reduceModBivar_C_X ModularCurve.laurentMap_coeff ModularCurve.reduceModBivar_X ModularCurve.laurentMap_single ModularCurve.evalAtJInt_X ModularCurve.evalAtJMod_X ModularCurve.jqNMod_one ModularCurve.aeval_heckeGen ModularCurve.coe_mTorsionGaloisRep_apply ModularCurve.eisensteinSystem_of_dvd ModularCurve.eisensteinSystem_of_not_dvd FreyPackage.mk.sizeOf_spec FreyPackage.mk.injEq WeierstrassCurve.Affine.Point.galoisRepModuleEnd_apply AlgebraicCurve.RationalFunctionField.placeInfty_toValuationSubring AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none AlgebraicCurve.Divisor.evalFun_zero AlgebraicCurve.Place.evalAt_one AlgebraicCurve.Place.differentialCoeff_zero AlgebraicCurve.Place.differentialCoeff_dCoord"
p2m_attr_erase "simp" "AlgebraicCurve.TranscendenceTower.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.injEq AlgebraicCurve.TranscendenceTower.mk.injEq AlgebraicCurve.PoleDivisorPackage.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.sizeOf_spec AlgebraicCurve.PoleDivisorPackage.mk.injEq AlgebraicCurve.coe_cechH0Equiv_apply AlgebraicCurve.cechH1ToH1_mk AlgebraicCurve.lSpaceOn_univ AlgebraicCurve.lSpaceOn_empty AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.sizeOf_spec AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.injEq AlgebraicCurve.adeleSingle_coe AlgebraicCurve.kaehlerResidueTermKFam_apply AlgebraicCurve.Place.LocalResidueData.mk.injEq AlgebraicCurve.Place.LocalResidueData.mk.sizeOf_spec AlgebraicCurve.Place.kw_ffgc_adicCompletionComapIntegers_coe AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.sizeOf_spec AlgebraicCurve.Place.mem_simplePoleSubmodule AlgebraicCurve.Place.coe_uniformizerSubring ModularCurve.Lg37.Lg37CompletionSection.mk.injEq AlgebraicCurve.Place.CoefficientFieldSection.mk.injEq AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.injEq ModularCurve.Lg37.Lg37CompletionSection.mk.sizeOf_spec AlgebraicCurve.Place.CoefficientFieldSection.mk.sizeOf_spec AlgebraicCurve.Place.poleSubmodule_one AlgebraicCurve.Place.mem_poleSubmodule PresheafOfModules.InternalHom.IsSheafAux.appAt_toPresheafHom SheafOfModules.ihomSectionsEquivFamily_unit AlgebraicGeometry.Scheme.Modules.restrictHomEquivFamily_apply SheafOfModules.ihomEval_unit_app AlgebraicGeometry.Scheme.Modules.ihomEval_zero_right AlgebraicGeometry.Scheme.Modules.ihomEval_zero_left AlgebraicGeometry.Scheme.Modules.homOfFamily_app_apply SheafOfModules.unit_ihomSectionsEquivFamily AlgebraicGeometry.Scheme.Modules.familyOfHom_app AlgebraicGeometry.Scheme.Modules.restrictUnitIso_hom_app_apply AlgebraicGeometry.Scheme.Modules.restrictUnitIso_inv_app_apply AlgebraicGeometry.Scheme.Modules.restrictHomOfFamily_app_apply AlgebraicGeometry.Scheme.Modules.restrictHomEquivFamily_symm_apply"
p2m_attr_erase "simp" "AlgebraicGeometry.Scheme.Modules.tensorSections_zero_right AlgebraicGeometry.Scheme.Modules.map_unitSection AlgebraicGeometry.Scheme.Modules.tensorSectionsBilin_apply AlgebraicGeometry.Scheme.Modules.tensorPowSection_zero AlgebraicGeometry.Scheme.Modules.tensorSections_zero_left AlgebraicGeometry.Scheme.Modules.tensorPow_zero AlgebraicGeometry.Scheme.Modules.tensorPow_succ AlgebraicGeometry.Scheme.Modules.pullbackLocalSection_neg AlgebraicGeometry.Scheme.Modules.pullbackLocalSection_zero AlgebraicGeometry.Scheme.Modules.pullbackLocalSection_sub AlgebraicGeometry.Scheme.Modules.pullbackLocalSection_add"

set_option autoImplicit false

universe u v w

p2m_open "CategoryTheory CategoryTheory.Limits AlgebraicGeometry P2MW.S_AlgebraicGeometry_RelPicard_exists_injective_forall_finrank_H0_add_eq_and_subsingleton_H1_of_blocks_of_isAlgEquivZero_of_lt_card.AlgebraicGeometry AlgebraicGeometry.RelPicard NeronModelInfra CategoryTheory.MonoidalCategory AlgebraicCurve~genus~cechDiff Opposite AlgebraicGeometry.SmoothProperCurve"

open scoped TensorProduct

noncomputable section

namespace AlgebraicGeometry
p2m_export "AlgebraicGeometry" "Scheme.Hom.ker_comp_of_isIso Scheme.IdealSheafData.ideal_mul Scheme.Modules.Hom.zero_app SmoothOfRelativeDimension Scheme.IdealSheafData.one_eq_top IsProper Scheme.Modules.pullback Scheme.Hom GeometricallyIntegral Scheme.Modules.presheaf GeometricallyIrreducible Scheme.Modules.Hom IsFinite Spec IsIntegral Spec.map Scheme Scheme.Modules.Hom.app Scheme.IdealSheafData.comap_top Scheme.IdealSheafData.ker_fst_of_isClosedImmersion IsClosedImmersion IsSeparated Scheme.Modules.pullbackCongr Spec.map_id Scheme.Modules.pullbackId Scheme.Modules Scheme.IdealSheafData.ext Scheme.IdealSheafData Scheme.Modules.pullbackComp Scheme.IdealSheafData.ideal_comap_of_isOpenImmersion Scheme.Modules.IsInvertible Scheme.Modules.pullbackUnitIso Scheme.Modules.isInvertible_unit Scheme.TwoAffineOpenCover Scheme.TwoAffineOpenCover.specMap RelEffCartierDiv Scheme.IdealSheafData.IsInvertible Scheme.IdealSheafData.isInvertible_top graphOver prodKerGraph prodKerGraph_eq_prod Scheme.Hom.finrank_eq_zero_of_isEmpty Scheme.TwoAffineOpenCover.exists_linearEquiv_sectionsOf_H0 RelEffCartierDiv.exists_I_eq_prodKerGraph_of_isAlgClosed Scheme.TwoAffineOpenCover.exists_linearEquiv_sectionsOf_of_iso Scheme.TwoAffineOpenCover.finrank_H1_sectionsOf_unit_eq_and_finrank_H0_eq_one RelEffCartierDiv.exists_I_eq_zeroSchemeIdeal_of_eulerChar_eq Scheme.Hom.isInvertible_ker_of_comp_eq_id GeometricallyIrreducible.of_irreducibleSpace_of_isAlgClosed Scheme.IdealSheafData.IsInvertible.nonempty_pullback_invModule_iso Scheme.IdealSheafData.IsInvertible.eulerChar_sectionsOf_tensor_invModule_eq Scheme.Hom.isFinite_and_finrank_subschemeIota_ker_pow_of_comp_eq_id Scheme.IdealSheafData.IsInvertible.isFinite_and_finrank_mul_subscheme_comp_eq_add Scheme.TwoAffineOpenCover.finrank_cechDiff_baseChange_of_isAlgClosed geometricallyIntegral_of_isAlgClosed Scheme.IdealSheafData.IsInvertible.nonempty_module_tensor_invModule_iso"
namespace ChiFibGenus
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

end AlgebraicGeometry.ChiFibGenus

namespace AlgebraicGeometry
p2m_export "AlgebraicGeometry" "Scheme.Hom.ker_comp_of_isIso Scheme.IdealSheafData.ideal_mul Scheme.Modules.Hom.zero_app SmoothOfRelativeDimension Scheme.IdealSheafData.one_eq_top IsProper Scheme.Modules.pullback Scheme.Hom GeometricallyIntegral Scheme.Modules.presheaf GeometricallyIrreducible Scheme.Modules.Hom IsFinite Spec IsIntegral Spec.map Scheme Scheme.Modules.Hom.app Scheme.IdealSheafData.comap_top Scheme.IdealSheafData.ker_fst_of_isClosedImmersion IsClosedImmersion IsSeparated Scheme.Modules.pullbackCongr Spec.map_id Scheme.Modules.pullbackId Scheme.Modules Scheme.IdealSheafData.ext Scheme.IdealSheafData Scheme.Modules.pullbackComp Scheme.IdealSheafData.ideal_comap_of_isOpenImmersion Scheme.Modules.IsInvertible Scheme.Modules.pullbackUnitIso Scheme.Modules.isInvertible_unit Scheme.TwoAffineOpenCover Scheme.TwoAffineOpenCover.specMap RelEffCartierDiv Scheme.IdealSheafData.IsInvertible Scheme.IdealSheafData.isInvertible_top graphOver prodKerGraph prodKerGraph_eq_prod Scheme.Hom.finrank_eq_zero_of_isEmpty Scheme.TwoAffineOpenCover.exists_linearEquiv_sectionsOf_H0 RelEffCartierDiv.exists_I_eq_prodKerGraph_of_isAlgClosed Scheme.TwoAffineOpenCover.exists_linearEquiv_sectionsOf_of_iso Scheme.TwoAffineOpenCover.finrank_H1_sectionsOf_unit_eq_and_finrank_H0_eq_one RelEffCartierDiv.exists_I_eq_zeroSchemeIdeal_of_eulerChar_eq Scheme.Hom.isInvertible_ker_of_comp_eq_id GeometricallyIrreducible.of_irreducibleSpace_of_isAlgClosed Scheme.IdealSheafData.IsInvertible.nonempty_pullback_invModule_iso Scheme.IdealSheafData.IsInvertible.eulerChar_sectionsOf_tensor_invModule_eq Scheme.Hom.isFinite_and_finrank_subschemeIota_ker_pow_of_comp_eq_id Scheme.IdealSheafData.IsInvertible.isFinite_and_finrank_mul_subscheme_comp_eq_add Scheme.TwoAffineOpenCover.finrank_cechDiff_baseChange_of_isAlgClosed geometricallyIntegral_of_isAlgClosed Scheme.IdealSheafData.IsInvertible.nonempty_module_tensor_invModule_iso"
namespace ChiFib
p2m_open "AlgebraicGeometry"

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

theorem prod_ker {K : Type u} [Field K] {X : Scheme.{u}} (x : X ⟶ Spec (CommRingCat.of K))
    [IsProper x] [SmoothOfRelativeDimension 1 x] (𝒱 : X.TwoAffineOpenCover)
    {n : ℕ} (v : Fin n → {q : Spec (CommRingCat.of K) ⟶ X // q ≫ x = 𝟙 _}) (s : Finset (Fin n)) :
    (∏ j ∈ s, (v j).1.ker).IsInvertible ∧
      ∃ _ : IsFinite ((∏ j ∈ s, (v j).1.ker).subschemeι ≫ x),
        ∀ y, ((∏ j ∈ s, (v j).1.ker).subschemeι ≫ x).finrank y = s.card := by
  classical
  haveI : IsSeparated x := inferInstance
  induction s using Finset.induction_on with
  | empty =>
    simp only [Finset.prod_empty, Finset.card_empty, Scheme.IdealSheafData.one_eq_top]
    exact ⟨Scheme.IdealSheafData.isInvertible_top, inferInstance,
      fun y => Scheme.Hom.finrank_eq_zero_of_isEmpty _ y⟩
  | insert j s hj ih =>
    obtain ⟨hJ, hfin, hdeg⟩ := ih
    have hq : (v j).1.ker.IsInvertible := Scheme.Hom.isInvertible_ker_of_comp_eq_id (v j).1 (v j).2
    obtain ⟨hfin1, hdeg1, -, -⟩ :=
      Scheme.Hom.isFinite_and_finrank_subschemeIota_ker_pow_of_comp_eq_id (v j).1 (v j).2 1
    rw [pow_one] at hfin1 hdeg1
    haveI := hfin; haveI := hfin1
    have H := fun y =>
      Scheme.IdealSheafData.IsInvertible.isFinite_and_finrank_mul_subscheme_comp_eq_add x 𝒱 hq hJ y
    rw [Finset.prod_insert hj, Finset.card_insert_of_notMem hj]
    refine ⟨hq.mul hJ, (H (IsLocalRing.closedPoint K)).1, fun y => ?_⟩
    rw [(H y).2, hdeg1 y, hdeg y, add_comm]

end AlgebraicGeometry.ChiFib

end

noncomputable section

namespace AlgebraicGeometry
p2m_export "AlgebraicGeometry" "Scheme.Hom.ker_comp_of_isIso Scheme.IdealSheafData.ideal_mul Scheme.Modules.Hom.zero_app SmoothOfRelativeDimension Scheme.IdealSheafData.one_eq_top IsProper Scheme.Modules.pullback Scheme.Hom GeometricallyIntegral Scheme.Modules.presheaf GeometricallyIrreducible Scheme.Modules.Hom IsFinite Spec IsIntegral Spec.map Scheme Scheme.Modules.Hom.app Scheme.IdealSheafData.comap_top Scheme.IdealSheafData.ker_fst_of_isClosedImmersion IsClosedImmersion IsSeparated Scheme.Modules.pullbackCongr Spec.map_id Scheme.Modules.pullbackId Scheme.Modules Scheme.IdealSheafData.ext Scheme.IdealSheafData Scheme.Modules.pullbackComp Scheme.IdealSheafData.ideal_comap_of_isOpenImmersion Scheme.Modules.IsInvertible Scheme.Modules.pullbackUnitIso Scheme.Modules.isInvertible_unit Scheme.TwoAffineOpenCover Scheme.TwoAffineOpenCover.specMap RelEffCartierDiv Scheme.IdealSheafData.IsInvertible Scheme.IdealSheafData.isInvertible_top graphOver prodKerGraph prodKerGraph_eq_prod Scheme.Hom.finrank_eq_zero_of_isEmpty Scheme.TwoAffineOpenCover.exists_linearEquiv_sectionsOf_H0 RelEffCartierDiv.exists_I_eq_prodKerGraph_of_isAlgClosed Scheme.TwoAffineOpenCover.exists_linearEquiv_sectionsOf_of_iso Scheme.TwoAffineOpenCover.finrank_H1_sectionsOf_unit_eq_and_finrank_H0_eq_one RelEffCartierDiv.exists_I_eq_zeroSchemeIdeal_of_eulerChar_eq Scheme.Hom.isInvertible_ker_of_comp_eq_id GeometricallyIrreducible.of_irreducibleSpace_of_isAlgClosed Scheme.IdealSheafData.IsInvertible.nonempty_pullback_invModule_iso Scheme.IdealSheafData.IsInvertible.eulerChar_sectionsOf_tensor_invModule_eq Scheme.Hom.isFinite_and_finrank_subschemeIota_ker_pow_of_comp_eq_id Scheme.IdealSheafData.IsInvertible.isFinite_and_finrank_mul_subscheme_comp_eq_add Scheme.TwoAffineOpenCover.finrank_cechDiff_baseChange_of_isAlgClosed geometricallyIntegral_of_isAlgClosed Scheme.IdealSheafData.IsInvertible.nonempty_module_tensor_invModule_iso"
namespace WrapB
p2m_open "AlgebraicGeometry"

theorem cover_ext {X : Scheme.{u}} {𝒱 𝒱' : X.TwoAffineOpenCover}
    (h0 : 𝒱.U0 = 𝒱'.U0) (h1 : 𝒱.U1 = 𝒱'.U1) : 𝒱 = 𝒱' := by
  cases 𝒱; cases 𝒱'; cases h0; cases h1; rfl

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

theorem exists_section_ne_zero {K : Type u} [Field K] {X : Scheme.{u}} (x : X ⟶ Spec (CommRingCat.of K))
    (𝒱 : X.TwoAffineOpenCover) (M : X.Modules) (h : Nontrivial (𝒱.sectionsOf x M).H0) :
    ∃ s : 𝟙_ X.Modules ⟶ M, s ≠ 0 := by
  obtain ⟨y, hy⟩ := exists_ne (0 : (𝒱.sectionsOf x M).H0)
  obtain ⟨eΓ, -⟩ := Scheme.TwoAffineOpenCover.exists_linearEquiv_sectionsOf_H0 𝒱 x M
  have hσ : eΓ.symm y ≠ 0 := fun h => hy (by rw [← eΓ.apply_symm_apply y, h, map_zero])
  exact exists_hom_ne_zero M (eΓ.symm y) hσ

end AlgebraicGeometry.WrapB

namespace AlgebraicGeometry p2m_export "AlgebraicGeometry" "Scheme.Hom.ker_comp_of_isIso Scheme.IdealSheafData.ideal_mul Scheme.Modules.Hom.zero_app SmoothOfRelativeDimension Scheme.IdealSheafData.one_eq_top IsProper Scheme.Modules.pullback Scheme.Hom GeometricallyIntegral Scheme.Modules.presheaf GeometricallyIrreducible Scheme.Modules.Hom IsFinite Spec IsIntegral Spec.map Scheme Scheme.Modules.Hom.app Scheme.IdealSheafData.comap_top Scheme.IdealSheafData.ker_fst_of_isClosedImmersion IsClosedImmersion IsSeparated Scheme.Modules.pullbackCongr Spec.map_id Scheme.Modules.pullbackId Scheme.Modules Scheme.IdealSheafData.ext Scheme.IdealSheafData Scheme.Modules.pullbackComp Scheme.IdealSheafData.ideal_comap_of_isOpenImmersion Scheme.Modules.IsInvertible Scheme.Modules.pullbackUnitIso Scheme.Modules.isInvertible_unit Scheme.TwoAffineOpenCover Scheme.TwoAffineOpenCover.specMap RelEffCartierDiv Scheme.IdealSheafData.IsInvertible Scheme.IdealSheafData.isInvertible_top graphOver prodKerGraph prodKerGraph_eq_prod Scheme.Hom.finrank_eq_zero_of_isEmpty Scheme.TwoAffineOpenCover.exists_linearEquiv_sectionsOf_H0 RelEffCartierDiv.exists_I_eq_prodKerGraph_of_isAlgClosed Scheme.TwoAffineOpenCover.exists_linearEquiv_sectionsOf_of_iso Scheme.TwoAffineOpenCover.finrank_H1_sectionsOf_unit_eq_and_finrank_H0_eq_one RelEffCartierDiv.exists_I_eq_zeroSchemeIdeal_of_eulerChar_eq Scheme.Hom.isInvertible_ker_of_comp_eq_id GeometricallyIrreducible.of_irreducibleSpace_of_isAlgClosed Scheme.IdealSheafData.IsInvertible.nonempty_pullback_invModule_iso Scheme.IdealSheafData.IsInvertible.eulerChar_sectionsOf_tensor_invModule_eq Scheme.Hom.isFinite_and_finrank_subschemeIota_ker_pow_of_comp_eq_id Scheme.IdealSheafData.IsInvertible.isFinite_and_finrank_mul_subscheme_comp_eq_add Scheme.TwoAffineOpenCover.finrank_cechDiff_baseChange_of_isAlgClosed geometricallyIntegral_of_isAlgClosed Scheme.IdealSheafData.IsInvertible.nonempty_module_tensor_invModule_iso" namespace Scheme p2m_export "AlgebraicGeometry.Scheme" "Hom.ker_comp_of_isIso IdealSheafData.ideal_mul Modules.Hom.zero_app ringCatSheaf IdealSheafData.one_eq_top Modules.pullback Hom Modules.presheaf Γ empty Hom.app Modules.Hom Modules.Hom.app functionField IdealSheafData.comap_top IdealSheafData.ker_fst_of_isClosedImmersion Modules.pullbackCongr Modules.pullbackId Modules Opens IdealSheafData.ext IdealSheafData Modules.pullbackComp Cover IdealSheafData.ideal_comap_of_isOpenImmersion Modules.IsInvertible Modules.pullbackUnitIso Modules.isInvertible_unit TwoAffineOpenCover TwoAffineOpenCover.specMap IdealSheafData.IsInvertible IdealSheafData.isInvertible_top Hom.finrank_eq_zero_of_isEmpty TwoAffineOpenCover.exists_linearEquiv_sectionsOf_H0 TwoAffineOpenCover.exists_linearEquiv_sectionsOf_of_iso TwoAffineOpenCover.finrank_H1_sectionsOf_unit_eq_and_finrank_H0_eq_one Hom.isInvertible_ker_of_comp_eq_id IdealSheafData.IsInvertible.nonempty_pullback_invModule_iso IdealSheafData.IsInvertible.eulerChar_sectionsOf_tensor_invModule_eq Hom.isFinite_and_finrank_subschemeIota_ker_pow_of_comp_eq_id IdealSheafData.IsInvertible.isFinite_and_finrank_mul_subscheme_comp_eq_add TwoAffineOpenCover.finrank_cechDiff_baseChange_of_isAlgClosed IdealSheafData.IsInvertible.nonempty_module_tensor_invModule_iso" namespace Modules p2m_export "AlgebraicGeometry.Scheme.Modules" "Hom.zero_app pullback presheaf Hom Hom.app pullbackCongr pullbackId pullbackComp IsInvertible pullbackUnitIso isInvertible_unit tensor" namespace IsInvertible p2m_export "AlgebraicGeometry.Scheme.Modules.IsInvertible" "pullback tensor" end AlgebraicGeometry.Scheme.Modules.IsInvertible
p2m_open_scoped "AlgebraicGeometry AlgebraicGeometry.Scheme AlgebraicGeometry.Scheme.Modules AlgebraicGeometry.Scheme.Modules.IsInvertible" in
open AlgebraicGeometry.WrapB in

theorem AlgebraicGeometry.Scheme.Modules.IsInvertible.exists_nonempty_pullback_fst_iso_invModule_prodKerGraph_of_eulerChar_eq
    (K : Type u) [Field K] [IsAlgClosed K] {X : Scheme.{u}} (x : X ⟶ Spec (CommRingCat.of K))
    [IsIntegral X] [IsProper x] [SmoothOfRelativeDimension 1 x]
    {M : X.Modules} (hM : Scheme.Modules.IsInvertible M) (𝒱 : X.TwoAffineOpenCover) (r : ℕ)
    (h0 : 0 < Module.finrank K (𝒱.sectionsOf x M).H0)
    (hχ : (Module.finrank K (𝒱.sectionsOf x M).H0 : ℤ) - Module.finrank K (𝒱.sectionsOf x M).H1 =
      (Module.finrank K (𝒱.sectionsOf x (𝟙_ X.Modules)).H0 : ℤ) -
        Module.finrank K (𝒱.sectionsOf x (𝟙_ X.Modules)).H1 + r) :
    ∃ (Pt : Fin r → (Spec (CommRingCat.of K) ⟶ X)) (hPt : ∀ m, Pt m ≫ x = 𝟙 _),
      (prodKerGraph x Pt hPt).IsInvertible ∧
      Nonempty ((Scheme.Modules.pullback (Limits.pullback.fst x (𝟙 (Spec (CommRingCat.of K))))).obj M ≅
        (prodKerGraph x Pt hPt).invModule) := by
  haveI : GeometricallyIrreducible x := GeometricallyIrreducible.of_irreducibleSpace_of_isAlgClosed x

  let φ : Limits.pullback x (𝟙 (Spec (CommRingCat.of K))) ≅ X := asIso (Limits.pullback.fst x (𝟙 _))
  have hφ : φ.hom ≫ x = Limits.pullback.snd x (𝟙 _) := by
    show Limits.pullback.fst x (𝟙 _) ≫ x = _
    rw [Limits.pullback.condition, Category.comp_id]
  let MY : (Limits.pullback x (𝟙 (Spec (CommRingCat.of K)))).Modules := (Scheme.Modules.pullback φ.hom).obj M
  have hMY : Scheme.Modules.IsInvertible MY := hM.pullback φ.hom

  obtain ⟨𝒱Y, hU0, hU1, ⟨e0⟩, ⟨e1⟩⟩ := Scheme.TwoAffineOpenCover.exists_linearEquiv_sectionsOf_of_iso
    (Limits.pullback.snd x (𝟙 _)) x φ hφ 𝒱 M MY (Iso.refl _)
  obtain ⟨𝒱Y', hU0', hU1', ⟨u0⟩, ⟨u1⟩⟩ := Scheme.TwoAffineOpenCover.exists_linearEquiv_sectionsOf_of_iso
    (Limits.pullback.snd x (𝟙 _)) x φ hφ 𝒱 (𝟙_ X.Modules) (𝟙_ (Limits.pullback x (𝟙 (Spec (CommRingCat.of K)))).Modules)
    (Scheme.Modules.pullbackUnitIso φ.hom).symm
  obtain rfl : 𝒱Y' = 𝒱Y := cover_ext (hU0'.trans hU0.symm) (hU1'.trans hU1.symm)

  have hnt : Nontrivial (𝒱Y'.sectionsOf (Limits.pullback.snd x (𝟙 _)) MY).H0 :=
    Module.nontrivial_of_finrank_pos (R := K) (by rw [e0.finrank_eq]; exact h0)
  obtain ⟨sY, hsY⟩ := exists_section_ne_zero (Limits.pullback.snd x (𝟙 _)) 𝒱Y' MY hnt
  have hχY : (Module.finrank K (𝒱Y'.sectionsOf (Limits.pullback.snd x (𝟙 _)) MY).H0 : ℤ) -
      Module.finrank K (𝒱Y'.sectionsOf (Limits.pullback.snd x (𝟙 _)) MY).H1 =
      (Module.finrank K (𝒱Y'.sectionsOf (Limits.pullback.snd x (𝟙 _))
          (𝟙_ (Limits.pullback x (𝟙 (Spec (CommRingCat.of K)))).Modules)).H0 : ℤ) -
        Module.finrank K (𝒱Y'.sectionsOf (Limits.pullback.snd x (𝟙 _))
          (𝟙_ (Limits.pullback x (𝟙 (Spec (CommRingCat.of K)))).Modules)).H1 + r := by
    rw [e0.finrank_eq, e1.finrank_eq, u0.finrank_eq, u1.finrank_eq]; exact hχ

  obtain ⟨D, -, ⟨eD, -⟩⟩ := RelEffCartierDiv.exists_I_eq_zeroSchemeIdeal_of_eulerChar_eq (f := x)
    (𝟙 _) hMY sY hsY 𝒱Y' r hχY
  obtain ⟨Pt, hPt, hDI⟩ := RelEffCartierDiv.exists_I_eq_prodKerGraph_of_isAlgClosed D
  refine ⟨Pt, hPt, hDI ▸ D.isInvertible_I, ⟨eD ≪≫ eqToIso ?_⟩⟩
  show D.I.invModule = _
  rw [hDI]

namespace WSM

theorem isInvertible_prod {X : Scheme.{u}} {ι : Type*} (s : Finset ι) (I : ι → X.IdealSheafData)
    (h : ∀ i ∈ s, (I i).IsInvertible) : (∏ i ∈ s, I i).IsInvertible := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using Scheme.IdealSheafData.isInvertible_top
  | insert a s ha ih =>
    rw [Finset.prod_insert ha]
    exact (h a (Finset.mem_insert_self a s)).mul (ih fun i hi => h i (Finset.mem_insert_of_mem hi))

theorem comap_mul_of_isIso {X Y : Scheme.{u}} (φ : Y ⟶ X) [IsIso φ] (I J : X.IdealSheafData) :
    (I * J).comap φ = I.comap φ * J.comap φ := by
  refine Scheme.IdealSheafData.ext (funext fun U => ?_)
  rw [Scheme.IdealSheafData.ideal_mul, Pi.mul_apply,
    Scheme.IdealSheafData.ideal_comap_of_isOpenImmersion, Scheme.IdealSheafData.ideal_comap_of_isOpenImmersion,
    Scheme.IdealSheafData.ideal_comap_of_isOpenImmersion, Scheme.IdealSheafData.ideal_mul, Pi.mul_apply]
  set e : Γ(Y, U) ≃+* Γ(X, φ ''ᵁ U) := (φ.appIso U).symm.commRingCatIsoToRingEquiv with he
  have hinv : (φ.appIso U).inv.hom = e.toRingHom := rfl
  rw [hinv]
  change Ideal.comap (e : Γ(Y, U) →+* Γ(X, φ ''ᵁ U)) _ =
    Ideal.comap (e : Γ(Y, U) →+* Γ(X, φ ''ᵁ U)) _ * Ideal.comap (e : Γ(Y, U) →+* Γ(X, φ ''ᵁ U)) _
  rw [Ideal.comap_coe, Ideal.comap_coe, Ideal.comap_coe, ← Ideal.map_symm, ← Ideal.map_symm, ← Ideal.map_symm,
    Ideal.map_mul]

theorem comap_prod_of_isIso {X Y : Scheme.{u}} (φ : Y ⟶ X) [IsIso φ] {ι : Type*} (s : Finset ι)
    (I : ι → X.IdealSheafData) : (∏ i ∈ s, I i).comap φ = ∏ i ∈ s, (I i).comap φ := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [Scheme.IdealSheafData.comap_top]
  | insert a s ha ih => rw [Finset.prod_insert ha, Finset.prod_insert ha, comap_mul_of_isIso, ih]

theorem ker_graphOver_eq_comap {K : Type u} [Field K] {X : Scheme.{u}} (x : X ⟶ Spec (CommRingCat.of K)) [IsSeparated x]
    (q : Spec (CommRingCat.of K) ⟶ X) (hq : q ≫ x = 𝟙 _) :
    (graphOver x q hq).ker = q.ker.comap (pullback.fst x (𝟙 (Spec (CommRingCat.of K)))) := by
  haveI : IsClosedImmersion (q ≫ x) := by rw [hq]; infer_instance
  haveI : IsClosedImmersion q := .of_comp q x
  set φ := pullback.fst x (𝟙 (Spec (CommRingCat.of K))) with hφ
  rw [← Scheme.IdealSheafData.ker_fst_of_isClosedImmersion q φ]

  let l : Spec (CommRingCat.of K) ⟶ pullback φ q := pullback.lift (graphOver x q hq) (𝟙 _) (by simp [hφ])
  have hl : l ≫ pullback.snd φ q = 𝟙 _ := pullback.lift_snd _ _ _
  haveI : IsIso l := IsIso.of_isIso_fac_right hl
  have hgl : graphOver x q hq = l ≫ pullback.fst φ q := (pullback.lift_fst _ _ _).symm
  rw [hgl, Scheme.Hom.ker_comp_of_isIso]

theorem prodKerGraph_eq_comap {K : Type u} [Field K] {X : Scheme.{u}} (x : X ⟶ Spec (CommRingCat.of K)) [IsSeparated x]
    {r : ℕ} (Pt : Fin r → (Spec (CommRingCat.of K) ⟶ X)) (hPt : ∀ m, Pt m ≫ x = 𝟙 _) :
    prodKerGraph x Pt hPt = (∏ m, (Pt m).ker).comap (pullback.fst x (𝟙 (Spec (CommRingCat.of K)))) := by
  rw [prodKerGraph_eq_prod, comap_prod_of_isIso]
  exact Finset.prod_congr rfl fun m _ => ker_graphOver_eq_comap x (Pt m) (hPt m)

private def _root_.WSM.pullbackUnitIso {X Y : Scheme.{u}} (φ : Y ≅ X) (N : X.Modules) :
    N ≅ (Scheme.Modules.pullback φ.inv).obj ((Scheme.Modules.pullback φ.hom).obj N) :=
  ((Scheme.Modules.pullbackId X).app N).symm ≪≫
    (Scheme.Modules.pullbackCongr φ.inv_hom_id.symm).app N ≪≫
    ((Scheme.Modules.pullbackComp φ.inv φ.hom).app N).symm

p2m_export "WSM" "pullbackUnitIso"

def isoOfPullbackIso {X Y : Scheme.{u}} (φ : Y ≅ X) {M N : X.Modules}
    (e : (Scheme.Modules.pullback φ.hom).obj M ≅ (Scheme.Modules.pullback φ.hom).obj N) : M ≅ N :=
  pullbackUnitIso φ M ≪≫ (Scheme.Modules.pullback φ.inv).mapIso e ≪≫ (pullbackUnitIso φ N).symm

end WSM

p2m_open_scoped "AlgebraicGeometry AlgebraicGeometry.Scheme AlgebraicGeometry.Scheme.Modules AlgebraicGeometry.Scheme.Modules.IsInvertible" in

theorem AlgebraicGeometry.Scheme.Modules.IsInvertible.exists_nonempty_iso_invModule_prod_ker_of_eulerChar_eq
    (K : Type u) [Field K] [IsAlgClosed K] {X : Scheme.{u}} (x : X ⟶ Spec (CommRingCat.of K))
    [IsIntegral X] [IsProper x] [SmoothOfRelativeDimension 1 x]
    {M : X.Modules} (hM : Scheme.Modules.IsInvertible M) (𝒱 : X.TwoAffineOpenCover) (r : ℕ)
    (h0 : 0 < Module.finrank K (𝒱.sectionsOf x M).H0)
    (hχ : (Module.finrank K (𝒱.sectionsOf x M).H0 : ℤ) - Module.finrank K (𝒱.sectionsOf x M).H1 =
      (Module.finrank K (𝒱.sectionsOf x (𝟙_ X.Modules)).H0 : ℤ) - Module.finrank K (𝒱.sectionsOf x (𝟙_ X.Modules)).H1 + r) :
    ∃ P : Fin r → {q : Spec (CommRingCat.of K) ⟶ X // q ≫ x = 𝟙 _}, Nonempty (M ≅ (∏ m, (P m).1.ker).invModule) := by
  classical
  haveI : IsSeparated x := inferInstance
  obtain ⟨Pt, hPt, hPK, ⟨eY⟩⟩ :=
    Scheme.Modules.IsInvertible.exists_nonempty_pullback_fst_iso_invModule_prodKerGraph_of_eulerChar_eq
      K x hM 𝒱 r h0 hχ
  refine ⟨fun m => ⟨Pt m, hPt m⟩, ?_⟩
  let φ : Limits.pullback x (𝟙 (Spec (CommRingCat.of K))) ≅ X :=
    asIso (Limits.pullback.fst x (𝟙 (Spec (CommRingCat.of K))))

  have hI : (∏ m, (Pt m).ker).IsInvertible :=
    WSM.isInvertible_prod Finset.univ (fun m => (Pt m).ker)
      fun m _ => Scheme.Hom.isInvertible_ker_of_comp_eq_id (Pt m) (hPt m)
  have hcomap : (∏ m, (Pt m).ker).comap φ.hom = prodKerGraph x Pt hPt :=
    (WSM.prodKerGraph_eq_comap x Pt hPt).symm
  have hI' : ((∏ m, (Pt m).ker).comap φ.hom).IsInvertible := by
    rw [hcomap]; exact hPK
  obtain ⟨e93⟩ := Scheme.IdealSheafData.IsInvertible.nonempty_pullback_invModule_iso φ.hom hI hI'
  have e₁ : (Scheme.Modules.pullback φ.hom).obj M ≅ (Scheme.Modules.pullback φ.hom).obj (∏ m, (Pt m).ker).invModule :=
    eY ≪≫ eqToIso (by rw [hcomap]) ≪≫ e93.symm
  exact ⟨WSM.isoOfPullbackIso φ e₁⟩

namespace WSM

theorem cover_ext {X : Scheme.{u}} {𝒱 𝒱' : X.TwoAffineOpenCover}
    (h0 : 𝒱.U0 = 𝒱'.U0) (h1 : 𝒱.U1 = 𝒱'.U1) : 𝒱 = 𝒱' := by
  cases 𝒱; cases 𝒱'; cases h0; cases h1; rfl

theorem nonempty_linearEquiv_of_iso {R : Type u} [CommRing R] {X : Scheme.{u}} (x : X ⟶ Spec (CommRingCat.of R))
    (𝒱 : X.TwoAffineOpenCover) {M M' : X.Modules} (e : M ≅ M') :
    Nonempty ((𝒱.sectionsOf x M).H0 ≃ₗ[R] (𝒱.sectionsOf x M').H0) ∧
      Nonempty ((𝒱.sectionsOf x M).H1 ≃ₗ[R] (𝒱.sectionsOf x M').H1) := by
  obtain ⟨𝒱₂, h0, h1, ⟨e0⟩, ⟨e1⟩⟩ :=
    Scheme.TwoAffineOpenCover.exists_linearEquiv_sectionsOf_of_iso x x (Iso.refl X) (Category.id_comp x)
      𝒱 M' M (e ≪≫ ((Scheme.Modules.pullbackId X).app M').symm)
  obtain rfl : 𝒱₂ = 𝒱 := cover_ext h0 h1
  exact ⟨⟨e0⟩, ⟨e1⟩⟩

end WSM

namespace AlgebraicGeometry
p2m_export "AlgebraicGeometry" "Scheme.Hom.ker_comp_of_isIso Scheme.IdealSheafData.ideal_mul Scheme.Modules.Hom.zero_app SmoothOfRelativeDimension Scheme.IdealSheafData.one_eq_top IsProper Scheme.Modules.pullback Scheme.Hom GeometricallyIntegral Scheme.Modules.presheaf GeometricallyIrreducible Scheme.Modules.Hom IsFinite Spec IsIntegral Spec.map Scheme Scheme.Modules.Hom.app Scheme.IdealSheafData.comap_top Scheme.IdealSheafData.ker_fst_of_isClosedImmersion IsClosedImmersion IsSeparated Scheme.Modules.pullbackCongr Spec.map_id Scheme.Modules.pullbackId Scheme.Modules Scheme.IdealSheafData.ext Scheme.IdealSheafData Scheme.Modules.pullbackComp Scheme.IdealSheafData.ideal_comap_of_isOpenImmersion Scheme.Modules.IsInvertible Scheme.Modules.pullbackUnitIso Scheme.Modules.isInvertible_unit Scheme.TwoAffineOpenCover Scheme.TwoAffineOpenCover.specMap RelEffCartierDiv Scheme.IdealSheafData.IsInvertible Scheme.IdealSheafData.isInvertible_top graphOver prodKerGraph prodKerGraph_eq_prod Scheme.Hom.finrank_eq_zero_of_isEmpty Scheme.TwoAffineOpenCover.exists_linearEquiv_sectionsOf_H0 RelEffCartierDiv.exists_I_eq_prodKerGraph_of_isAlgClosed Scheme.TwoAffineOpenCover.exists_linearEquiv_sectionsOf_of_iso Scheme.TwoAffineOpenCover.finrank_H1_sectionsOf_unit_eq_and_finrank_H0_eq_one RelEffCartierDiv.exists_I_eq_zeroSchemeIdeal_of_eulerChar_eq Scheme.Hom.isInvertible_ker_of_comp_eq_id GeometricallyIrreducible.of_irreducibleSpace_of_isAlgClosed Scheme.IdealSheafData.IsInvertible.nonempty_pullback_invModule_iso Scheme.IdealSheafData.IsInvertible.eulerChar_sectionsOf_tensor_invModule_eq Scheme.Hom.isFinite_and_finrank_subschemeIota_ker_pow_of_comp_eq_id Scheme.IdealSheafData.IsInvertible.isFinite_and_finrank_mul_subscheme_comp_eq_add Scheme.TwoAffineOpenCover.finrank_cechDiff_baseChange_of_isAlgClosed geometricallyIntegral_of_isAlgClosed Scheme.IdealSheafData.IsInvertible.nonempty_module_tensor_invModule_iso"
namespace K6Impl
p2m_open "AlgebraicGeometry"

variable {K : Type u} [Field K] [IsAlgClosed K] {X : Scheme.{u}} (x : X ⟶ Spec (CommRingCat.of K))

theorem eulerChar_tensor_module_prod_ker [IsProper x] [SmoothOfRelativeDimension 1 x]
    (𝒱 : X.TwoAffineOpenCover) (N : X.Modules) (hN : Scheme.Modules.IsInvertible N)
    {n : ℕ} (Q : Fin n → {q : Spec (CommRingCat.of K) ⟶ X // q ≫ x = 𝟙 _}) :
    (Module.finrank K (𝒱.sectionsOf x (N ⊗ (∏ j, (Q j).1.ker).module)).H0 : ℤ)
        - Module.finrank K (𝒱.sectionsOf x (N ⊗ (∏ j, (Q j).1.ker).module)).H1
      = (Module.finrank K (𝒱.sectionsOf x N).H0 : ℤ) - Module.finrank K (𝒱.sectionsOf x N).H1 - n := by
  classical
  haveI : IsSeparated x := inferInstance
  obtain ⟨hJ, hJfin, hJdeg⟩ := AlgebraicGeometry.ChiFib.prod_ker x 𝒱 Q Finset.univ
  have hdegn : ∀ y, ((∏ j, (Q j).1.ker).subschemeι ≫ x).finrank y = n := fun y => by
    rw [hJdeg y, Finset.card_univ, Fintype.card_fin]
  have hNJ : Scheme.Modules.IsInvertible (N ⊗ (∏ j, (Q j).1.ker).module) := hN.tensor hJ.isInvertible_module
  have hB := Scheme.IdealSheafData.IsInvertible.eulerChar_sectionsOf_tensor_invModule_eq x hJ hJfin hdegn
    (N ⊗ (∏ j, (Q j).1.ker).module) hNJ 𝒱
  obtain ⟨⟨eN⟩, -⟩ := Scheme.IdealSheafData.IsInvertible.nonempty_module_tensor_invModule_iso hJ
  have hB' := AlgebraicGeometry.ChiFib.eulerChar_congr x 𝒱
    (α_ N ((∏ j, (Q j).1.ker).module) ((∏ j, (Q j).1.ker).invModule) ≪≫ whiskerLeftIso N eN ≪≫ ρ_ N)
  omega

theorem eulerChar_tensor_invModule_prod_ker [IsProper x] [SmoothOfRelativeDimension 1 x]
    (𝒱 : X.TwoAffineOpenCover) (N : X.Modules) (hN : Scheme.Modules.IsInvertible N)
    {t : ℕ} (w : Fin t → {q : Spec (CommRingCat.of K) ⟶ X // q ≫ x = 𝟙 _}) :
    (Module.finrank K (𝒱.sectionsOf x (N ⊗ (∏ l, (w l).1.ker).invModule)).H0 : ℤ)
        - Module.finrank K (𝒱.sectionsOf x (N ⊗ (∏ l, (w l).1.ker).invModule)).H1
      = (Module.finrank K (𝒱.sectionsOf x N).H0 : ℤ) - Module.finrank K (𝒱.sectionsOf x N).H1 + t := by
  classical
  haveI : IsSeparated x := inferInstance
  obtain ⟨hJ, hJfin, hJdeg⟩ := AlgebraicGeometry.ChiFib.prod_ker x 𝒱 w Finset.univ
  have hdegt : ∀ y, ((∏ l, (w l).1.ker).subschemeι ≫ x).finrank y = t := fun y => by
    rw [hJdeg y, Finset.card_univ, Fintype.card_fin]
  exact Scheme.IdealSheafData.IsInvertible.eulerChar_sectionsOf_tensor_invModule_eq x hJ hJfin hdegt N hN 𝒱

end AlgebraicGeometry.K6Impl

end

open AlgebraicGeometry.K6Impl AlgebraicGeometry.WrapB in
theorem solution
    (K : Type u) [Field K] [IsAlgClosed K] {X : Scheme.{u}} (x : X ⟶ Spec (CommRingCat.of K))
    [IsIntegral X] [IsProper x] [SmoothOfRelativeDimension 1 x]
    (γ : ℕ) (𝒱₀ : X.TwoAffineOpenCover)
    (hγ : Module.finrank K (𝒱₀.sectionsOf x (SheafOfModules.unit X.ringCatSheaf)).H1 = γ)
    (L : X.Modules) (hL : Scheme.Modules.IsInvertible L) (h0 : IsAlgEquivZero x L)

    {t : ℕ} (w : Fin t → {q : Spec (CommRingCat.of K) ⟶ X // q ≫ x = 𝟙 _})

    {N : ℕ} (S : Fin N → Finset {q : Spec (CommRingCat.of K) ⟶ X // q ≫ x = 𝟙 _}) (e : ℕ)
    (hS : ∀ κ, 2 * γ + (S κ).card ≤ t + 1) (heS : ∀ κ, e + (S κ).card + γ ≤ t + 1)

    {ι : Type*} [Fintype ι] [DecidableEq ι] (B : ι → Finset {q : Spec (CommRingCat.of K) ⟶ X // q ≫ x = 𝟙 _})
    (hdisj : ∀ i i', i ≠ i' → Disjoint (B i) (B i'))
    {b : ℕ} (hb1 : 1 ≤ b) (hb : ∀ i, (B i).card ≤ b)
    (hcard : N * t * b ^ e + e < Fintype.card ι) :
    ∃ a : Fin e → ι, Function.Injective a ∧
      ∀ v : Fin e → {q : Spec (CommRingCat.of K) ⟶ X // q ≫ x = 𝟙 _}, (∀ j, v j ∈ B (a j)) →
        ∀ κ, ∀ 𝒱 : X.TwoAffineOpenCover,
          Module.finrank K (𝒱.sectionsOf x
              (L ⊗ ((∏ l, (w l).1.ker).invModule ⊗ ((∏ j, (v j).1.ker) * ∏ p ∈ S κ, p.1.ker).module))).H0
            + e + (S κ).card + γ = t + 1 ∧
          Subsingleton (𝒱.sectionsOf x
              (L ⊗ ((∏ l, (w l).1.ker).invModule ⊗ ((∏ j, (v j).1.ker) * ∏ p ∈ S κ, p.1.ker).module))).H1 := by
  classical
  haveI : IsSeparated x := inferInstance

  obtain ⟨hgU, F, _, _, Mdl, eM, heM, Kc, hRR⟩ := AlgebraicGeometry.ChiFibGenus.rr_of_cech K x γ 𝒱₀ hγ
  haveI : IsCurveOver K F :=
    isCurveOver_of_ringEquiv_functionField_of_isIntegral_of_smoothOfRelativeDimension_one
      Mdl.toBase Mdl.ffEquiv Mdl.ffEquiv_algebraMap
  have hKc : Divisor.degree Kc = 2 * (γ : ℤ) - 2 := by
    have h0 := hRR 0
    have h1 := hRR Kc
    rw [sub_zero, map_zero] at h0
    rw [sub_self] at h1
    linarith

  let pl : {q : Spec (CommRingCat.of K) ⟶ X // q ≫ x = 𝟙 _} → Place K F := fun q =>
    Mdl.pointEquivPlace ⟨q.1 ≫ eM.inv, by rw [Category.assoc, ← heM, eM.inv_hom_id_assoc]; exact q.2⟩
  have hpl : Function.Injective pl := by
    intro q q' h
    have h1 := Mdl.pointEquivPlace.injective h
    have h2 : q.1 ≫ eM.inv = q'.1 ≫ eM.inv := congrArg Subtype.val h1
    exact Subtype.ext ((cancel_mono eM.inv).mp h2)
  have hpl1 : ∀ q, (pl q).deg = 1 := fun q => IsCurveOver.deg_eq_one_of_isAlgClosed (pl q)
  have hdegsum : ∀ (s : Finset {q : Spec (CommRingCat.of K) ⟶ X // q ≫ x = 𝟙 _}),
      Divisor.degree (∑ q ∈ s, Finsupp.single (pl q) (1 : ℤ)) = s.card := fun s => by
    rw [map_sum, Finset.sum_congr rfl fun q _ => by rw [Divisor.degree_single, hpl1, Nat.cast_one, mul_one]]
    simp
  have hdegsumFin : ∀ {m : ℕ} (f : Fin m → {q : Spec (CommRingCat.of K) ⟶ X // q ≫ x = 𝟙 _}),
      Divisor.degree (∑ j, Finsupp.single (pl (f j)) (1 : ℤ)) = m := fun f => by
    rw [map_sum, Finset.sum_congr rfl fun j _ => by rw [Divisor.degree_single, hpl1, Nat.cast_one, mul_one]]
    simp

  rcases Nat.eq_zero_or_pos N with hN0 | hNpos
  · subst hN0
    let B' : ι → Finset (Place K F) := fun i => (B i).image pl
    obtain ⟨a, ha, -⟩ :=
      AlgebraicCurve.RROpens.exists_injective_forall_forall_mem_ell_sub_sum_single_add_eq_ell_of_lt_card
        (Fin.elim0 : Fin 0 → Divisor K F) e t (fun k => Fin.elim0 k) (fun k => Fin.elim0 k) B'
        (fun i w _ => IsCurveOver.deg_eq_one_of_isAlgClosed w)
        (fun i i' hne => (Finset.disjoint_image hpl).mpr (hdisj i i' hne)) hb1
        (fun i => by rw [Finset.card_image_of_injective _ hpl]; exact hb i) hcard
    exact ⟨a, ha, fun v _ κ => Fin.elim0 κ⟩

  have hκ₀ := hS ⟨0, hNpos⟩
  have hwk : ∀ l, (w l).1.ker.IsInvertible := fun l => Scheme.Hom.isInvertible_ker_of_comp_eq_id (w l).1 (w l).2
  have hTI : (∏ l, (w l).1.ker).IsInvertible :=
    WSM.isInvertible_prod Finset.univ (fun l => (w l).1.ker) fun l _ => hwk l
  have hT : Scheme.Modules.IsInvertible (∏ l, (w l).1.ker).invModule := hTI.isInvertible_invModule
  have hLT : Scheme.Modules.IsInvertible (L ⊗ (∏ l, (w l).1.ker).invModule) := hL.tensor hT
  obtain ⟨hH1u, hH0u⟩ := Scheme.TwoAffineOpenCover.finrank_H1_sectionsOf_unit_eq_and_finrank_H0_eq_one K x γ hgU 𝒱₀
  change Module.finrank K (𝒱₀.sectionsOf x (𝟙_ X.Modules)).H1 = γ at hH1u
  change Module.finrank K (𝒱₀.sectionsOf x (𝟙_ X.Modules)).H0 = 1 at hH0u

  have hχ1 := IsAlgEquivZero.eulerChar_sectionsOf_tensor_eq x 𝒱₀ L ((∏ l, (w l).1.ker).invModule) hL hT h0
  have hχ2 := eulerChar_tensor_invModule_prod_ker x 𝒱₀ (𝟙_ X.Modules) (Scheme.Modules.isInvertible_unit X) w
  have hχ3 := AlgebraicGeometry.ChiFib.eulerChar_congr x 𝒱₀ (λ_ ((∏ l, (w l).1.ker).invModule))
  have hχLT : (Module.finrank K (𝒱₀.sectionsOf x (L ⊗ (∏ l, (w l).1.ker).invModule)).H0 : ℤ)
        - Module.finrank K (𝒱₀.sectionsOf x (L ⊗ (∏ l, (w l).1.ker).invModule)).H1
      = (Module.finrank K (𝒱₀.sectionsOf x (𝟙_ X.Modules)).H0 : ℤ)
        - Module.finrank K (𝒱₀.sectionsOf x (𝟙_ X.Modules)).H1 + t := by
    rw [hχ1, ← hχ3, hχ2]
  have hpos : 0 < Module.finrank K (𝒱₀.sectionsOf x (L ⊗ (∏ l, (w l).1.ker).invModule)).H0 := by
    rw [hH1u, hH0u] at hχLT
    have : (0 : ℤ) < Module.finrank K (𝒱₀.sectionsOf x (L ⊗ (∏ l, (w l).1.ker).invModule)).H0 := by
      have h1 : (0 : ℤ) ≤ Module.finrank K (𝒱₀.sectionsOf x (L ⊗ (∏ l, (w l).1.ker).invModule)).H1 :=
        Int.natCast_nonneg _
      omega
    exact_mod_cast this

  obtain ⟨Pt, ⟨eE⟩⟩ :=
    Scheme.Modules.IsInvertible.exists_nonempty_iso_invModule_prod_ker_of_eulerChar_eq K x hLT 𝒱₀ t hpos hχLT

  let E : Divisor K F := ∑ m, Finsupp.single (pl (Pt m)) (1 : ℤ)
  let D : Fin N → Divisor K F := fun κ => E - ∑ q ∈ S κ, Finsupp.single (pl q) (1 : ℤ)
  have hdegD : ∀ κ, Divisor.degree (D κ) = t - (S κ).card := fun κ => by
    show Divisor.degree (E - _) = _
    rw [map_sub, hdegsum, show Divisor.degree E = t from hdegsumFin Pt]
  have hellD : ∀ κ, (ell (D κ) : ℤ) = t - (S κ).card + 1 - γ := fun κ => by
    have hz : ell (Kc - D κ) = 0 :=
      ell_eq_zero_of_degree_neg (by rw [map_sub, hKc, hdegD κ]; have := hS κ; omega)
    have h := hRR (D κ)
    rw [hz, hdegD κ] at h
    push_cast at h
    linarith

  let B' : ι → Finset (Place K F) := fun i => (B i).image pl
  obtain ⟨a, ha, hK0⟩ :=
    AlgebraicCurve.RROpens.exists_injective_forall_forall_mem_ell_sub_sum_single_add_eq_ell_of_lt_card
      D e t (fun κ => by have := hellD κ; have := heS κ; omega) (fun κ => by rw [hdegD κ]; omega) B'
      (fun i w _ => IsCurveOver.deg_eq_one_of_isAlgClosed w)
      (fun i i' hne => (Finset.disjoint_image hpl).mpr (hdisj i i' hne)) hb1
      (fun i => by rw [Finset.card_image_of_injective _ hpl]; exact hb i) hcard
  refine ⟨a, ha, fun v hv κ 𝒱 => ?_⟩

  let sE : Fin (S κ).card → {q : Spec (CommRingCat.of K) ⟶ X // q ≫ x = 𝟙 _} := fun i => ((S κ).equivFin.symm i : _)
  let Q : Fin (e + (S κ).card) → {q : Spec (CommRingCat.of K) ⟶ X // q ≫ x = 𝟙 _} := Fin.append v sE
  have hprodS : ∏ i, (sE i).1.ker = ∏ q ∈ S κ, q.1.ker := by
    rw [← Finset.prod_coe_sort (S κ)]
    exact Fintype.prod_equiv (S κ).equivFin.symm (fun i => (sE i).1.ker) (fun q => q.1.1.ker) (fun i => rfl)
  have hsumS : ∑ i, Finsupp.single (pl (sE i)) (1 : ℤ) = ∑ q ∈ S κ, Finsupp.single (pl q) (1 : ℤ) := by
    rw [← Finset.sum_coe_sort (S κ)]
    exact Fintype.sum_equiv (S κ).equivFin.symm (fun i => Finsupp.single (pl (sE i)) (1 : ℤ))
      (fun q => Finsupp.single (pl q.1) (1 : ℤ)) (fun i => rfl)
  have hQprod : ∏ j, (Q j).1.ker = (∏ j, (v j).1.ker) * ∏ q ∈ S κ, q.1.ker := by
    rw [Fin.prod_univ_add]
    simp only [Q, Fin.append_left, Fin.append_right]
    rw [hprodS]
  have hQsum : ∑ j, Finsupp.single (pl (Q j)) (1 : ℤ) =
      ∑ j, Finsupp.single (pl (v j)) (1 : ℤ) + ∑ q ∈ S κ, Finsupp.single (pl q) (1 : ℤ) := by
    rw [Fin.sum_univ_add]
    simp only [Q, Fin.append_left, Fin.append_right]
    rw [hsumS]

  have hNI : (∏ j, (Q j).1.ker).IsInvertible :=
    WSM.isInvertible_prod Finset.univ (fun j => (Q j).1.ker)
      fun j _ => Scheme.Hom.isInvertible_ker_of_comp_eq_id (Q j).1 (Q j).2
  have hPI : (∏ m, (Pt m).1.ker).IsInvertible :=
    WSM.isInvertible_prod Finset.univ (fun m => (Pt m).1.ker)
      fun m _ => Scheme.Hom.isInvertible_ker_of_comp_eq_id (Pt m).1 (Pt m).2
  let eMN : L ⊗ ((∏ l, (w l).1.ker).invModule ⊗ ((∏ j, (v j).1.ker) * ∏ p ∈ S κ, p.1.ker).module) ≅
      (∏ m, (Pt m).1.ker).invModule ⊗ (∏ j, (Q j).1.ker).module :=
    (α_ L ((∏ l, (w l).1.ker).invModule) (((∏ j, (v j).1.ker) * ∏ p ∈ S κ, p.1.ker).module)).symm ≪≫
      whiskerRightIso eE _ ≪≫ eqToIso (by rw [hQprod])
  obtain ⟨⟨k0⟩, ⟨k1⟩⟩ := WSM.nonempty_linearEquiv_of_iso x 𝒱 eMN

  obtain ⟨fin0, fin1, hrk⟩ :=
    AlgebraicCurve.CurveModel.finrank_H0_sectionsOf_invModule_prod_ker_tensor_module_prod_ker_eq_ell
      x Mdl eM heM Pt Q 𝒱
  have hmem : ∀ j, pl (v j) ∈ B' (a j) := fun j => Finset.mem_image_of_mem pl (hv j)
  have hdrop := hK0 κ (fun j => pl (v j)) hmem
  have hellQ : ell ((∑ m, Finsupp.single (pl (Pt m)) (1 : ℤ)) - ∑ j, Finsupp.single (pl (Q j)) (1 : ℤ)) + e
      = ell (D κ) := by
    rw [hQsum, show (∑ m, Finsupp.single (pl (Pt m)) (1 : ℤ)) -
        (∑ j, Finsupp.single (pl (v j)) (1 : ℤ) + ∑ q ∈ S κ, Finsupp.single (pl q) (1 : ℤ))
        = D κ - ∑ j, Finsupp.single (pl (v j)) (1 : ℤ) from by simp only [D, E]; abel]
    exact hdrop
  have hH0 : (Module.finrank K (𝒱.sectionsOf x
      (L ⊗ ((∏ l, (w l).1.ker).invModule ⊗ ((∏ j, (v j).1.ker) * ∏ p ∈ S κ, p.1.ker).module))).H0 : ℤ)
        + e + (S κ).card + γ = t + 1 := by
    have hrk' : Module.finrank K (𝒱.sectionsOf x ((∏ m, (Pt m).1.ker).invModule ⊗ (∏ j, (Q j).1.ker).module)).H0
        = ell ((∑ m, Finsupp.single (pl (Pt m)) (1 : ℤ)) - ∑ j, Finsupp.single (pl (Q j)) (1 : ℤ)) := hrk
    rw [k0.finrank_eq, hrk']
    have := hellD κ
    have h2 : ((ell ((∑ m, Finsupp.single (pl (Pt m)) (1 : ℤ)) - ∑ j, Finsupp.single (pl (Q j)) (1 : ℤ)) : ℕ) : ℤ)
        + e = ell (D κ) := by exact_mod_cast hellQ
    have := hS κ
    omega
  refine ⟨by exact_mod_cast hH0, ?_⟩

  haveI : Module.Finite K (𝒱.sectionsOf x
      (L ⊗ ((∏ l, (w l).1.ker).invModule ⊗ ((∏ j, (v j).1.ker) * ∏ p ∈ S κ, p.1.ker).module))).H1 :=
    Module.Finite.equiv k1.symm
  have hχa := AlgebraicGeometry.ChiFib.eulerChar_congr x 𝒱 eMN
  have hχb := eulerChar_tensor_module_prod_ker x 𝒱 ((∏ m, (Pt m).1.ker).invModule) hPI.isInvertible_invModule Q
  have hχc := eulerChar_tensor_invModule_prod_ker x 𝒱 (𝟙_ X.Modules) (Scheme.Modules.isInvertible_unit X) Pt
  have hχd := AlgebraicGeometry.ChiFib.eulerChar_congr x 𝒱 (λ_ ((∏ m, (Pt m).1.ker).invModule))
  obtain ⟨hH1u', hH0u'⟩ := Scheme.TwoAffineOpenCover.finrank_H1_sectionsOf_unit_eq_and_finrank_H0_eq_one K x γ hgU 𝒱
  change Module.finrank K (𝒱.sectionsOf x (𝟙_ X.Modules)).H1 = γ at hH1u'
  change Module.finrank K (𝒱.sectionsOf x (𝟙_ X.Modules)).H0 = 1 at hH0u'
  have hM1 : Module.finrank K (𝒱.sectionsOf x
      (L ⊗ ((∏ l, (w l).1.ker).invModule ⊗ ((∏ j, (v j).1.ker) * ∏ p ∈ S κ, p.1.ker).module))).H1 = 0 := by
    omega
  exact Module.finrank_zero_iff.mp hM1

end S_AlgebraicGeometry_RelPicard_exists_injective_forall_finrank_H0_add_eq_and_subsingleton_H1_of_blocks_of_isAlgEquivZero_of_lt_card
end P2MW
export P2MW.S_AlgebraicGeometry_RelPicard_exists_injective_forall_finrank_H0_add_eq_and_subsingleton_H1_of_blocks_of_isAlgEquivZero_of_lt_card (solution)
