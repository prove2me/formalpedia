-- Prove2me | solution 1 for AlgebraicGeometry.Polarisation.memKernel_tpow_tensor_tpow_pullback_negMor_iff_memKernel_nsmul_add
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:02.935278+00:00
-- url     : https://prove2.me/submissions/3a213c1e-8a58-5a1e-b5b3-b21a86be5874

import Mathlib
import Definitions.Def_AlgebraicGeometry_PolarisedAbelianSchemeOfType
import Definitions.Def_AlgebraicGeometry_PolarisationRosati
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import Definitions.Def_AlgebraicGeometry_ModulesPullbackMonoidalV2
import Theorems.Thm_AlgebraicGeometry_Polarisation_nonempty_pullback_sliceAt_mumfordBundle_tensor_iso_of_commRing
import Theorems.Thm_AlgebraicGeometry_Polarisation_nonempty_pullback_sliceAt_mumfordBundle_pullback_negMor_iso_of_commRing
import Theorems.Thm_AlgebraicGeometry_Polarisation_locIsoOnBase_pullback_negMor_prod_sliceAt_mumfordBundle_dual_of_commRing
import Theorems.Thm_AlgebraicGeometry_Polarisation_locIsoOnBase_sliceAt_mumfordBundle_inv_dual_of_commRing
import Theorems.Thm_AlgebraicGeometry_Polarisation_locIsoOnBase_sliceAt_mumfordBundle_mul_tensor_of_commRing
import Theorems.Thm_AlgebraicGeometry_Polarisation_locIsoOnBase_pullback_sliceAt_mumfordBundle_one_unit_of_commRing
import Theorems.Thm_AlgebraicGeometry_Polarisation_LocIsoOnBase_tensor
import Theorems.Thm_AlgebraicGeometry_Polarisation_LocIsoOnBase_equivalence
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_IsInvertible_dual_monoidalV2
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_IsInvertible_pullback_dual_monoidalV2
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_IsInvertible_tensor_monoidalV2
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_Polarisation_memKernel_tpow_tensor_tpow_pullback_negMor_iff_memKernel_nsmul_add
p2m_attr_erase "instance" "TwoChartCech.Sections.M0_moduleA TwoChartCech.Sections.M1_module TwoChartCech.Cover.A01_algebra TwoChartCech.Cover.A0_algebra TwoChartCech.Cover.A1_commRing TwoChartCech.Cover.A1_algebra TwoChartCech.Sections.M01_module TwoChartCech.Sections.M0_addCommGroup TwoChartCech.Sections.M0_tower TwoChartCech.Sections.M01_addCommGroup TwoChartCech.Cover.A0_commRing TwoChartCech.Sections.M1_tower TwoChartCech.Sections.M01_moduleA TwoChartCech.Sections.M0_module TwoChartCech.Sections.M1_moduleA TwoChartCech.Sections.M1_addCommGroup TwoChartCech.Cover.A01_commRing TwoChartCech.Sections.M01_tower CoherentBaseChange.TwoTermComplex.C0_module CoherentBaseChange.TwoTermComplex.C0_addCommGroup CoherentBaseChange.TwoTermComplex.C1_module CoherentBaseChange.TwoTermComplex.C1_addCommGroup CoherentBaseChange.TwoTermComplex.C0_free CoherentBaseChange.TwoTermComplex.C1_finite CoherentBaseChange.TwoTermComplex.C0_finite CoherentBaseChange.TwoTermComplex.C1_free AlgebraicGeometry.SubalgebraStages.compactSpace_pullback AlgebraicGeometry.SubalgebraStages.quasiSeparatedSpace_pullback AlgebraicGeometry.SubalgebraStages.compactSpace_obj AlgebraicGeometry.SubalgebraStages.quasiSeparatedSpace_obj AlgebraicGeometry.SubalgebraStages.quasiCompact_snd AlgebraicGeometry.SubalgebraStages.isAffineHom_leg AlgebraicGeometry.SubalgebraStages.isAffineHom_trans AlgebraicGeometry.SubalgebraStages.isAffineHom_diagram_map AlgebraicGeometry.SubalgebraStages.quasiSeparated_snd AlgebraicGeometry.SubalgebraStages.isCofiltered_op IsDirectLimit.Module.instDirectLimitCoeLinearMapIdOfOfNonempty AdicCompletion.instIsLocalRingMaximalIdeal AlgebraicGeometry.OModulePresheaf.isScalarTower AlgebraicGeometry.Scheme.OrderedAffineCover.instLinearOrder"
p2m_attr_erase "instance" "AlgebraicGeometry.OModulePresheaf.module AlgebraicGeometry.Scheme.OrderedAffineCover.instFintype AlgebraicGeometry.Scheme.OrderedAffineCover.instFintypeIdx AlgebraicGeometry.OModulePresheaf.addCommGroup AlgebraicGeometry.Scheme.OrderedAffineCover.instDecidableEqIdx AlgebraicGeometry.OModulePresheaf.moduleSections AlgebraicGeometry.OModulePresheaf.instSubsingletonObjZero AlgebraicGeometry.OModulePresheaf.Leray.relAltC_scalarTower AlgebraicGeometry.OModulePresheaf.Leray.ker_relAltd_modΓ AlgebraicGeometry.OModulePresheaf.Leray.relAltC_modΓ AlgebraicGeometry.OModulePresheaf.Leray.biC_abGrp AlgebraicGeometry.OModulePresheaf.Leray.relAltH_modΓ AlgebraicGeometry.OModulePresheaf.Leray.ker_relAltd_smul AlgebraicGeometry.OModulePresheaf.Leray.relAltH_scalarTower AlgebraicGeometry.OModulePresheaf.Leray.relAltH_smul AlgebraicGeometry.OModulePresheaf.Leray.biC_module AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instDecidableEqIdx AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instFintype AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instLinearOrder AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instFintypeIdx DoubleComplex.instModuleE₂I DoubleComplex.Bounded.modR DoubleComplex.instModuleE₂II DoubleComplex.instAddCommGroupE₂II DoubleComplex.Bounded.abGrp DoubleComplex.instAddCommGroupE₂I ProjSpaceCech.GradedModule.H.module ProjSpaceCech.GradedModule.H.addCommGroup ProjSpaceCech.GradedModule.sec.instAdd ProjSpaceCech.GradedModule.sec.instNeg ProjSpaceCech.GradedModule.acg ProjSpaceCech.GradedModule.Frac.setoid ProjSpaceCech.GradedModule.modR ProjSpaceCech.GradedModule.sec.instModule ProjSpaceCech.GradedModule.sec.instAddCommGroup ProjSpaceCech.GradedModule.sec.instZero ProjSpaceCech.GradedModule.Presentation.fJ ProjSpaceCech.GradedModule.sec.instSMul ProjSpaceCech.Twist.H.module ProjSpaceCech.Idx.instFintype"
p2m_attr_erase "instance" "ProjSpaceCech.Twist.H.addCommGroup ProjSpaceCech.Idx.instDecidableEq ProjSpaceCech.Twist.Mon.instDecidableEq ProjSpaceCech.Twist.cochain.instAddCommGroup ProjSpaceCech.Twist.cochain.instModule AlgebraicGeometry.Scheme.Modules.GlueOfCocycle.instSMulCarrierObjOppositeOpensCarrierCarrierCommRingCatPresheafOpOpensSubtypeForallMinMemAddSubgroupFamilies AlgebraicGeometry.Scheme.Modules.GlueOfCocycle.instModulePreGlue AlgebraicGeometry.Scheme.Modules.GlueOfCocycle.instModuleCarrierObjOppositeOpensCarrierCarrierCommRingCatPresheafOpOpensSubtypeForallMinMemAddSubgroupFamilies SheafOfModules.isIso_ihomModelToIhom PresheafOfModules.ExteriorPower.instModulePresheafAb AlgebraicGeometry.Scheme.OrderedOpenFamily.instFintype AlgebraicGeometry.Scheme.OrderedOpenFamily.instDecidableEqIdx AlgebraicGeometry.Scheme.OrderedOpenFamily.instLinearOrder AlgebraicGeometry.Scheme.OrderedOpenFamily.instFintypeIdx CochainCx.Bounded.abGrp CochainCx.Bounded.modR instTopologicallyFGOfFiniteType AlgebraicCurve.CurveModel.isProper AlgebraicCurve.CurveModel.isIntegral AlgebraicCurve.CurveModel.smooth AlgebraicCurve.Place.instIsScalarTowerSubtypeMemValuationSubringToValuationSubring AlgebraicCurve.Divisor.instDistribMulActionAlgEquiv AlgebraicCurve.Place.instSMulAlgEquiv AlgebraicCurve.Place.instIsPrincipalIdealRingSubtypeMemValuationSubringToValuationSubring AlgebraicCurve.Place.instIsDiscreteValuationRingSubtypeMemValuationSubringToValuationSubring AlgebraicCurve.Pic0.instDistribMulActionAlgEquiv AlgebraicCurve.Place.instAlgebraSubtypeMemValuationSubringToValuationSubring AlgebraicCurve.Place.instMulActionAlgEquiv AlgebraicCurve.Pic0.instSMulAlgEquiv AlgebraicCurve.CurveModel.locallyOfFiniteType_gluedToBase AlgebraicCurve.CurveModel.isFractionRing_overlap AlgebraicCurve.CurveModel.isLocallyNoetherian_glued AlgebraicCurve.CurveModel.jacobsonSpace_glued AlgebraicCurve.CurveModel.isOpenImmersion_ι₀ AlgebraicCurve.CurveModel.isIntegral_glued AlgebraicCurve.CurveModel.quasiSeparated_gluedToBase AlgebraicCurve.CurveModel.compactSpace_glued AlgebraicCurve.CurveModel.isIntegral_adjoin_chartRing AlgebraicCurve.CurveModel.isFractionRing_overlap_functionField AlgebraicCurve.CurveModel.isProper_gluedToBase"
p2m_attr_erase "instance" "AlgebraicCurve.CurveModel.isOpenImmersion_ιU AlgebraicCurve.CurveModel.isOpenImmersion_f₀ AlgebraicCurve.CurveModel.isOpenImmersion_fInf AlgebraicCurve.CurveModel.isOpenImmersion_ιInf AlgebraicCurve.CurveModel.algebra_overlap_functionField AlgebraicCurve.CurveModel.quasiCompact_gluedToBase AlgebraicCurve.CurveModel.algebraAdjoin AlgebraicCurve.CurveModel.isDedekindDomain_chartRing AlgebraicCurve.CurveModel.isIntegralClosure AlgebraicCurve.CurveModel.finite_chartRing AlgebraicCurve.CurveModel.centre_isPrime AlgebraicCurve.CurveModel.isFractionRing_chartRing AlgebraicCurve.CurveModel.finiteType_chartRing AlgebraicCurve.CurveModel.isNoetherianRing_chartRing AlgebraicCurve.CurveModel.isScalarTower_base_adjoin AlgebraicCurve.CurveModel.isScalarTower_adjoin AlgebraicCurve.CurveModel.chartRing_finitePresentation AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation"
p2m_attr_erase "simp" "GoodReductionJacobian.relativeGroupLawOfGrpObj_inv GoodReductionJacobian.relativeGroupLawOfGrpObj_mul GoodReductionJacobian.overHomEquivSchemeHomOver_apply_coe GoodReductionJacobian.relativeGroupLawOfGrpObj_one GoodReductionJacobian.overHomEquivSchemeHomOver_symm_apply_left GoodReductionJacobian.prodInr_comp_prodFst GoodReductionJacobian.RelativeGroupLaw.prod_inv GoodReductionJacobian.prodInl_comp_prodSnd GoodReductionJacobian.prodInr_comp_prodSnd GoodReductionJacobian.prodInl_comp_prodFst GoodReductionJacobian.prodFstPt_prodPairPt GoodReductionJacobian.prodFst_coe GoodReductionJacobian.prodSndPt_prodPairPt GoodReductionJacobian.RelativeGroupLaw.prod_one GoodReductionJacobian.prodPairPt_coe GoodReductionJacobian.prodPairPt_prodFstPt_prodSndPt GoodReductionJacobian.prodFstPt_coe GoodReductionJacobian.RelativeGroupLaw.prod_mul GoodReductionJacobian.prodSndPt_coe GoodReductionJacobian.prodSnd_coe NeronModelInfra.NeronModelPropertyBundle.endExtensionEquiv_symm_restrict NeronModelInfra.schemeHomOverComp_id_left NeronModelInfra.schemeHomOverComp_id_right NeronModelInfra.schemeHomOverId_coe NeronModelInfra.NeronModelPropertyBundle.endExtensionEquiv_apply NeronModelInfra.NeronModelPropertyBundle.restrict_endExtensionEquiv_symm NeronModelInfra.schemeHomOverComp_coe AlgebraicGeometry.RelPicard.RepresentsRelSubPic.mk.injEq AlgebraicGeometry.RelPicard.SubPicCondition.mk.injEq AlgebraicGeometry.RelPicard.SubPicCondition.mk.sizeOf_spec AlgebraicGeometry.RelPicard.RepresentsRelSubPic.mk.sizeOf_spec AlgebraicGeometry.Scheme.TwoAffineOpenCover.mk.injEq AlgebraicGeometry.Scheme.TwoAffineOpenCover.mk.sizeOf_spec AlgebraicGeometry.Scheme.TwoAffineOpenCover.pullback_U1 AlgebraicGeometry.Scheme.TwoAffineOpenCover.pullback_U0 TwoChartCech.Sections.mk.injEq TwoChartCech.Cover.mk.injEq TwoChartCech.GrothendieckComplex.mk.injEq TwoChartCech.Sections.mk.sizeOf_spec TwoChartCech.Cover.mk.sizeOf_spec"
p2m_attr_erase "simp" "TwoChartCech.Cover.lineBundle_r0_apply TwoChartCech.GrothendieckComplex.mk.sizeOf_spec TwoChartCech.Cover.lineBundle_r1_apply CoherentBaseChange.TwoTermComplex.mk.sizeOf_spec CoherentBaseChange.TwoTermComplex.mk.injEq AlgebraicGeometry.SubalgebraStages.specCone_π_app AlgebraicGeometry.SubalgebraStages.specLeg_specHom AlgebraicGeometry.SubalgebraStages.specLeg_specTrans AlgebraicGeometry.SubalgebraStages.cone_pt AlgebraicGeometry.SubalgebraStages.trans_fst AlgebraicGeometry.SubalgebraStages.diagram_obj AlgebraicGeometry.SubalgebraStages.leg_snd AlgebraicGeometry.SubalgebraStages.diagram_map AlgebraicGeometry.SubalgebraStages.specTrans_refl AlgebraicGeometry.SubalgebraStages.trans_snd AlgebraicGeometry.SubalgebraStages.specTrans_specHom AlgebraicGeometry.SubalgebraStages.specCone_pt AlgebraicGeometry.SubalgebraStages.cone_π_app AlgebraicGeometry.SubalgebraStages.specDiagram_map AlgebraicGeometry.SubalgebraStages.specDiagram_obj AlgebraicGeometry.SubalgebraStages.leg_fst AlgebraicGeometry.SubalgebraStages.leg_trans IsDirectLimit.Module.linearEquiv_symm_apply IsDirectLimit.linearEquiv_symm_apply IsDirectLimit.lift_of IsDirectLimit.Module.linearEquiv_apply IsDirectLimit.Module.lift_of IsDirectLimit.Equiv_apply RegularLocalRingQuotientAscent.dualNumberFst_apply GoodReductionJacobian.RelativeGroupLaw.baseChangePointToBase_ofBase GoodReductionJacobian.RelativeGroupLaw.baseChangePointToBase_coe GoodReductionJacobian.RelativeGroupLaw.baseChangePointOfBase_coe GoodReductionJacobian.RelativeGroupLaw.baseChange_inv GoodReductionJacobian.RelativeGroupLaw.baseChangePointOfBase_toBase GoodReductionJacobian.RelativeGroupLaw.baseChange_mul GoodReductionJacobian.RelativeGroupLaw.baseChange_one NeronSpecialFibreInfra.specialFibreRestrict_coe_comp_fst NeronSpecialFibreInfra.fibreRestrictAlong_coe_comp_snd NeronSpecialFibreInfra.fibreRestrictAlong_coe_comp_fst NeronSpecialFibreInfra.neronEndRestrictEquiv_apply"
p2m_attr_erase "simp" "NeronSpecialFibreInfra.fibreRestrictAlong_coe_comp_fst_assoc NeronSpecialFibreInfra.specialFibreRestrict_coe_comp_snd NeronSpecialFibreInfra.neronEndExtension_genericFibreRestrict NeronSpecialFibreInfra.specClosedFibreInclusion_eq NeronSpecialFibreInfra.specialFibreRestrict_coe_comp_fst_assoc NeronSpecialFibreInfra.specialFibreRestrict_coe_comp_snd_assoc NeronSpecialFibreInfra.genericFibreRestrict_neronEndExtension NeronSpecialFibreInfra.homOverId_coe NeronSpecialFibreInfra.homOverComp_coe NeronSpecialFibreInfra.fibreRestrictAlong_coe_comp_snd_assoc GoodReductionJacobian.RelativeGroupLaw.fibre_inv GoodReductionJacobian.RelativeGroupLaw.fibrePointToBase_coe GoodReductionJacobian.RelativeGroupLaw.fibrePointOfBase_toBase GoodReductionJacobian.RelativeGroupLaw.fibre_mul GoodReductionJacobian.RelativeGroupLaw.fibrePointToBase_ofBase GoodReductionJacobian.RelativeGroupLaw.fibre_one GoodReductionJacobian.RelativeGroupLaw.fibrePointOfBase_coe AlgebraicGeometry.schemeFibreEndo_snd AlgebraicGeometry.schemeFibreEndo_fst AlgebraicGeometry.Scheme.OrderedAffineCover.mk.injEq AlgebraicGeometry.OModulePresheaf.mk.sizeOf_spec AlgebraicGeometry.Scheme.OrderedAffineCover.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.mk.injEq AlgebraicGeometry.OModulePresheaf.prod_obj AlgebraicGeometry.OModulePresheaf.restrOpen_obj AlgebraicGeometry.OModulePresheaf.DevissageStep.mk.injEq AlgebraicGeometry.OModulePresheaf.pushforward_obj AlgebraicGeometry.OModulePresheaf.im_obj AlgebraicGeometry.OModulePresheaf.pow_obj AlgebraicGeometry.OModulePresheaf.fstHom_app AlgebraicGeometry.OModulePresheaf.ker_obj AlgebraicGeometry.OModulePresheaf.coker_obj AlgebraicGeometry.OModulePresheaf.DevissageStep.mk.sizeOf_spec AlgebraicGeometry.Scheme.OrderedAffineCover.preimage_U AlgebraicGeometry.OModulePresheaf.sndHom_app AlgebraicGeometry.OModulePresheaf.Hom.mk.injEq AlgebraicGeometry.OModulePresheaf.Hom.id_app AlgebraicGeometry.OModulePresheaf.AffHom.appSections_apply AlgebraicGeometry.OModulePresheaf.AffHom.comp_app AlgebraicGeometry.OModulePresheaf.AffSES.mk.sizeOf_spec"
p2m_attr_erase "simp" "AlgebraicGeometry.OModulePresheaf.AffHom.kerMap_coe AlgebraicGeometry.OModulePresheaf.AffHom.id_app AlgebraicGeometry.OModulePresheaf.Hom.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.Hom.toAffHom_app AlgebraicGeometry.OModulePresheaf.SES.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.AffHom.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.Hom.comp_app AlgebraicGeometry.OModulePresheaf.SES.mk.injEq AlgebraicGeometry.OModulePresheaf.AffHom.mk.injEq AlgebraicGeometry.OModulePresheaf.Hom.appSections_apply AlgebraicGeometry.OModulePresheaf.AffSES.mk.injEq AlgebraicGeometry.OModulePresheaf.Leray.restrictToPreimage_U AlgebraicGeometry.Scheme.OrderedAffineCover.toCoverOf_U AlgebraicGeometry.Scheme.OrderedAffineCoverOf.mk.sizeOf_spec AlgebraicGeometry.Scheme.OrderedAffineCoverOf.mk.injEq AlgebraicGeometry.Scheme.OrderedAffineCover.restrict_U DoubleComplex.Bounded.mk.injEq DoubleComplex.Bounded.mk.sizeOf_spec DoubleComplex.Convergence.mk.injEq DoubleComplex.Convergence.mk.sizeOf_spec DoubleComplex.SubQuot.mk.sizeOf_spec DoubleComplex.SubQuot.mk.injEq ProjSpaceCech.GradedModule.mk.injEq ProjSpaceCech.GradedModule.mk.sizeOf_spec ProjSpaceCech.GradedModule.Frac.mk.sizeOf_spec ProjSpaceCech.GradedModule.Presentation.mk.injEq ProjSpaceCech.GradedModule.Frac.mk.injEq ProjSpaceCech.GradedModule.Presentation.mk.sizeOf_spec ProjSpaceCech.GradedModule.Hom.shift_toLinearMap ProjSpaceCech.GradedModule.Hom.mk.sizeOf_spec ProjSpaceCech.GradedModule.Hom.mk.injEq AlgebraicGeometry.Scheme.Modules.tensorSections_zero_right AlgebraicGeometry.Scheme.Modules.map_unitSection AlgebraicGeometry.Scheme.Modules.tensorSectionsBilin_apply AlgebraicGeometry.Scheme.Modules.tensorPowSection_zero AlgebraicGeometry.Scheme.Modules.tensorSections_zero_left AlgebraicGeometry.Scheme.Modules.tensorPow_zero AlgebraicGeometry.Scheme.Modules.tensorPow_succ AlgebraicGeometry.Scheme.Modules.glueComponent_glueMk AlgebraicGeometry.Scheme.Modules.UnitCocycle.mk.injEq"
p2m_attr_erase "simp" "AlgebraicGeometry.Scheme.Modules.UnitCocycle.mk.sizeOf_spec AlgebraicGeometry.Scheme.Modules.pullbackLocalSection_neg AlgebraicGeometry.Scheme.Modules.pullbackLocalSection_zero AlgebraicGeometry.Scheme.Modules.pullbackLocalSection_sub AlgebraicGeometry.Scheme.Modules.pullbackLocalSection_add PresheafOfModules.InternalHom.IsSheafAux.appAt_toPresheafHom SheafOfModules.ihomSectionsEquivFamily_unit AlgebraicGeometry.Scheme.Modules.restrictHomEquivFamily_apply SheafOfModules.ihomEval_unit_app AlgebraicGeometry.Scheme.Modules.ihomEval_zero_right AlgebraicGeometry.Scheme.Modules.ihomEval_zero_left AlgebraicGeometry.Scheme.Modules.homOfFamily_app_apply SheafOfModules.unit_ihomSectionsEquivFamily AlgebraicGeometry.Scheme.Modules.familyOfHom_app AlgebraicGeometry.Scheme.Modules.restrictUnitIso_hom_app_apply AlgebraicGeometry.Scheme.Modules.restrictUnitIso_inv_app_apply AlgebraicGeometry.Scheme.Modules.restrictHomOfFamily_app_apply AlgebraicGeometry.Scheme.Modules.restrictHomEquivFamily_symm_apply AlgebraicGeometry.tilde.functorCompPullbackSpecIso_app AlgebraicGeometry.Scheme.Hom.kaehlerPresheaf_obj PresheafOfModules.exteriorPower_map_ιMulti PresheafOfModules.ExteriorPower.appₗ_apply AlgebraicGeometry.Scheme.Modules.exteriorPower_obj AlgebraicGeometry.Scheme.OrderedOpenFamily.mk.injEq AlgebraicGeometry.Scheme.OrderedOpenFamily.mk.sizeOf_spec CochainCx.Bounded.mk.sizeOf_spec CochainCx.Bounded.mk.injEq AlgebraicCurve.CurveModel.mk.injEq AlgebraicCurve.CurveModel.mk.sizeOf_spec AlgebraicCurve.Place.mk.injEq AlgebraicCurve.Divisor.degree_single AlgebraicCurve.Divisor.smul_single AlgebraicCurve.Place.smul_toValuationSubring AlgebraicCurve.Place.heightOneSpectrum_asIdeal AlgebraicCurve.Place.coe_algebraMap AlgebraicCurve.Place.ord_one AlgebraicCurve.Place.coe_smulRingEquiv_apply AlgebraicCurve.Pic0.coe_degZeroSMulHom AlgebraicCurve.Place.deg_smul AlgebraicCurve.Pic0.mk_zero"
p2m_attr_erase "simp" "AlgebraicCurve.Place.mk.sizeOf_spec AlgebraicCurve.Divisor.degree_smul AlgebraicCurve.Pic0.mk_add AlgebraicCurve.Place.ord_zero AlgebraicCurve.Place.ofHeightOneSpectrum_toValuationSubring AlgebraicCurve.CurveModel.coe_gInf AlgebraicCurve.CurveModel.coe_tInvChart AlgebraicCurve.CurveModel.ιInf_gluedToBase_assoc AlgebraicCurve.CurveModel.ιInf_gluedToBase AlgebraicCurve.CurveModel.primeOfι₀_asIdeal AlgebraicCurve.CurveModel.coe_tChart AlgebraicCurve.CurveModel.ι₀_gluedToBase_assoc AlgebraicCurve.CurveModel.primeOfιInf_asIdeal AlgebraicCurve.CurveModel.ι₀_gluedToBase AlgebraicCurve.CurveModel.coe_tma AlgebraicCurve.CurveModel.coe_primeEquivChartPlaces AlgebraicCurve.Place.congrEquiv_symm_apply AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply AlgebraicCurve.RationalFunctionField.deg_placeOfPoint"

set_option autoImplicit false

p2m_open "CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory AlgebraicGeometry NeronModelInfra GoodReductionJacobian AlgebraicGeometry.Polarisation"

namespace KerRoot

section
variable {C : Type*} [Category C] [MonoidalCategory C]

noncomputable def isoOfTensorIsoUnit [BraidedCategory C] {A B D : C} (eB : A ⊗ B ≅ 𝟙_ C) (eD : A ⊗ D ≅ 𝟙_ C) : B ≅ D :=
  (λ_ B).symm ≪≫ whiskerRightIso ((β_ D A ≪≫ eD).symm) B ≪≫ α_ D A B ≪≫ whiskerLeftIso D eB ≪≫ ρ_ D

def mpow (M : C) : ℕ → C
  | 0 => 𝟙_ C
  | n + 1 => mpow M n ⊗ M

noncomputable def mpowAddIso (M : C) (a : ℕ) : ∀ b : ℕ, mpow M a ⊗ mpow M b ≅ mpow M (a + b)
  | 0 => ρ_ _
  | b + 1 => (α_ _ _ _).symm ≪≫ whiskerRightIso (mpowAddIso M a b) M

end

theorem tpow_eq_mpow {X : Scheme.{0}} (M : X.Modules) : ∀ n : ℕ, Scheme.Modules.tpow M n = mpow M n
  | 0 => rfl
  | n + 1 => by rw [Scheme.Modules.tpow, mpow, tpow_eq_mpow M n]

theorem locIsoOnBase_of_iso {S : Type} [CommRing S] {X : Scheme.{0}} (g : X ⟶ Spec (CommRingCat.of S))
    {M M' : X.Modules} (e : M ≅ M') : LocIsoOnBase g M M' := fun s =>
  ⟨⊤, trivial, ⟨(Scheme.Modules.pullback (g ⁻¹ᵁ ⊤).ι).mapIso e⟩⟩

theorem nonempty_dual_iso {X : Scheme.{0}} {M M' : X.Modules} (hM : Scheme.Modules.IsInvertible M)
    (hM' : Scheme.Modules.IsInvertible M') (e : M ≅ M') : Nonempty (Scheme.Modules.dual M ≅ Scheme.Modules.dual M') := by
  obtain ⟨-, ⟨eM⟩⟩ := Scheme.Modules.IsInvertible.dual_monoidalV2 hM
  obtain ⟨-, ⟨eM'⟩⟩ := Scheme.Modules.IsInvertible.dual_monoidalV2 hM'
  exact ⟨(isoOfTensorIsoUnit eM' ((e.symm ⊗ᵢ Iso.refl _) ≪≫ eM)).symm⟩

theorem nonempty_dual_dual_iso {X : Scheme.{0}} {M : X.Modules} (hM : Scheme.Modules.IsInvertible M) :
    Nonempty (Scheme.Modules.dual (Scheme.Modules.dual M) ≅ M) := by
  obtain ⟨hd, ⟨eM⟩⟩ := Scheme.Modules.IsInvertible.dual_monoidalV2 hM
  obtain ⟨-, ⟨edM⟩⟩ := Scheme.Modules.IsInvertible.dual_monoidalV2 hd
  exact ⟨isoOfTensorIsoUnit edM (β_ _ _ ≪≫ eM)⟩

theorem locIsoOnBase_dual {S : Type} [CommRing S] {X : Scheme.{0}} (g : X ⟶ Spec (CommRingCat.of S))
    {M M' : X.Modules} (hM : Scheme.Modules.IsInvertible M) (hM' : Scheme.Modules.IsInvertible M')
    (h : LocIsoOnBase g M M') : LocIsoOnBase g (Scheme.Modules.dual M) (Scheme.Modules.dual M') := by
  intro s
  obtain ⟨U, hsU, ⟨φ⟩⟩ := h s
  obtain ⟨e₁⟩ := Scheme.Modules.IsInvertible.pullback_dual_monoidalV2 (g ⁻¹ᵁ U).ι hM
  obtain ⟨e₂⟩ := Scheme.Modules.IsInvertible.pullback_dual_monoidalV2 (g ⁻¹ᵁ U).ι hM'
  obtain ⟨e₃⟩ := nonempty_dual_iso (hM.pullback _) (hM'.pullback _) φ
  exact ⟨U, hsU, ⟨e₁ ≪≫ e₃ ≪≫ e₂.symm⟩⟩

theorem isInvertible_mumfordBundle {S : Type} [CommRing S] {A : Scheme.{0}} (f : A ⟶ Spec (CommRingCat.of S))
    (L : RelativeGroupLaw S f) {𝓛 : A.Modules} (h𝓛 : Scheme.Modules.IsInvertible 𝓛) :
    Scheme.Modules.IsInvertible (mumfordBundle f L 𝓛) := by
  obtain ⟨hd, -⟩ := Scheme.Modules.IsInvertible.dual_monoidalV2 h𝓛
  exact Scheme.Modules.IsInvertible.tensor_monoidalV2 (h𝓛.pullback _)
    (Scheme.Modules.IsInvertible.tensor_monoidalV2 (hd.pullback _) (hd.pullback _))

private theorem _root_.KerRoot.isInvertible_unit (X : Scheme.{0}) : Scheme.Modules.IsInvertible (𝟙_ X.Modules) :=
  Scheme.Modules.isInvertible_unit X

p2m_export "KerRoot" "isInvertible_unit"
theorem isInvertible_tpow {X : Scheme.{0}} {M : X.Modules} (hM : Scheme.Modules.IsInvertible M) :
    ∀ n, Scheme.Modules.IsInvertible (Scheme.Modules.tpow M n)
  | 0 => isInvertible_unit X
  | n + 1 => Scheme.Modules.IsInvertible.tensor_monoidalV2 (isInvertible_tpow hM n) hM

theorem nonempty_mumfordBundle_unit_iso {S : Type} [CommRing S] {A : Scheme.{0}} (f : A ⟶ Spec (CommRingCat.of S))
    (L : RelativeGroupLaw S f) : Nonempty (mumfordBundle f L (𝟙_ A.Modules) ≅ 𝟙_ _) := by
  obtain ⟨-, ⟨e1⟩⟩ := Scheme.Modules.IsInvertible.dual_monoidalV2 (isInvertible_unit A)
  have eD : Scheme.Modules.dual (𝟙_ A.Modules) ≅ 𝟙_ _ := (λ_ _).symm ≪≫ e1
  refine ⟨?_⟩
  unfold mumfordBundle
  exact (Scheme.Modules.pullbackTensorUnitObjIso _ ⊗ᵢ
      (((Scheme.Modules.pullback _).mapIso eD ≪≫ Scheme.Modules.pullbackTensorUnitObjIso _) ⊗ᵢ
        ((Scheme.Modules.pullback _).mapIso eD ≪≫ Scheme.Modules.pullbackTensorUnitObjIso _))) ≪≫
    (λ_ _) ≪≫ (λ_ _)

end KerRoot

open KerRoot

section Slices

variable {S : Type} [CommRing S] {A : Scheme.{0}} (f : A ⟶ Spec (CommRingCat.of S)) (L : RelativeGroupLaw S f)
  (hc : L.IsCommutative) (hA : AbelianSchemePropertyBundle S f)
  (R : Type) [CommRing R] (t : Spec (CommRingCat.of R) ⟶ Spec (CommRingCat.of S)) (y : SchemeHomOver t f)

theorem KerRoot.locIsoOnBase_slice_unit :
    LocIsoOnBase (pullback.snd f t) ((Scheme.Modules.pullback (sliceAt f y)).obj (mumfordBundle f L (𝟙_ A.Modules)))
      (𝟙_ (pullback f t).Modules) := by
  obtain ⟨e⟩ := nonempty_mumfordBundle_unit_iso f L
  exact locIsoOnBase_of_iso _ ((Scheme.Modules.pullback _).mapIso e ≪≫ Scheme.Modules.pullbackTensorUnitObjIso _)

include hc hA in

theorem KerRoot.locIsoOnBase_slice_pullback_negMor (𝓛₀ : A.Modules) (h₀ : Scheme.Modules.IsInvertible 𝓛₀) :
    LocIsoOnBase (pullback.snd f t)
      ((Scheme.Modules.pullback (sliceAt f y)).obj (mumfordBundle f L ((Scheme.Modules.pullback (negMor f L)).obj 𝓛₀)))
      ((Scheme.Modules.pullback (sliceAt f y)).obj (mumfordBundle f L 𝓛₀)) := by
  have E := LocIsoOnBase.equivalence (S := R) (pullback.snd f t)
  have hΛ : Scheme.Modules.IsInvertible (mumfordBundle f L 𝓛₀) := isInvertible_mumfordBundle f L h₀
  have hΛy : Scheme.Modules.IsInvertible ((Scheme.Modules.pullback (sliceAt f y)).obj (mumfordBundle f L 𝓛₀)) :=
    hΛ.pullback _
  have hΛi : Scheme.Modules.IsInvertible
      ((Scheme.Modules.pullback (sliceAt f (L.inv t y))).obj (mumfordBundle f L 𝓛₀)) := hΛ.pullback _
  obtain ⟨hdy, -⟩ := Scheme.Modules.IsInvertible.dual_monoidalV2 hΛy
  obtain ⟨eB⟩ := nonempty_pullback_sliceAt_mumfordBundle_pullback_negMor_iso_of_commRing S f L hc 𝓛₀ h₀ R t y
  have hC := locIsoOnBase_pullback_negMor_prod_sliceAt_mumfordBundle_dual_of_commRing S f L hc hA 𝓛₀ h₀ R t (L.inv t y)
  have hD := locIsoOnBase_sliceAt_mumfordBundle_inv_dual_of_commRing S f L hc hA 𝓛₀ h₀ R t y
  have hD' := locIsoOnBase_dual (pullback.snd f t) hΛi hdy hD
  obtain ⟨eE⟩ := nonempty_dual_dual_iso hΛy
  exact E.trans (locIsoOnBase_of_iso _ eB) (E.trans hC (E.trans hD' (locIsoOnBase_of_iso _ eE)))

theorem KerRoot.locIsoOnBase_slice_tpow (M : A.Modules) (hM : Scheme.Modules.IsInvertible M)
    (U : (pullback f t).Modules)
    (hU : LocIsoOnBase (pullback.snd f t) ((Scheme.Modules.pullback (sliceAt f y)).obj (mumfordBundle f L M)) U) :
    ∀ n : ℕ, LocIsoOnBase (pullback.snd f t)
      ((Scheme.Modules.pullback (sliceAt f y)).obj (mumfordBundle f L (Scheme.Modules.tpow M n))) (mpow U n) := by
  have E := LocIsoOnBase.equivalence (S := R) (pullback.snd f t)
  intro n
  induction n with
  | zero => exact KerRoot.locIsoOnBase_slice_unit f L R t y
  | succ n ih =>
    obtain ⟨e⟩ := nonempty_pullback_sliceAt_mumfordBundle_tensor_iso_of_commRing S f L (Scheme.Modules.tpow M n) M
      (isInvertible_tpow hM n) hM y
    exact E.trans (locIsoOnBase_of_iso _ e) (LocIsoOnBase.tensor ih hU)

include hc hA in

theorem KerRoot.locIsoOnBase_slice_nsmul (𝓛₀ : A.Modules) (h₀ : Scheme.Modules.IsInvertible 𝓛₀) :
    ∀ n : ℕ, LocIsoOnBase (pullback.snd f t)
      ((Scheme.Modules.pullback (sliceAt f (L.nsmul t n y))).obj (mumfordBundle f L 𝓛₀))
      (mpow ((Scheme.Modules.pullback (sliceAt f y)).obj (mumfordBundle f L 𝓛₀)) n) := by
  have E := LocIsoOnBase.equivalence (S := R) (pullback.snd f t)
  intro n
  induction n with
  | zero => exact locIsoOnBase_pullback_sliceAt_mumfordBundle_one_unit_of_commRing f L 𝓛₀ h₀ R t
  | succ n ih =>
    show LocIsoOnBase (pullback.snd f t)
      ((Scheme.Modules.pullback (sliceAt f (L.mul t (L.nsmul t n y) y))).obj (mumfordBundle f L 𝓛₀)) _
    exact E.trans (locIsoOnBase_sliceAt_mumfordBundle_mul_tensor_of_commRing S f L hc hA 𝓛₀ h₀ R t (L.nsmul t n y) y)
      (LocIsoOnBase.tensor ih (E.refl _))

end Slices

theorem solution
    {S : Type} [CommRing S] {A : Scheme.{0}} (f : A ⟶ Spec (CommRingCat.of S)) (L : RelativeGroupLaw S f)
    (hc : L.IsCommutative) (hA : AbelianSchemePropertyBundle S f)
    (𝓛₀ : A.Modules) (h𝓛₀ : Scheme.Modules.IsInvertible 𝓛₀) (a b : ℕ) (hab : 1 ≤ a + b)
    (R : Type) [CommRing R] (t : Spec (CommRingCat.of R) ⟶ Spec (CommRingCat.of S)) (y : SchemeHomOver t f) :
    MemKernel f L (Scheme.Modules.tpow 𝓛₀ a ⊗ Scheme.Modules.tpow ((Scheme.Modules.pullback (negMor f L)).obj 𝓛₀) b) t y ↔
      MemKernel f L 𝓛₀ t (L.nsmul t (a + b) y) := by
  have E := LocIsoOnBase.equivalence (S := R) (pullback.snd f t)
  let N := (Scheme.Modules.pullback (negMor f L)).obj 𝓛₀
  let U := (Scheme.Modules.pullback (sliceAt f y)).obj (mumfordBundle f L 𝓛₀)
  have hN : Scheme.Modules.IsInvertible N := h𝓛₀.pullback _
  have hUa := KerRoot.locIsoOnBase_slice_tpow f L R t y 𝓛₀ h𝓛₀ U (E.refl _) a
  have hUb := KerRoot.locIsoOnBase_slice_tpow f L R t y N hN U
    (KerRoot.locIsoOnBase_slice_pullback_negMor f L hc hA R t y 𝓛₀ h𝓛₀) b
  obtain ⟨e⟩ := nonempty_pullback_sliceAt_mumfordBundle_tensor_iso_of_commRing S f L
    (Scheme.Modules.tpow 𝓛₀ a) (Scheme.Modules.tpow N b) (isInvertible_tpow h𝓛₀ a) (isInvertible_tpow hN b) y
  have hL : LocIsoOnBase (pullback.snd f t)
      ((Scheme.Modules.pullback (sliceAt f y)).obj
        (mumfordBundle f L (Scheme.Modules.tpow 𝓛₀ a ⊗ Scheme.Modules.tpow N b))) (mpow U (a + b)) :=
    E.trans (locIsoOnBase_of_iso _ e) (E.trans (LocIsoOnBase.tensor hUa hUb) (locIsoOnBase_of_iso _ (mpowAddIso U a b)))
  have hR := KerRoot.locIsoOnBase_slice_nsmul f L hc hA R t y 𝓛₀ h𝓛₀ (a + b)
  constructor
  · intro h
    exact E.trans hR (E.trans (E.symm hL) h)
  · intro h
    exact E.trans hL (E.trans (E.symm hR) h)

end S_AlgebraicGeometry_Polarisation_memKernel_tpow_tensor_tpow_pullback_negMor_iff_memKernel_nsmul_add
end P2MW
export P2MW.S_AlgebraicGeometry_Polarisation_memKernel_tpow_tensor_tpow_pullback_negMor_iff_memKernel_nsmul_add (solution)
