-- Prove2me | solution 1 for AlgebraicGeometry.PolarisedAbelianScheme.natCast_add_ne_zero_of_principalRoot_of_rootedSymmetricOfType_of_isAlgClosed
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:02.935278+00:00
-- url     : https://prove2.me/submissions/ba33d229-da0f-5b6d-ba03-51bfaf808a21

import Mathlib
import Theorems.Thm_AlgebraicGeometry_Polarisation_memKernel_tpow_tensor_tpow_pullback_negMor_iff_memKernel_nsmul_add
import Theorems.Thm_AlgebraicGeometry_Polarisation_locIsoOnBase_pullback_sliceAt_mumfordBundle_one_unit_of_commRing
import Theorems.Thm_AlgebraicGeometry_Polarisation_memKernel_iff_memKernel_comp_of_isPullback
import Theorems.Thm_GoodReductionJacobian_AbelianSchemePropertyBundle_exists_nsmul_eq_one_dualNumber_ne_one_of_natCast_eq_zero
import Theorems.Thm_AlgebraicGeometry_topologicalKrullDim_preimage_pullback_snd_eq_of_smooth_of_isConnected
import Theorems.Thm_GoodReductionJacobian_AbelianSchemePropertyBundle_isCommutative
import Theorems.Thm_GoodReductionJacobian_AbelianSchemePropertyBundle_of_isPullback
import Theorems.Thm_AlgebraicGeometry_Polarisation_LocIsoOnBase_mumfordBundle_of_isInvertible
import Theorems.Thm_AlgebraicGeometry_Polarisation_LocIsoOnBase_equivalence
import Theorems.Thm_AlgebraicGeometry_Polarisation_LocIsoOnBase_pullback_of_comp_eq
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_IsInvertible_tensor_monoidalV2
import Definitions.Def_AlgebraicGeometry_ThetaGroupLaw
import Definitions.Def_AlgebraicGeometry_PolarisedAbelianSchemeOfType
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_PolarisedAbelianScheme_natCast_add_ne_zero_of_principalRoot_of_rootedSymmetricOfType_of_isAlgClosed
p2m_attr_erase "instance" "PresheafOfModules.PullbackMonoidal.pullback_monoidal PresheafOfModules.PullbackMonoidal.isIso_δ PresheafOfModules.pushforward_laxMonoidal PresheafOfModules.PullbackMonoidal.isIso_η PresheafOfModules.free_monoidal PresheafOfModules.restrictScalars_laxMonoidal PresheafOfModules.PullbackMonoidal.isIso_δ_gS PresheafOfModules.pullback_oplaxMonoidal PresheafOfModules.PullbackMonoidal.instPreservesColimitsOfSizeCompOppositeCommRingCatRingCatForget₂RingHomCarrierCarrierPb PresheafOfModules.pullback_monoidal' AlgebraicGeometry.Scheme.Modules.preservesBinaryProducts_opensMap AlgebraicGeometry.Scheme.Modules.pullback_monoidal AlgebraicGeometry.Scheme.Modules.sheafify_isLocalization' AlgebraicGeometry.Scheme.Modules.preservesTerminal_opensMap AlgebraicGeometry.Scheme.Modules.pullback₀_monoidal AlgebraicGeometry.Scheme.Modules.preservesFiniteProducts_opensMap AlgebraicGeometry.Scheme.Modules.instLiftingPresheafOfModulesSheafifyPresheafWOpensCarrierCarrierCommRingCatGrothendieckTopologyObjFunctorOppositeIsSheafSheafCompPullback₀Pullback TwoChartCech.Sections.M0_moduleA TwoChartCech.Sections.M1_module TwoChartCech.Cover.A01_algebra TwoChartCech.Cover.A0_algebra TwoChartCech.Cover.A1_commRing TwoChartCech.Cover.A1_algebra TwoChartCech.Sections.M01_module TwoChartCech.Sections.M0_addCommGroup TwoChartCech.Sections.M0_tower TwoChartCech.Sections.M01_addCommGroup TwoChartCech.Cover.A0_commRing TwoChartCech.Sections.M1_tower TwoChartCech.Sections.M01_moduleA TwoChartCech.Sections.M0_module TwoChartCech.Sections.M1_moduleA TwoChartCech.Sections.M1_addCommGroup TwoChartCech.Cover.A01_commRing TwoChartCech.Sections.M01_tower CoherentBaseChange.TwoTermComplex.C0_module CoherentBaseChange.TwoTermComplex.C0_addCommGroup CoherentBaseChange.TwoTermComplex.C1_module CoherentBaseChange.TwoTermComplex.C1_addCommGroup CoherentBaseChange.TwoTermComplex.C0_free"
p2m_attr_erase "instance" "CoherentBaseChange.TwoTermComplex.C1_finite CoherentBaseChange.TwoTermComplex.C0_finite CoherentBaseChange.TwoTermComplex.C1_free AlgebraicGeometry.SubalgebraStages.compactSpace_pullback AlgebraicGeometry.SubalgebraStages.quasiSeparatedSpace_pullback AlgebraicGeometry.SubalgebraStages.compactSpace_obj AlgebraicGeometry.SubalgebraStages.quasiSeparatedSpace_obj AlgebraicGeometry.SubalgebraStages.quasiCompact_snd AlgebraicGeometry.SubalgebraStages.isAffineHom_leg AlgebraicGeometry.SubalgebraStages.isAffineHom_trans AlgebraicGeometry.SubalgebraStages.isAffineHom_diagram_map AlgebraicGeometry.SubalgebraStages.quasiSeparated_snd AlgebraicGeometry.SubalgebraStages.isCofiltered_op IsDirectLimit.Module.instDirectLimitCoeLinearMapIdOfOfNonempty AdicCompletion.instIsLocalRingMaximalIdeal AlgebraicGeometry.OModulePresheaf.isScalarTower AlgebraicGeometry.Scheme.OrderedAffineCover.instLinearOrder AlgebraicGeometry.OModulePresheaf.module AlgebraicGeometry.Scheme.OrderedAffineCover.instFintype AlgebraicGeometry.Scheme.OrderedAffineCover.instFintypeIdx AlgebraicGeometry.OModulePresheaf.addCommGroup AlgebraicGeometry.Scheme.OrderedAffineCover.instDecidableEqIdx AlgebraicGeometry.OModulePresheaf.moduleSections AlgebraicGeometry.OModulePresheaf.instSubsingletonObjZero AlgebraicGeometry.OModulePresheaf.Leray.relAltC_scalarTower AlgebraicGeometry.OModulePresheaf.Leray.ker_relAltd_modΓ AlgebraicGeometry.OModulePresheaf.Leray.relAltC_modΓ AlgebraicGeometry.OModulePresheaf.Leray.biC_abGrp AlgebraicGeometry.OModulePresheaf.Leray.relAltH_modΓ AlgebraicGeometry.OModulePresheaf.Leray.ker_relAltd_smul AlgebraicGeometry.OModulePresheaf.Leray.relAltH_scalarTower AlgebraicGeometry.OModulePresheaf.Leray.relAltH_smul AlgebraicGeometry.OModulePresheaf.Leray.biC_module AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instDecidableEqIdx AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instFintype AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instLinearOrder AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instFintypeIdx DoubleComplex.instModuleE₂I DoubleComplex.Bounded.modR DoubleComplex.instModuleE₂II"
p2m_attr_erase "instance" "DoubleComplex.instAddCommGroupE₂II DoubleComplex.Bounded.abGrp DoubleComplex.instAddCommGroupE₂I ProjSpaceCech.GradedModule.H.module ProjSpaceCech.GradedModule.H.addCommGroup ProjSpaceCech.GradedModule.sec.instAdd ProjSpaceCech.GradedModule.sec.instNeg ProjSpaceCech.GradedModule.acg ProjSpaceCech.GradedModule.Frac.setoid ProjSpaceCech.GradedModule.modR ProjSpaceCech.GradedModule.sec.instModule ProjSpaceCech.GradedModule.sec.instAddCommGroup ProjSpaceCech.GradedModule.sec.instZero ProjSpaceCech.GradedModule.Presentation.fJ ProjSpaceCech.GradedModule.sec.instSMul ProjSpaceCech.Twist.H.module ProjSpaceCech.Idx.instFintype ProjSpaceCech.Twist.H.addCommGroup ProjSpaceCech.Idx.instDecidableEq ProjSpaceCech.Twist.Mon.instDecidableEq ProjSpaceCech.Twist.cochain.instAddCommGroup ProjSpaceCech.Twist.cochain.instModule AlgebraicGeometry.Scheme.Modules.GlueOfCocycle.instSMulCarrierObjOppositeOpensCarrierCarrierCommRingCatPresheafOpOpensSubtypeForallMinMemAddSubgroupFamilies AlgebraicGeometry.Scheme.Modules.GlueOfCocycle.instModulePreGlue AlgebraicGeometry.Scheme.Modules.GlueOfCocycle.instModuleCarrierObjOppositeOpensCarrierCarrierCommRingCatPresheafOpOpensSubtypeForallMinMemAddSubgroupFamilies SheafOfModules.isIso_ihomModelToIhom PresheafOfModules.ExteriorPower.instModulePresheafAb AlgebraicGeometry.Scheme.OrderedOpenFamily.instFintype AlgebraicGeometry.Scheme.OrderedOpenFamily.instDecidableEqIdx AlgebraicGeometry.Scheme.OrderedOpenFamily.instLinearOrder AlgebraicGeometry.Scheme.OrderedOpenFamily.instFintypeIdx CochainCx.Bounded.abGrp CochainCx.Bounded.modR instTopologicallyFGOfFiniteType AlgebraicCurve.CurveModel.isProper AlgebraicCurve.CurveModel.isIntegral AlgebraicCurve.CurveModel.smooth AlgebraicCurve.Place.instIsScalarTowerSubtypeMemValuationSubringToValuationSubring AlgebraicCurve.Divisor.instDistribMulActionAlgEquiv AlgebraicCurve.Place.instSMulAlgEquiv"
p2m_attr_erase "instance" "AlgebraicCurve.Place.instIsPrincipalIdealRingSubtypeMemValuationSubringToValuationSubring AlgebraicCurve.Place.instIsDiscreteValuationRingSubtypeMemValuationSubringToValuationSubring AlgebraicCurve.Pic0.instDistribMulActionAlgEquiv AlgebraicCurve.Place.instAlgebraSubtypeMemValuationSubringToValuationSubring AlgebraicCurve.Place.instMulActionAlgEquiv AlgebraicCurve.Pic0.instSMulAlgEquiv AlgebraicCurve.CurveModel.locallyOfFiniteType_gluedToBase AlgebraicCurve.CurveModel.isFractionRing_overlap AlgebraicCurve.CurveModel.isLocallyNoetherian_glued AlgebraicCurve.CurveModel.jacobsonSpace_glued AlgebraicCurve.CurveModel.isOpenImmersion_ι₀ AlgebraicCurve.CurveModel.isIntegral_glued AlgebraicCurve.CurveModel.quasiSeparated_gluedToBase AlgebraicCurve.CurveModel.compactSpace_glued AlgebraicCurve.CurveModel.isIntegral_adjoin_chartRing AlgebraicCurve.CurveModel.isFractionRing_overlap_functionField AlgebraicCurve.CurveModel.isProper_gluedToBase AlgebraicCurve.CurveModel.isOpenImmersion_ιU AlgebraicCurve.CurveModel.isOpenImmersion_f₀ AlgebraicCurve.CurveModel.isOpenImmersion_fInf AlgebraicCurve.CurveModel.isOpenImmersion_ιInf AlgebraicCurve.CurveModel.algebra_overlap_functionField AlgebraicCurve.CurveModel.quasiCompact_gluedToBase AlgebraicCurve.CurveModel.algebraAdjoin AlgebraicCurve.CurveModel.isDedekindDomain_chartRing AlgebraicCurve.CurveModel.isIntegralClosure AlgebraicCurve.CurveModel.finite_chartRing AlgebraicCurve.CurveModel.centre_isPrime AlgebraicCurve.CurveModel.isFractionRing_chartRing AlgebraicCurve.CurveModel.finiteType_chartRing AlgebraicCurve.CurveModel.isNoetherianRing_chartRing AlgebraicCurve.CurveModel.isScalarTower_base_adjoin AlgebraicCurve.CurveModel.isScalarTower_adjoin AlgebraicCurve.CurveModel.chartRing_finitePresentation AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation CerednikDrinfeld.ShimuraCurveModel.instFieldFc CerednikDrinfeld.ShimuraCurveModel.isCurveOverC CerednikDrinfeld.ShimuraCurveModel.essFiniteTypeF CerednikDrinfeld.ShimuraCurveModel.instFieldF"
p2m_attr_erase "instance" "CerednikDrinfeld.ShimuraCurveModel.instAlgebraFbar CerednikDrinfeld.ShimuraCurveModel.instAlgebraFc CerednikDrinfeld.ShimuraCurveModel.instFieldFbar CerednikDrinfeld.ShimuraCurveModel.essFiniteTypeC CerednikDrinfeld.ShimuraCurveModel.instFiniteTors CerednikDrinfeld.ShimuraCurveModel.isCurveOverF CerednikDrinfeld.ShimuraCurveModel.essFiniteTypeBar CerednikDrinfeld.ShimuraCurveModel.isCurveOverBar CerednikDrinfeld.ShimuraCurveModel.instAlgebraF IsDedekindDomain.HeightOneSpectrum.instAlgebraRatAdicCompletion IsDedekindDomain.HeightOneSpectrum.instModuleRatAdicCompletion AlgebraicCurve.SemilinearAut.instDistribMulActionSubtypeProdRingAutMemSubgroupPic0 AlgebraicCurve.SemilinearAut.instDistribMulActionSubtypeProdRingAutMemSubgroupDivisor AlgebraicCurve.Pic0.instModuleZModTorsion AlgebraicCurve.SemilinearAut.instSMulSubtypeProdRingAutMemSubgroupPlace AlgebraicCurve.SemilinearAut.instDistribMulActionTorsion AlgebraicCurve.SemilinearAut.instSMulSubtypeProdRingAutMemSubgroupPic0 AlgebraicCurve.SemilinearAut.instSMulTorsion AlgebraicCurve.SemilinearAut.instMulActionSubtypeProdRingAutMemSubgroupPlace AlgebraicCurve.SemilinearAut.instSMulCommClassZModTorsion AlgebraicCurve.SemilinearAut.instMulSemiringActionSubtypeProdRingAutMemSubgroup AlgebraicCurve.IsCurveOver.instNontrivialKaehler AlgebraicCurve.IsCurveOver.instFreeKaehler AlgebraicCurve.IsCurveOver.toHasPrincipalDivisors AlgebraicCurve.IsCurveOver.instFiniteResidue CerednikDrinfeld.TwoPlaceTorsionDatum.instAddCommGroup CerednikDrinfeld.TwoPlaceTorsionDatum.instFinite CerednikDrinfeld.JPrimeTorsionDatum.instAddCommGroup CerednikDrinfeld.JPrimeTorsionDatum.instFinite AlgebraicGeometry.SquareZero.isLocalRing' AlgebraicGeometry.SquareZero.isLocalRing"
p2m_attr_erase "simp" "PresheafOfModules.freeεIso_hom_app PresheafOfModules.freeμIso_hom_app GoodReductionJacobian.RelativeGroupLaw.sndPoint_coe GoodReductionJacobian.RelativeGroupLaw.fstPoint_coe GoodReductionJacobian.relativeGroupLawOfGrpObj_inv GoodReductionJacobian.relativeGroupLawOfGrpObj_mul GoodReductionJacobian.overHomEquivSchemeHomOver_apply_coe GoodReductionJacobian.relativeGroupLawOfGrpObj_one GoodReductionJacobian.overHomEquivSchemeHomOver_symm_apply_left GoodReductionJacobian.prodInr_comp_prodFst GoodReductionJacobian.RelativeGroupLaw.prod_inv GoodReductionJacobian.prodInl_comp_prodSnd GoodReductionJacobian.prodInr_comp_prodSnd GoodReductionJacobian.prodInl_comp_prodFst GoodReductionJacobian.prodFstPt_prodPairPt GoodReductionJacobian.prodFst_coe GoodReductionJacobian.prodSndPt_prodPairPt GoodReductionJacobian.RelativeGroupLaw.prod_one GoodReductionJacobian.prodPairPt_coe GoodReductionJacobian.prodPairPt_prodFstPt_prodSndPt GoodReductionJacobian.prodFstPt_coe GoodReductionJacobian.RelativeGroupLaw.prod_mul GoodReductionJacobian.prodSndPt_coe GoodReductionJacobian.prodSnd_coe AlgebraicGeometry.RelPicard.RepresentsRelSubPic.mk.injEq AlgebraicGeometry.RelPicard.SubPicCondition.mk.injEq AlgebraicGeometry.RelPicard.SubPicCondition.mk.sizeOf_spec AlgebraicGeometry.RelPicard.RepresentsRelSubPic.mk.sizeOf_spec AlgebraicGeometry.Scheme.TwoAffineOpenCover.mk.injEq AlgebraicGeometry.Scheme.TwoAffineOpenCover.mk.sizeOf_spec AlgebraicGeometry.Scheme.TwoAffineOpenCover.pullback_U1 AlgebraicGeometry.Scheme.TwoAffineOpenCover.pullback_U0 TwoChartCech.Sections.mk.injEq TwoChartCech.Cover.mk.injEq TwoChartCech.GrothendieckComplex.mk.injEq TwoChartCech.Sections.mk.sizeOf_spec TwoChartCech.Cover.mk.sizeOf_spec TwoChartCech.Cover.lineBundle_r0_apply TwoChartCech.GrothendieckComplex.mk.sizeOf_spec TwoChartCech.Cover.lineBundle_r1_apply"
p2m_attr_erase "simp" "CoherentBaseChange.TwoTermComplex.mk.sizeOf_spec CoherentBaseChange.TwoTermComplex.mk.injEq AlgebraicGeometry.SubalgebraStages.specCone_π_app AlgebraicGeometry.SubalgebraStages.specLeg_specHom AlgebraicGeometry.SubalgebraStages.specLeg_specTrans AlgebraicGeometry.SubalgebraStages.cone_pt AlgebraicGeometry.SubalgebraStages.trans_fst AlgebraicGeometry.SubalgebraStages.diagram_obj AlgebraicGeometry.SubalgebraStages.leg_snd AlgebraicGeometry.SubalgebraStages.diagram_map AlgebraicGeometry.SubalgebraStages.specTrans_refl AlgebraicGeometry.SubalgebraStages.trans_snd AlgebraicGeometry.SubalgebraStages.specTrans_specHom AlgebraicGeometry.SubalgebraStages.specCone_pt AlgebraicGeometry.SubalgebraStages.cone_π_app AlgebraicGeometry.SubalgebraStages.specDiagram_map AlgebraicGeometry.SubalgebraStages.specDiagram_obj AlgebraicGeometry.SubalgebraStages.leg_fst AlgebraicGeometry.SubalgebraStages.leg_trans IsDirectLimit.Module.linearEquiv_symm_apply IsDirectLimit.linearEquiv_symm_apply IsDirectLimit.lift_of IsDirectLimit.Module.linearEquiv_apply IsDirectLimit.Module.lift_of IsDirectLimit.Equiv_apply RegularLocalRingQuotientAscent.dualNumberFst_apply GoodReductionJacobian.RelativeGroupLaw.baseChangePointToBase_ofBase GoodReductionJacobian.RelativeGroupLaw.baseChangePointToBase_coe GoodReductionJacobian.RelativeGroupLaw.baseChangePointOfBase_coe GoodReductionJacobian.RelativeGroupLaw.baseChange_inv GoodReductionJacobian.RelativeGroupLaw.baseChangePointOfBase_toBase GoodReductionJacobian.RelativeGroupLaw.baseChange_mul GoodReductionJacobian.RelativeGroupLaw.baseChange_one NeronSpecialFibreInfra.specialFibreRestrict_coe_comp_fst NeronSpecialFibreInfra.fibreRestrictAlong_coe_comp_snd NeronSpecialFibreInfra.fibreRestrictAlong_coe_comp_fst NeronSpecialFibreInfra.neronEndRestrictEquiv_apply NeronSpecialFibreInfra.fibreRestrictAlong_coe_comp_fst_assoc NeronSpecialFibreInfra.specialFibreRestrict_coe_comp_snd NeronSpecialFibreInfra.neronEndExtension_genericFibreRestrict"
p2m_attr_erase "simp" "NeronSpecialFibreInfra.specClosedFibreInclusion_eq NeronSpecialFibreInfra.specialFibreRestrict_coe_comp_fst_assoc NeronSpecialFibreInfra.specialFibreRestrict_coe_comp_snd_assoc NeronSpecialFibreInfra.genericFibreRestrict_neronEndExtension NeronSpecialFibreInfra.homOverId_coe NeronSpecialFibreInfra.homOverComp_coe NeronSpecialFibreInfra.fibreRestrictAlong_coe_comp_snd_assoc GoodReductionJacobian.RelativeGroupLaw.fibre_inv GoodReductionJacobian.RelativeGroupLaw.fibrePointToBase_coe GoodReductionJacobian.RelativeGroupLaw.fibrePointOfBase_toBase GoodReductionJacobian.RelativeGroupLaw.fibre_mul GoodReductionJacobian.RelativeGroupLaw.fibrePointToBase_ofBase GoodReductionJacobian.RelativeGroupLaw.fibre_one GoodReductionJacobian.RelativeGroupLaw.fibrePointOfBase_coe AlgebraicGeometry.schemeFibreEndo_snd AlgebraicGeometry.schemeFibreEndo_fst AlgebraicGeometry.Scheme.OrderedAffineCover.mk.injEq AlgebraicGeometry.OModulePresheaf.mk.sizeOf_spec AlgebraicGeometry.Scheme.OrderedAffineCover.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.mk.injEq AlgebraicGeometry.OModulePresheaf.prod_obj AlgebraicGeometry.OModulePresheaf.restrOpen_obj AlgebraicGeometry.OModulePresheaf.DevissageStep.mk.injEq AlgebraicGeometry.OModulePresheaf.pushforward_obj AlgebraicGeometry.OModulePresheaf.im_obj AlgebraicGeometry.OModulePresheaf.pow_obj AlgebraicGeometry.OModulePresheaf.fstHom_app AlgebraicGeometry.OModulePresheaf.ker_obj AlgebraicGeometry.OModulePresheaf.coker_obj AlgebraicGeometry.OModulePresheaf.DevissageStep.mk.sizeOf_spec AlgebraicGeometry.Scheme.OrderedAffineCover.preimage_U AlgebraicGeometry.OModulePresheaf.sndHom_app AlgebraicGeometry.OModulePresheaf.Hom.mk.injEq AlgebraicGeometry.OModulePresheaf.Hom.id_app AlgebraicGeometry.OModulePresheaf.AffHom.appSections_apply AlgebraicGeometry.OModulePresheaf.AffHom.comp_app AlgebraicGeometry.OModulePresheaf.AffSES.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.AffHom.kerMap_coe AlgebraicGeometry.OModulePresheaf.AffHom.id_app AlgebraicGeometry.OModulePresheaf.Hom.mk.sizeOf_spec"
p2m_attr_erase "simp" "AlgebraicGeometry.OModulePresheaf.Hom.toAffHom_app AlgebraicGeometry.OModulePresheaf.SES.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.AffHom.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.Hom.comp_app AlgebraicGeometry.OModulePresheaf.SES.mk.injEq AlgebraicGeometry.OModulePresheaf.AffHom.mk.injEq AlgebraicGeometry.OModulePresheaf.Hom.appSections_apply AlgebraicGeometry.OModulePresheaf.AffSES.mk.injEq AlgebraicGeometry.OModulePresheaf.Leray.restrictToPreimage_U AlgebraicGeometry.Scheme.OrderedAffineCover.toCoverOf_U AlgebraicGeometry.Scheme.OrderedAffineCoverOf.mk.sizeOf_spec AlgebraicGeometry.Scheme.OrderedAffineCoverOf.mk.injEq AlgebraicGeometry.Scheme.OrderedAffineCover.restrict_U DoubleComplex.Bounded.mk.injEq DoubleComplex.Bounded.mk.sizeOf_spec DoubleComplex.Convergence.mk.injEq DoubleComplex.Convergence.mk.sizeOf_spec DoubleComplex.SubQuot.mk.sizeOf_spec DoubleComplex.SubQuot.mk.injEq ProjSpaceCech.GradedModule.mk.injEq ProjSpaceCech.GradedModule.mk.sizeOf_spec ProjSpaceCech.GradedModule.Frac.mk.sizeOf_spec ProjSpaceCech.GradedModule.Presentation.mk.injEq ProjSpaceCech.GradedModule.Frac.mk.injEq ProjSpaceCech.GradedModule.Presentation.mk.sizeOf_spec ProjSpaceCech.GradedModule.Hom.shift_toLinearMap ProjSpaceCech.GradedModule.Hom.mk.sizeOf_spec ProjSpaceCech.GradedModule.Hom.mk.injEq AlgebraicGeometry.Scheme.Modules.tensorSections_zero_right AlgebraicGeometry.Scheme.Modules.map_unitSection AlgebraicGeometry.Scheme.Modules.tensorSectionsBilin_apply AlgebraicGeometry.Scheme.Modules.tensorPowSection_zero AlgebraicGeometry.Scheme.Modules.tensorSections_zero_left AlgebraicGeometry.Scheme.Modules.tensorPow_zero AlgebraicGeometry.Scheme.Modules.tensorPow_succ AlgebraicGeometry.Scheme.Modules.glueComponent_glueMk AlgebraicGeometry.Scheme.Modules.UnitCocycle.mk.injEq AlgebraicGeometry.Scheme.Modules.UnitCocycle.mk.sizeOf_spec PresheafOfModules.InternalHom.IsSheafAux.appAt_toPresheafHom SheafOfModules.ihomSectionsEquivFamily_unit"
p2m_attr_erase "simp" "AlgebraicGeometry.Scheme.Modules.restrictHomEquivFamily_apply SheafOfModules.ihomEval_unit_app AlgebraicGeometry.Scheme.Modules.ihomEval_zero_right AlgebraicGeometry.Scheme.Modules.ihomEval_zero_left AlgebraicGeometry.Scheme.Modules.homOfFamily_app_apply SheafOfModules.unit_ihomSectionsEquivFamily AlgebraicGeometry.Scheme.Modules.familyOfHom_app AlgebraicGeometry.Scheme.Modules.restrictUnitIso_hom_app_apply AlgebraicGeometry.Scheme.Modules.restrictUnitIso_inv_app_apply AlgebraicGeometry.Scheme.Modules.restrictHomOfFamily_app_apply AlgebraicGeometry.Scheme.Modules.restrictHomEquivFamily_symm_apply AlgebraicGeometry.tilde.functorCompPullbackSpecIso_app AlgebraicGeometry.Scheme.Hom.kaehlerPresheaf_obj PresheafOfModules.exteriorPower_map_ιMulti PresheafOfModules.ExteriorPower.appₗ_apply AlgebraicGeometry.Scheme.Modules.exteriorPower_obj AlgebraicGeometry.Scheme.OrderedOpenFamily.mk.injEq AlgebraicGeometry.Scheme.OrderedOpenFamily.mk.sizeOf_spec CochainCx.Bounded.mk.sizeOf_spec CochainCx.Bounded.mk.injEq AlgebraicCurve.CurveModel.mk.injEq AlgebraicCurve.CurveModel.mk.sizeOf_spec AlgebraicCurve.Place.mk.injEq AlgebraicCurve.Divisor.degree_single AlgebraicCurve.Divisor.smul_single AlgebraicCurve.Place.smul_toValuationSubring AlgebraicCurve.Place.heightOneSpectrum_asIdeal AlgebraicCurve.Place.coe_algebraMap AlgebraicCurve.Place.ord_one AlgebraicCurve.Place.coe_smulRingEquiv_apply AlgebraicCurve.Pic0.coe_degZeroSMulHom AlgebraicCurve.Place.deg_smul AlgebraicCurve.Pic0.mk_zero AlgebraicCurve.Place.mk.sizeOf_spec AlgebraicCurve.Divisor.degree_smul AlgebraicCurve.Pic0.mk_add AlgebraicCurve.Place.ord_zero AlgebraicCurve.Place.ofHeightOneSpectrum_toValuationSubring AlgebraicCurve.CurveModel.coe_gInf AlgebraicCurve.CurveModel.coe_tInvChart"
p2m_attr_erase "simp" "AlgebraicCurve.CurveModel.ιInf_gluedToBase_assoc AlgebraicCurve.CurveModel.ιInf_gluedToBase AlgebraicCurve.CurveModel.primeOfι₀_asIdeal AlgebraicCurve.CurveModel.coe_tChart AlgebraicCurve.CurveModel.ι₀_gluedToBase_assoc AlgebraicCurve.CurveModel.primeOfιInf_asIdeal AlgebraicCurve.CurveModel.ι₀_gluedToBase AlgebraicCurve.CurveModel.coe_tma AlgebraicCurve.CurveModel.coe_primeEquivChartPlaces AlgebraicCurve.Place.congrEquiv_symm_apply AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply AlgebraicCurve.RationalFunctionField.deg_placeOfPoint CerednikDrinfeld.QM.FakeEllipticCurve.FullLevel.mk.sizeOf_spec CerednikDrinfeld.QM.FakeEllipticCurve.FullLevel.mk.injEq CerednikDrinfeld.QM.FakeEllipticCurve.ExtraLevel.mk.injEq CerednikDrinfeld.QM.FakeEllipticCurve.ExtraLevel.mk.sizeOf_spec CerednikDrinfeld.ShimuraCurveModel.ModuliWitness.mk.injEq CerednikDrinfeld.QM.mapPt_coe CerednikDrinfeld.QM.FakeEllipticCurve.mk.injEq CerednikDrinfeld.QM.FakeEllipticCurve.mk.sizeOf_spec CerednikDrinfeld.ShimuraCurveModel.ModuliWitness.mk.sizeOf_spec CerednikDrinfeld.ShimuraCurveModel.mk.injEq CerednikDrinfeld.ShimuraCurveModel.coe_torsionHecke_apply CerednikDrinfeld.ShimuraCurveModel.galJ_apply CerednikDrinfeld.ShimuraCurveModel.heckeGenJ_apply CerednikDrinfeld.ShimuraCurveModel.coe_torsionGal_apply CerednikDrinfeld.ShimuraCurveModel.mk.sizeOf_spec CerednikDrinfeld.ShimuraCurveModel.signTwist_heckeGen CerednikDrinfeld.ShimuraCurveModel.coe_restrictTors_apply Submodule.finiteAdeleEvalAt_tmul Submodule.val_finiteIdeleDiagonal_apply QuaternionAlgebra.nrd_coe QuaternionAlgebra.nrd_one QuaternionAlgebra.trd_mk QuaternionAlgebra.nrd_mk QuaternionAlgebra.nrd_neg QuaternionAlgebra.nrd_zero"
p2m_attr_erase "simp" "QuaternionAlgebra.nrd_star ModularCurve.UniformizedHeckeCurve.mk.sizeOf_spec ModularCurve.UniformizedHeckeCurve.mk.injEq ModularCurve.ComplexPlaceDictionary.mk.injEq ModularCurve.ComplexPlaceDictionary.mk.sizeOf_spec ModularCurve.qExpand_coeff_mul ModularCurve.qExpandₐ_apply ModularCurve.jqN_one ModularCurve.qExpand_single ModularCurve.dedekindPsi_one ModularCurve.ModularPolynomialData.mk.sizeOf_spec ModularCurve.evalAtJ_X ModularCurve.ModularPolynomialData.mk.injEq ModularCurve.constantCoeff_jNum ModularCurve.constantCoeff_eisenstein4 ModularCurve.qExpand_C ModularCurve.coeff_jq_neg_one ModularCurve.constantCoeff_jNumQ ModularCurve.coeffEmb_coeff ModularCurve.coeffMap_coeff ModularCurve.coeffMap_id ModularCurve.coeffMap_single ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL AlgebraicCurve.SemilinearAut.toRingAut_inv AlgebraicCurve.SemilinearAut.smul_def AlgebraicCurve.SemilinearAut.smul_single AlgebraicCurve.SemilinearAut.smul_toValuationSubring AlgebraicCurve.SemilinearAut.baseAut_inv AlgebraicCurve.SemilinearAut.baseAut_ofAlgAut AlgebraicCurve.SemilinearAut.toRingAut_ofAlgAut AlgebraicCurve.SemilinearAut.torsionRep_apply AlgebraicCurve.SemilinearAut.toRingAut_one"
p2m_attr_erase "simp" "AlgebraicCurve.SemilinearAut.deg_smul AlgebraicCurve.SemilinearAut.degree_smul AlgebraicCurve.SemilinearAut.coe_degZeroSMulHom AlgebraicCurve.SemilinearAut.baseAut_mul AlgebraicCurve.SemilinearAut.coe_smulValuationSubringEquiv_apply AlgebraicCurve.SemilinearAut.baseAut_one AlgebraicCurve.SemilinearAut.ofAlgAut_smul AlgebraicCurve.SemilinearAut.coe_torsion_smul AlgebraicCurve.SemilinearAut.toRingAut_mul CerednikDrinfeld.TwoPlaceTorsionDatum.snd_T CerednikDrinfeld.TwoPlaceTorsionDatum.snd_toric CerednikDrinfeld.TwoPlaceTorsionDatum.mk.injEq CerednikDrinfeld.TwoPlaceTorsionDatum.fst_T CerednikDrinfeld.TwoPlaceTorsionDatum.mk.sizeOf_spec CerednikDrinfeld.TwoPlaceTorsionDatum.fst_D CerednikDrinfeld.TwoPlaceTorsionDatum.snd_D CerednikDrinfeld.TwoPlaceTorsionDatum.fst_toric CerednikDrinfeld.HeckeData.mk.sizeOf_spec CerednikDrinfeld.Matching.mk.injEq CerednikDrinfeld.DegeneracyData.mk.sizeOf_spec CerednikDrinfeld.DegeneracyData.mk.injEq CerednikDrinfeld.ribbonGram_apply CerednikDrinfeld.HeckeData.mk.injEq CerednikDrinfeld.Matching.mk.sizeOf_spec ModularCurve.widthPairing_apply ModularCurve.gramMap_apply ModularCurve.degreeOn_apply ModularCurve.aeval_heckeGen ModularCurve.coe_mTorsionGaloisRep_apply ModularCurve.eisensteinSystem_of_dvd ModularCurve.eisensteinSystem_of_not_dvd AlgebraicGeometry.TangentPoints.map_coe AlgebraicGeometry.SquareZero.basePoint_toBase_assoc AlgebraicGeometry.SquareZero.basePoint_toBase AlgebraicGeometry.SquareZero.basePoint_specMap AlgebraicGeometry.SquareZero.basePointOver_coe AlgebraicGeometry.SquareZero.specMap_toBase_assoc AlgebraicGeometry.SquareZero.specMapOver_coe AlgebraicGeometry.RelPicard.TrivialModDeformations.map_coe AlgebraicGeometry.SquareZero.specMap_toBase"
p2m_attr_erase "simp" "AlgebraicGeometry.SquareZero.basePoint_specMap_assoc"

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian AlgebraicGeometry.Polarisation
p2m_open_scoped "BigOperators CategoryTheory.MonoidalCategory TensorProduct"

namespace MUnit

theorem exists_ringHom_comp_eq {S S' K : Type} [CommRing S] [CommRing S'] [Algebra S S'] [Module.FaithfullyFlat S S']
    [Algebra.FiniteType S S'] [Field K] [IsAlgClosed K] (φ : S →+* K) :
    ∃ σ : S' →+* K, σ.comp (algebraMap S S') = φ := by
  classical
  letI : Algebra S K := φ.toAlgebra
  haveI : Nontrivial (K ⊗[S] S') := inferInstance
  obtain ⟨𝔪, h𝔪⟩ := Ideal.exists_maximal (K ⊗[S] S')
  letI : Field ((K ⊗[S] S') ⧸ 𝔪) := Ideal.Quotient.field 𝔪
  haveI : Module.Finite K ((K ⊗[S] S') ⧸ 𝔪) := finite_of_finite_type_of_isJacobsonRing K _
  have hbij := IsAlgClosed.algebraMap_bijective_of_isIntegral (k := K) (K := (K ⊗[S] S') ⧸ 𝔪)
  let e : K ≃+* ((K ⊗[S] S') ⧸ 𝔪) := RingEquiv.ofBijective (algebraMap K ((K ⊗[S] S') ⧸ 𝔪)) hbij
  refine ⟨(e.symm : ((K ⊗[S] S') ⧸ 𝔪) →+* K).comp ((Ideal.Quotient.mk 𝔪).comp
    (Algebra.TensorProduct.includeRight : S' →ₐ[S] K ⊗[S] S').toRingHom), ?_⟩
  ext s
  have h1 : (Algebra.TensorProduct.includeRight : S' →ₐ[S] K ⊗[S] S') (algebraMap S S' s) = algebraMap K (K ⊗[S] S') (φ s) := by
    change (1 : K) ⊗ₜ[S] (algebraMap S S' s) = algebraMap K (K ⊗[S] S') (algebraMap S K s)
    simp [Algebra.algebraMap_eq_smul_one, Algebra.TensorProduct.one_def]
  change e.symm (Ideal.Quotient.mk 𝔪 ((Algebra.TensorProduct.includeRight : S' →ₐ[S] K ⊗[S] S') (algebraMap S S' s))) = φ s
  rw [h1, ← Ideal.Quotient.algebraMap_eq, ← IsScalarTower.algebraMap_apply]
  exact e.symm_apply_apply (φ s)

theorem memKernel_congr {S : Type} [CommRing S] {A : Scheme.{0}} (f : A ⟶ Spec (CommRingCat.of S)) (L : RelativeGroupLaw S f)
    (𝓛 : A.Modules) {R : Type} [CommRing R] {t₁ t₂ : Spec (CommRingCat.of R) ⟶ Spec (CommRingCat.of S)} (h : t₁ = t₂)
    (p : Spec (CommRingCat.of R) ⟶ A) (h₁ : p ≫ f = t₁) (h₂ : p ≫ f = t₂) :
    Polarisation.MemKernel f L 𝓛 t₁ ⟨p, h₁⟩ ↔ Polarisation.MemKernel f L 𝓛 t₂ ⟨p, h₂⟩ := by
  subst h; rfl

theorem memKernel_iff_of_locIsoOnBase {S : Type} [CommRing S] {A : Scheme.{0}} (f : A ⟶ Spec (CommRingCat.of S))
    (L : RelativeGroupLaw S f) {𝓛 𝓜 : A.Modules} (h𝓛 : Scheme.Modules.IsInvertible 𝓛) (h𝓜 : Scheme.Modules.IsInvertible 𝓜)
    (h : LocIsoOnBase f 𝓛 𝓜) {R : Type} [CommRing R] (t : Spec (CommRingCat.of R) ⟶ Spec (CommRingCat.of S))
    (y : SchemeHomOver t f) : MemKernel f L 𝓛 t y ↔ MemKernel f L 𝓜 t y := by
  have hΛ := LocIsoOnBase.mumfordBundle_of_isInvertible f L h𝓛 h𝓜 h
  have comm : sliceAt f y ≫ (pullback.fst f f ≫ f) = pullback.snd f t ≫ t := by
    rw [← Category.assoc, sliceAt, pullback.lift_fst, pullback.condition]
  have hs := LocIsoOnBase.pullback_of_comp_eq (pullback.snd f t) (sliceAt f y) t comm hΛ
  have E := LocIsoOnBase.equivalence (pullback.snd f t)
  constructor
  · intro hk; exact E.trans (E.symm hs) hk
  · intro hk; exact E.trans hs hk

theorem isInvertible_tpow {X : Scheme.{0}} (M : X.Modules) (hM : Scheme.Modules.IsInvertible M) (n : ℕ) :
    Scheme.Modules.IsInvertible (Scheme.Modules.tpow M n) := by
  induction n with
  | zero => exact Scheme.Modules.isInvertible_unit X
  | succ n ih => exact ih.tensor_monoidalV2 hM

theorem epi_spec_away {R : Type} [CommRing R] (s : R) (hs : IsUnit s) :
    Epi (Spec.map (CommRingCat.ofHom (algebraMap R (Localization.Away s)))) := by
  have hbij : Function.Bijective (algebraMap R (Localization.Away s)) := by
    have e := IsLocalization.atUnits R (Submonoid.powers s) (S := Localization.Away s)
      (by rintro z ⟨k, rfl⟩; exact hs.pow k)
    have : (algebraMap R (Localization.Away s) : R → _) = e := by
      ext z; exact (e.commutes z).symm
    rw [this]; exact e.bijective
  haveI : IsIso (CommRingCat.ofHom (algebraMap R (Localization.Away s))) :=
    (RingEquiv.ofBijective _ hbij).toCommRingCatIso.isIso_hom
  infer_instance

theorem exists_isUnit_of_span_eq_top {R : Type} [CommRing R] [IsLocalRing R] {m : ℕ} (r : Fin m → R)
    (hr : Ideal.span (Set.range r) = ⊤) : ∃ j, IsUnit (r j) := by
  by_contra hne
  have hle : Ideal.span (Set.range r) ≤ IsLocalRing.maximalIdeal R := by
    rw [Ideal.span_le]; rintro _ ⟨j, rfl⟩
    exact (IsLocalRing.mem_maximalIdeal _).2 (fun hu' => hne ⟨j, hu'⟩)
  rw [hr, top_le_iff] at hle
  exact (IsLocalRing.maximalIdeal.isMaximal R).ne_top hle

theorem main
    {g d n : ℕ} (δ : Fin g → ℕ) [∀ i, NeZero (δ i)] (hδd : ∏ i, δ i = d)
    {S : Type} [CommRing S] (hd : IsUnit ((d : ℕ) : S))
    (u : PolarisedAbelianScheme g d n S)
    {K : Type} [Field K] [IsAlgClosed K] (t : Spec (CommRingCat.of K) ⟶ Spec (CommRingCat.of S))

    (L' : RelativeGroupLaw K (pullback.snd u.f t))
    (hL' : ∀ (T : Scheme.{0}) (t' : T ⟶ Spec (CommRingCat.of K)) (P Q : SchemeHomOver t' (pullback.snd u.f t)),
      (L'.mul t' P Q).1 ≫ pullback.fst u.f t =
        (u.L.mul (t' ≫ t)
          ⟨P.1 ≫ pullback.fst u.f t, by rw [Category.assoc, pullback.condition, ← Category.assoc, P.2]⟩
          ⟨Q.1 ≫ pullback.fst u.f t, by rw [Category.assoc, pullback.condition, ← Category.assoc, Q.2]⟩).1)
    (𝓛₀ : (pullback u.f t).Modules) (a b : ℕ) (hab : 1 ≤ a + b) (h𝓛₀ : Scheme.Modules.IsInvertible 𝓛₀)
    (hker : Polarisation.KernelTrivial (pullback.snd u.f t) L' 𝓛₀)
    (hroot : Polarisation.LocIsoOnBase (pullback.snd u.f t)
      ((Scheme.Modules.pullback (pullback.fst u.f t)).obj u.pol)
      (Scheme.Modules.tpow 𝓛₀ a ⊗ Scheme.Modules.tpow ((Scheme.Modules.pullback (Polarisation.negMor (pullback.snd u.f t) L')).obj 𝓛₀) b))
    (hu : PolarisedAbelianScheme.RootedSymmetricOfType δ S u) (hg : 0 < g) :
    ((a + b : ℕ) : K) ≠ 0 := by
  classical

  obtain ⟨φ₀, rfl⟩ : ∃ φ₀ : S →+* K, Spec.map (CommRingCat.ofHom φ₀) = t :=
    ⟨(Spec.preimage t).hom, by rw [CommRingCat.ofHom_hom]; exact Spec.map_preimage t⟩
  intro hzero

  have hX := IsPullback.of_hasPullback u.f (Spec.map (CommRingCat.ofHom φ₀))
  have hA' : AbelianSchemePropertyBundle K (pullback.snd u.f (Spec.map (CommRingCat.ofHom φ₀))) := u.bundle.of_isPullback hX
  have hc' : L'.IsCommutative := hA'.isCommutative L'
  haveI := u.bundle.smooth
  have hdim' := AlgebraicGeometry.topologicalKrullDim_preimage_pullback_snd_eq_of_smooth_of_isConnected φ₀ u.f u.bundle.connectedFibres g u.dim_fibre

  obtain ⟨y, hyn, hyred, hyne⟩ := GoodReductionJacobian.AbelianSchemePropertyBundle.exists_nsmul_eq_one_dualNumber_ne_one_of_natCast_eq_zero L' hc' hA' g hdim' hg (a + b) (by exact_mod_cast hzero)
  apply hyne

  have hmemT := (AlgebraicGeometry.Polarisation.memKernel_tpow_tensor_tpow_pullback_negMor_iff_memKernel_nsmul_add (pullback.snd u.f (Spec.map (CommRingCat.ofHom φ₀))) L' hc' hA' 𝓛₀ h𝓛₀ a b hab
      (DualNumber K) (Spec.map (CommRingCat.ofHom (algebraMap K (DualNumber K)))) y).2
      (by rw [hyn]; exact AlgebraicGeometry.Polarisation.locIsoOnBase_pullback_sliceAt_mumfordBundle_one_unit_of_commRing _ L' 𝓛₀ h𝓛₀ _ _)

  have hinvT : Scheme.Modules.IsInvertible (Scheme.Modules.tpow 𝓛₀ a ⊗
      Scheme.Modules.tpow ((Scheme.Modules.pullback (Polarisation.negMor (pullback.snd u.f (Spec.map (CommRingCat.ofHom φ₀))) L')).obj 𝓛₀) b) :=
    (isInvertible_tpow _ h𝓛₀ a).tensor_monoidalV2 (isInvertible_tpow _ (h𝓛₀.pullback _) b)
  have hmemP := (memKernel_iff_of_locIsoOnBase (pullback.snd u.f (Spec.map (CommRingCat.ofHom φ₀))) L'
      (u.pol_isInvertible.pullback _) hinvT hroot _ y).2 hmemT

  have hmemA := (AlgebraicGeometry.Polarisation.memKernel_iff_memKernel_comp_of_isPullback φ₀ hX u.L L' (fun t' P Q => hL' _ t' P Q) u.pol u.pol_isInvertible _ (Iso.refl _)
      (Spec.map (CommRingCat.ofHom (algebraMap K (DualNumber K)))) y).1 hmemP

  obtain ⟨S', _, _, _, _, x', -, -, hmem⟩ := hu.2.1
  haveI : Algebra.FiniteType S S' := inferInstance
  obtain ⟨σ, hσ⟩ := exists_ringHom_comp_eq (S := S) (S' := S') (K := K) φ₀
  letI instKε : Algebra S' (DualNumber K) := ((algebraMap K (DualNumber K)).comp σ).toAlgebra
  have hbase : Spec.map (CommRingCat.ofHom ((algebraMap S' (DualNumber K)).comp (algebraMap S S'))) =
      Spec.map (CommRingCat.ofHom (algebraMap K (DualNumber K))) ≫ Spec.map (CommRingCat.ofHom φ₀) := by
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
    congr 2
    change ((algebraMap K (DualNumber K)).comp σ).comp (algebraMap S S') = (algebraMap K (DualNumber K)).comp φ₀
    rw [RingHom.comp_assoc, hσ]
  have hyS : (y.1 ≫ pullback.fst u.f (Spec.map (CommRingCat.ofHom φ₀))) ≫ u.f =
      Spec.map (CommRingCat.ofHom (algebraMap K (DualNumber K))) ≫ Spec.map (CommRingCat.ofHom φ₀) := by
    rw [Category.assoc, hX.w, ← Category.assoc, y.2]
  obtain ⟨m, r, hr, hloc⟩ := (hmem (DualNumber K) ⟨y.1 ≫ pullback.fst u.f _, by rw [hbase]; exact hyS⟩).1
    ((memKernel_congr u.f u.L u.pol hbase _ (by rw [hbase]; exact hyS) hyS).2 hmemA)

  obtain ⟨j, hj⟩ := exists_isUnit_of_span_eq_top r hr
  obtain ⟨h, hh⟩ := hloc j
  have hepi := epi_spec_away (r j) hj

  have hyfst : y.1 ≫ pullback.fst u.f (Spec.map (CommRingCat.ofHom φ₀)) =
      Spec.map (CommRingCat.ofHom (algebraMap K (DualNumber K))) ≫ (Spec.map (CommRingCat.ofHom σ) ≫ (x' h).1) := by
    conv at hh => rhs; rw [CommRingCat.ofHom_comp, Spec.map_comp, Category.assoc]
    have h3 : y.1 ≫ pullback.fst u.f (Spec.map (CommRingCat.ofHom φ₀)) =
        Spec.map (CommRingCat.ofHom (algebraMap S' (DualNumber K))) ≫ (x' h).1 := hepi.left_cancellation _ _ hh
    rw [h3, ← Category.assoc, ← Spec.map_comp, ← CommRingCat.ofHom_comp]

  have hρ : Spec.map (CommRingCat.ofHom (TrivSqZeroExt.fstHom K K K).toRingHom) ≫
      Spec.map (CommRingCat.ofHom (algebraMap K (DualNumber K))) = 𝟙 _ := by
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
    have : (TrivSqZeroExt.fstHom K K K).toRingHom.comp (algebraMap K (DualNumber K)) = RingHom.id K := by
      ext z; simp
    rw [this, CommRingCat.ofHom_id, Spec.map_id]
  have hz : Spec.map (CommRingCat.ofHom σ) ≫ (x' h).1 =
      (L'.one (𝟙 (Spec (CommRingCat.of K)))).1 ≫ pullback.fst u.f (Spec.map (CommRingCat.ofHom φ₀)) := by
    have := congrArg (fun q => Spec.map (CommRingCat.ofHom (TrivSqZeroExt.fstHom K K K).toRingHom) ≫ q) hyfst
    simp only [← Category.assoc] at this
    rw [hρ, Category.id_comp, hyred] at this
    exact this.symm

  apply Subtype.ext
  apply pullback.hom_ext
  · rw [hyfst, hz, ← Category.assoc]
    have h1 := L'.one_natural (𝟙 (Spec (CommRingCat.of K))) (Spec.map (CommRingCat.ofHom (algebraMap K (DualNumber K))))
      (Spec.map (CommRingCat.ofHom (algebraMap K (DualNumber K)))) (Category.comp_id _)
    have h1' : Spec.map (CommRingCat.ofHom (algebraMap K (DualNumber K))) ≫ (L'.one (𝟙 (Spec (CommRingCat.of K)))).1 =
        (L'.one (Spec.map (CommRingCat.ofHom (algebraMap K (DualNumber K))))).1 := congrArg Subtype.val h1
    rw [h1']
  · rw [y.2, (L'.one _).2]

end MUnit

theorem solution
    {g d n : ℕ} (δ : Fin g → ℕ) [∀ i, NeZero (δ i)] (hδd : ∏ i, δ i = d)
    {S : Type} [CommRing S] (hd : IsUnit ((d : ℕ) : S))
    (u : PolarisedAbelianScheme g d n S)
    {K : Type} [Field K] [IsAlgClosed K] (t : Spec (CommRingCat.of K) ⟶ Spec (CommRingCat.of S))

    (L' : RelativeGroupLaw K (pullback.snd u.f t))
    (hL' : ∀ (T : Scheme.{0}) (t' : T ⟶ Spec (CommRingCat.of K)) (P Q : SchemeHomOver t' (pullback.snd u.f t)),
      (L'.mul t' P Q).1 ≫ pullback.fst u.f t =
        (u.L.mul (t' ≫ t)
          ⟨P.1 ≫ pullback.fst u.f t, by rw [Category.assoc, pullback.condition, ← Category.assoc, P.2]⟩
          ⟨Q.1 ≫ pullback.fst u.f t, by rw [Category.assoc, pullback.condition, ← Category.assoc, Q.2]⟩).1)
    (𝓛₀ : (pullback u.f t).Modules) (a b : ℕ) (hab : 1 ≤ a + b) (h𝓛₀ : Scheme.Modules.IsInvertible 𝓛₀)
    (hker : Polarisation.KernelTrivial (pullback.snd u.f t) L' 𝓛₀)
    (hroot : Polarisation.LocIsoOnBase (pullback.snd u.f t)
      ((Scheme.Modules.pullback (pullback.fst u.f t)).obj u.pol)
      (Scheme.Modules.tpow 𝓛₀ a ⊗ Scheme.Modules.tpow ((Scheme.Modules.pullback (Polarisation.negMor (pullback.snd u.f t) L')).obj 𝓛₀) b))
    (hu : PolarisedAbelianScheme.RootedSymmetricOfType δ S u) (hg : 0 < g) :
    ((a + b : ℕ) : K) ≠ 0 :=
  MUnit.main δ hδd hd u t L' hL' 𝓛₀ a b hab h𝓛₀ hker hroot hu hg

end S_AlgebraicGeometry_PolarisedAbelianScheme_natCast_add_ne_zero_of_principalRoot_of_rootedSymmetricOfType_of_isAlgClosed
end P2MW
export P2MW.S_AlgebraicGeometry_PolarisedAbelianScheme_natCast_add_ne_zero_of_principalRoot_of_rootedSymmetricOfType_of_isAlgClosed (solution)
