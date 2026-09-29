-- Prove2me | solution 1 for AlgebraicGeometry.Polarisation.locIsoOnBase_pullback_negMor_prod_sliceAt_mumfordBundle_dual_of_commRing
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:02.935278+00:00
-- url     : https://prove2.me/submissions/dba55c66-c5fa-56df-96b6-c6c18509fe6f

import Definitions.Def_AlgebraicGeometry_PolarisationPicZero
import Definitions.Def_AlgebraicGeometry_PolarisationRosati
import Definitions.Def_AlgebraicGeometry_ModulesPullbackMonoidalV2
import Definitions.Def_AlgebraicGeometry_RelativeGroupLawGrpObj
import Theorems.Thm_AlgebraicGeometry_Polarisation_LocIsoOnBase_equivalence
import Theorems.Thm_AlgebraicGeometry_Polarisation_LocIsoOnBase_tensor
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_IsInvertible_tensor_monoidalV2
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_IsInvertible_dual_monoidalV2
import Theorems.Thm_AlgebraicGeometry_Polarisation_nonempty_pullback_mul_mul_tensor_iso_tensor_pullback_one_of_commRing
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_Polarisation_locIsoOnBase_pullback_negMor_prod_sliceAt_mumfordBundle_dual_of_commRing
p2m_attr_erase "instance" "TwoChartCech.Sections.M0_moduleA TwoChartCech.Sections.M1_module TwoChartCech.Cover.A01_algebra TwoChartCech.Cover.A0_algebra TwoChartCech.Cover.A1_commRing TwoChartCech.Cover.A1_algebra TwoChartCech.Sections.M01_module TwoChartCech.Sections.M0_addCommGroup TwoChartCech.Sections.M0_tower TwoChartCech.Sections.M01_addCommGroup TwoChartCech.Cover.A0_commRing TwoChartCech.Sections.M1_tower TwoChartCech.Sections.M01_moduleA TwoChartCech.Sections.M0_module TwoChartCech.Sections.M1_moduleA TwoChartCech.Sections.M1_addCommGroup TwoChartCech.Cover.A01_commRing TwoChartCech.Sections.M01_tower CoherentBaseChange.TwoTermComplex.C0_module CoherentBaseChange.TwoTermComplex.C0_addCommGroup CoherentBaseChange.TwoTermComplex.C1_module CoherentBaseChange.TwoTermComplex.C1_addCommGroup CoherentBaseChange.TwoTermComplex.C0_free CoherentBaseChange.TwoTermComplex.C1_finite CoherentBaseChange.TwoTermComplex.C0_finite CoherentBaseChange.TwoTermComplex.C1_free AlgebraicGeometry.SubalgebraStages.compactSpace_pullback AlgebraicGeometry.SubalgebraStages.quasiSeparatedSpace_pullback AlgebraicGeometry.SubalgebraStages.compactSpace_obj AlgebraicGeometry.SubalgebraStages.quasiSeparatedSpace_obj AlgebraicGeometry.SubalgebraStages.quasiCompact_snd AlgebraicGeometry.SubalgebraStages.isAffineHom_leg AlgebraicGeometry.SubalgebraStages.isAffineHom_trans AlgebraicGeometry.SubalgebraStages.isAffineHom_diagram_map AlgebraicGeometry.SubalgebraStages.quasiSeparated_snd AlgebraicGeometry.SubalgebraStages.isCofiltered_op IsDirectLimit.Module.instDirectLimitCoeLinearMapIdOfOfNonempty AdicCompletion.instIsLocalRingMaximalIdeal AlgebraicGeometry.OModulePresheaf.isScalarTower AlgebraicGeometry.Scheme.OrderedAffineCover.instLinearOrder"
p2m_attr_erase "instance" "AlgebraicGeometry.OModulePresheaf.module AlgebraicGeometry.Scheme.OrderedAffineCover.instFintype AlgebraicGeometry.Scheme.OrderedAffineCover.instFintypeIdx AlgebraicGeometry.OModulePresheaf.addCommGroup AlgebraicGeometry.Scheme.OrderedAffineCover.instDecidableEqIdx AlgebraicGeometry.OModulePresheaf.moduleSections AlgebraicGeometry.OModulePresheaf.instSubsingletonObjZero AlgebraicGeometry.OModulePresheaf.Leray.relAltC_scalarTower AlgebraicGeometry.OModulePresheaf.Leray.ker_relAltd_modΓ AlgebraicGeometry.OModulePresheaf.Leray.relAltC_modΓ AlgebraicGeometry.OModulePresheaf.Leray.biC_abGrp AlgebraicGeometry.OModulePresheaf.Leray.relAltH_modΓ AlgebraicGeometry.OModulePresheaf.Leray.ker_relAltd_smul AlgebraicGeometry.OModulePresheaf.Leray.relAltH_scalarTower AlgebraicGeometry.OModulePresheaf.Leray.relAltH_smul AlgebraicGeometry.OModulePresheaf.Leray.biC_module AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instDecidableEqIdx AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instFintype AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instLinearOrder AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instFintypeIdx DoubleComplex.instModuleE₂I DoubleComplex.Bounded.modR DoubleComplex.instModuleE₂II DoubleComplex.instAddCommGroupE₂II DoubleComplex.Bounded.abGrp DoubleComplex.instAddCommGroupE₂I ProjSpaceCech.GradedModule.H.module ProjSpaceCech.GradedModule.H.addCommGroup ProjSpaceCech.GradedModule.sec.instAdd ProjSpaceCech.GradedModule.sec.instNeg ProjSpaceCech.GradedModule.acg ProjSpaceCech.GradedModule.Frac.setoid ProjSpaceCech.GradedModule.modR ProjSpaceCech.GradedModule.sec.instModule ProjSpaceCech.GradedModule.sec.instAddCommGroup ProjSpaceCech.GradedModule.sec.instZero ProjSpaceCech.GradedModule.Presentation.fJ ProjSpaceCech.GradedModule.sec.instSMul ProjSpaceCech.Twist.H.module ProjSpaceCech.Idx.instFintype"
p2m_attr_erase "instance" "ProjSpaceCech.Twist.H.addCommGroup ProjSpaceCech.Idx.instDecidableEq ProjSpaceCech.Twist.Mon.instDecidableEq ProjSpaceCech.Twist.cochain.instAddCommGroup ProjSpaceCech.Twist.cochain.instModule AlgebraicGeometry.Scheme.Modules.GlueOfCocycle.instSMulCarrierObjOppositeOpensCarrierCarrierCommRingCatPresheafOpOpensSubtypeForallMinMemAddSubgroupFamilies AlgebraicGeometry.Scheme.Modules.GlueOfCocycle.instModulePreGlue AlgebraicGeometry.Scheme.Modules.GlueOfCocycle.instModuleCarrierObjOppositeOpensCarrierCarrierCommRingCatPresheafOpOpensSubtypeForallMinMemAddSubgroupFamilies SheafOfModules.isIso_ihomModelToIhom PresheafOfModules.ExteriorPower.instModulePresheafAb AlgebraicGeometry.Scheme.OrderedOpenFamily.instFintype AlgebraicGeometry.Scheme.OrderedOpenFamily.instDecidableEqIdx AlgebraicGeometry.Scheme.OrderedOpenFamily.instLinearOrder AlgebraicGeometry.Scheme.OrderedOpenFamily.instFintypeIdx CochainCx.Bounded.abGrp CochainCx.Bounded.modR instTopologicallyFGOfFiniteType AlgebraicCurve.CurveModel.isProper AlgebraicCurve.CurveModel.isIntegral AlgebraicCurve.CurveModel.smooth AlgebraicCurve.Place.instIsScalarTowerSubtypeMemValuationSubringToValuationSubring AlgebraicCurve.Divisor.instDistribMulActionAlgEquiv AlgebraicCurve.Place.instSMulAlgEquiv AlgebraicCurve.Place.instIsPrincipalIdealRingSubtypeMemValuationSubringToValuationSubring AlgebraicCurve.Place.instIsDiscreteValuationRingSubtypeMemValuationSubringToValuationSubring AlgebraicCurve.Pic0.instDistribMulActionAlgEquiv AlgebraicCurve.Place.instAlgebraSubtypeMemValuationSubringToValuationSubring AlgebraicCurve.Place.instMulActionAlgEquiv AlgebraicCurve.Pic0.instSMulAlgEquiv AlgebraicCurve.CurveModel.locallyOfFiniteType_gluedToBase AlgebraicCurve.CurveModel.isFractionRing_overlap AlgebraicCurve.CurveModel.isLocallyNoetherian_glued AlgebraicCurve.CurveModel.jacobsonSpace_glued AlgebraicCurve.CurveModel.isOpenImmersion_ι₀ AlgebraicCurve.CurveModel.isIntegral_glued AlgebraicCurve.CurveModel.quasiSeparated_gluedToBase AlgebraicCurve.CurveModel.compactSpace_glued AlgebraicCurve.CurveModel.isIntegral_adjoin_chartRing AlgebraicCurve.CurveModel.isFractionRing_overlap_functionField AlgebraicCurve.CurveModel.isProper_gluedToBase"
p2m_attr_erase "instance" "AlgebraicCurve.CurveModel.isOpenImmersion_ιU AlgebraicCurve.CurveModel.isOpenImmersion_f₀ AlgebraicCurve.CurveModel.isOpenImmersion_fInf AlgebraicCurve.CurveModel.isOpenImmersion_ιInf AlgebraicCurve.CurveModel.algebra_overlap_functionField AlgebraicCurve.CurveModel.quasiCompact_gluedToBase AlgebraicCurve.CurveModel.algebraAdjoin AlgebraicCurve.CurveModel.isDedekindDomain_chartRing AlgebraicCurve.CurveModel.isIntegralClosure AlgebraicCurve.CurveModel.finite_chartRing AlgebraicCurve.CurveModel.centre_isPrime AlgebraicCurve.CurveModel.isFractionRing_chartRing AlgebraicCurve.CurveModel.finiteType_chartRing AlgebraicCurve.CurveModel.isNoetherianRing_chartRing AlgebraicCurve.CurveModel.isScalarTower_base_adjoin AlgebraicCurve.CurveModel.isScalarTower_adjoin AlgebraicCurve.CurveModel.chartRing_finitePresentation AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation"
p2m_attr_erase "simp" "GoodReductionJacobian.prodInr_comp_prodFst GoodReductionJacobian.RelativeGroupLaw.prod_inv GoodReductionJacobian.prodInl_comp_prodSnd GoodReductionJacobian.prodInr_comp_prodSnd GoodReductionJacobian.prodInl_comp_prodFst GoodReductionJacobian.prodFstPt_prodPairPt GoodReductionJacobian.prodFst_coe GoodReductionJacobian.prodSndPt_prodPairPt GoodReductionJacobian.RelativeGroupLaw.prod_one GoodReductionJacobian.prodPairPt_coe GoodReductionJacobian.prodPairPt_prodFstPt_prodSndPt GoodReductionJacobian.prodFstPt_coe GoodReductionJacobian.RelativeGroupLaw.prod_mul GoodReductionJacobian.prodSndPt_coe GoodReductionJacobian.prodSnd_coe NeronModelInfra.NeronModelPropertyBundle.endExtensionEquiv_symm_restrict NeronModelInfra.schemeHomOverComp_id_left NeronModelInfra.schemeHomOverComp_id_right NeronModelInfra.schemeHomOverId_coe NeronModelInfra.NeronModelPropertyBundle.endExtensionEquiv_apply NeronModelInfra.NeronModelPropertyBundle.restrict_endExtensionEquiv_symm NeronModelInfra.schemeHomOverComp_coe AlgebraicGeometry.RelPicard.RepresentsRelSubPic.mk.injEq AlgebraicGeometry.RelPicard.SubPicCondition.mk.injEq AlgebraicGeometry.RelPicard.SubPicCondition.mk.sizeOf_spec AlgebraicGeometry.RelPicard.RepresentsRelSubPic.mk.sizeOf_spec AlgebraicGeometry.Scheme.TwoAffineOpenCover.mk.injEq AlgebraicGeometry.Scheme.TwoAffineOpenCover.mk.sizeOf_spec AlgebraicGeometry.Scheme.TwoAffineOpenCover.pullback_U1 AlgebraicGeometry.Scheme.TwoAffineOpenCover.pullback_U0 TwoChartCech.Sections.mk.injEq TwoChartCech.Cover.mk.injEq TwoChartCech.GrothendieckComplex.mk.injEq TwoChartCech.Sections.mk.sizeOf_spec TwoChartCech.Cover.mk.sizeOf_spec TwoChartCech.Cover.lineBundle_r0_apply TwoChartCech.GrothendieckComplex.mk.sizeOf_spec TwoChartCech.Cover.lineBundle_r1_apply CoherentBaseChange.TwoTermComplex.mk.sizeOf_spec CoherentBaseChange.TwoTermComplex.mk.injEq"
p2m_attr_erase "simp" "AlgebraicGeometry.SubalgebraStages.specCone_π_app AlgebraicGeometry.SubalgebraStages.specLeg_specHom AlgebraicGeometry.SubalgebraStages.specLeg_specTrans AlgebraicGeometry.SubalgebraStages.cone_pt AlgebraicGeometry.SubalgebraStages.trans_fst AlgebraicGeometry.SubalgebraStages.diagram_obj AlgebraicGeometry.SubalgebraStages.leg_snd AlgebraicGeometry.SubalgebraStages.diagram_map AlgebraicGeometry.SubalgebraStages.specTrans_refl AlgebraicGeometry.SubalgebraStages.trans_snd AlgebraicGeometry.SubalgebraStages.specTrans_specHom AlgebraicGeometry.SubalgebraStages.specCone_pt AlgebraicGeometry.SubalgebraStages.cone_π_app AlgebraicGeometry.SubalgebraStages.specDiagram_map AlgebraicGeometry.SubalgebraStages.specDiagram_obj AlgebraicGeometry.SubalgebraStages.leg_fst AlgebraicGeometry.SubalgebraStages.leg_trans IsDirectLimit.Module.linearEquiv_symm_apply IsDirectLimit.linearEquiv_symm_apply IsDirectLimit.lift_of IsDirectLimit.Module.linearEquiv_apply IsDirectLimit.Module.lift_of IsDirectLimit.Equiv_apply RegularLocalRingQuotientAscent.dualNumberFst_apply GoodReductionJacobian.RelativeGroupLaw.baseChangePointToBase_ofBase GoodReductionJacobian.RelativeGroupLaw.baseChangePointToBase_coe GoodReductionJacobian.RelativeGroupLaw.baseChangePointOfBase_coe GoodReductionJacobian.RelativeGroupLaw.baseChange_inv GoodReductionJacobian.RelativeGroupLaw.baseChangePointOfBase_toBase GoodReductionJacobian.RelativeGroupLaw.baseChange_mul GoodReductionJacobian.RelativeGroupLaw.baseChange_one NeronSpecialFibreInfra.specialFibreRestrict_coe_comp_fst NeronSpecialFibreInfra.fibreRestrictAlong_coe_comp_snd NeronSpecialFibreInfra.fibreRestrictAlong_coe_comp_fst NeronSpecialFibreInfra.neronEndRestrictEquiv_apply NeronSpecialFibreInfra.fibreRestrictAlong_coe_comp_fst_assoc NeronSpecialFibreInfra.specialFibreRestrict_coe_comp_snd NeronSpecialFibreInfra.neronEndExtension_genericFibreRestrict NeronSpecialFibreInfra.specClosedFibreInclusion_eq NeronSpecialFibreInfra.specialFibreRestrict_coe_comp_fst_assoc"
p2m_attr_erase "simp" "NeronSpecialFibreInfra.specialFibreRestrict_coe_comp_snd_assoc NeronSpecialFibreInfra.genericFibreRestrict_neronEndExtension NeronSpecialFibreInfra.homOverId_coe NeronSpecialFibreInfra.homOverComp_coe NeronSpecialFibreInfra.fibreRestrictAlong_coe_comp_snd_assoc GoodReductionJacobian.RelativeGroupLaw.fibre_inv GoodReductionJacobian.RelativeGroupLaw.fibrePointToBase_coe GoodReductionJacobian.RelativeGroupLaw.fibrePointOfBase_toBase GoodReductionJacobian.RelativeGroupLaw.fibre_mul GoodReductionJacobian.RelativeGroupLaw.fibrePointToBase_ofBase GoodReductionJacobian.RelativeGroupLaw.fibre_one GoodReductionJacobian.RelativeGroupLaw.fibrePointOfBase_coe AlgebraicGeometry.schemeFibreEndo_snd AlgebraicGeometry.schemeFibreEndo_fst AlgebraicGeometry.Scheme.OrderedAffineCover.mk.injEq AlgebraicGeometry.OModulePresheaf.mk.sizeOf_spec AlgebraicGeometry.Scheme.OrderedAffineCover.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.mk.injEq AlgebraicGeometry.OModulePresheaf.prod_obj AlgebraicGeometry.OModulePresheaf.restrOpen_obj AlgebraicGeometry.OModulePresheaf.DevissageStep.mk.injEq AlgebraicGeometry.OModulePresheaf.pushforward_obj AlgebraicGeometry.OModulePresheaf.im_obj AlgebraicGeometry.OModulePresheaf.pow_obj AlgebraicGeometry.OModulePresheaf.fstHom_app AlgebraicGeometry.OModulePresheaf.ker_obj AlgebraicGeometry.OModulePresheaf.coker_obj AlgebraicGeometry.OModulePresheaf.DevissageStep.mk.sizeOf_spec AlgebraicGeometry.Scheme.OrderedAffineCover.preimage_U AlgebraicGeometry.OModulePresheaf.sndHom_app AlgebraicGeometry.OModulePresheaf.Hom.mk.injEq AlgebraicGeometry.OModulePresheaf.Hom.id_app AlgebraicGeometry.OModulePresheaf.AffHom.appSections_apply AlgebraicGeometry.OModulePresheaf.AffHom.comp_app AlgebraicGeometry.OModulePresheaf.AffSES.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.AffHom.kerMap_coe AlgebraicGeometry.OModulePresheaf.AffHom.id_app AlgebraicGeometry.OModulePresheaf.Hom.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.Hom.toAffHom_app AlgebraicGeometry.OModulePresheaf.SES.mk.sizeOf_spec"
p2m_attr_erase "simp" "AlgebraicGeometry.OModulePresheaf.AffHom.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.Hom.comp_app AlgebraicGeometry.OModulePresheaf.SES.mk.injEq AlgebraicGeometry.OModulePresheaf.AffHom.mk.injEq AlgebraicGeometry.OModulePresheaf.Hom.appSections_apply AlgebraicGeometry.OModulePresheaf.AffSES.mk.injEq AlgebraicGeometry.OModulePresheaf.Leray.restrictToPreimage_U AlgebraicGeometry.Scheme.OrderedAffineCover.toCoverOf_U AlgebraicGeometry.Scheme.OrderedAffineCoverOf.mk.sizeOf_spec AlgebraicGeometry.Scheme.OrderedAffineCoverOf.mk.injEq AlgebraicGeometry.Scheme.OrderedAffineCover.restrict_U DoubleComplex.Bounded.mk.injEq DoubleComplex.Bounded.mk.sizeOf_spec DoubleComplex.Convergence.mk.injEq DoubleComplex.Convergence.mk.sizeOf_spec DoubleComplex.SubQuot.mk.sizeOf_spec DoubleComplex.SubQuot.mk.injEq ProjSpaceCech.GradedModule.mk.injEq ProjSpaceCech.GradedModule.mk.sizeOf_spec ProjSpaceCech.GradedModule.Frac.mk.sizeOf_spec ProjSpaceCech.GradedModule.Presentation.mk.injEq ProjSpaceCech.GradedModule.Frac.mk.injEq ProjSpaceCech.GradedModule.Presentation.mk.sizeOf_spec ProjSpaceCech.GradedModule.Hom.shift_toLinearMap ProjSpaceCech.GradedModule.Hom.mk.sizeOf_spec ProjSpaceCech.GradedModule.Hom.mk.injEq AlgebraicGeometry.Scheme.Modules.tensorSections_zero_right AlgebraicGeometry.Scheme.Modules.map_unitSection AlgebraicGeometry.Scheme.Modules.tensorSectionsBilin_apply AlgebraicGeometry.Scheme.Modules.tensorPowSection_zero AlgebraicGeometry.Scheme.Modules.tensorSections_zero_left AlgebraicGeometry.Scheme.Modules.tensorPow_zero AlgebraicGeometry.Scheme.Modules.tensorPow_succ AlgebraicGeometry.Scheme.Modules.glueComponent_glueMk AlgebraicGeometry.Scheme.Modules.UnitCocycle.mk.injEq AlgebraicGeometry.Scheme.Modules.UnitCocycle.mk.sizeOf_spec AlgebraicGeometry.Scheme.Modules.pullbackLocalSection_neg AlgebraicGeometry.Scheme.Modules.pullbackLocalSection_zero AlgebraicGeometry.Scheme.Modules.pullbackLocalSection_sub AlgebraicGeometry.Scheme.Modules.pullbackLocalSection_add"
p2m_attr_erase "simp" "PresheafOfModules.InternalHom.IsSheafAux.appAt_toPresheafHom SheafOfModules.ihomSectionsEquivFamily_unit AlgebraicGeometry.Scheme.Modules.restrictHomEquivFamily_apply SheafOfModules.ihomEval_unit_app AlgebraicGeometry.Scheme.Modules.ihomEval_zero_right AlgebraicGeometry.Scheme.Modules.ihomEval_zero_left AlgebraicGeometry.Scheme.Modules.homOfFamily_app_apply SheafOfModules.unit_ihomSectionsEquivFamily AlgebraicGeometry.Scheme.Modules.familyOfHom_app AlgebraicGeometry.Scheme.Modules.restrictUnitIso_hom_app_apply AlgebraicGeometry.Scheme.Modules.restrictUnitIso_inv_app_apply AlgebraicGeometry.Scheme.Modules.restrictHomOfFamily_app_apply AlgebraicGeometry.Scheme.Modules.restrictHomEquivFamily_symm_apply AlgebraicGeometry.tilde.functorCompPullbackSpecIso_app AlgebraicGeometry.Scheme.Hom.kaehlerPresheaf_obj PresheafOfModules.exteriorPower_map_ιMulti PresheafOfModules.ExteriorPower.appₗ_apply AlgebraicGeometry.Scheme.Modules.exteriorPower_obj AlgebraicGeometry.Scheme.OrderedOpenFamily.mk.injEq AlgebraicGeometry.Scheme.OrderedOpenFamily.mk.sizeOf_spec CochainCx.Bounded.mk.sizeOf_spec CochainCx.Bounded.mk.injEq AlgebraicCurve.CurveModel.mk.injEq AlgebraicCurve.CurveModel.mk.sizeOf_spec AlgebraicCurve.Place.mk.injEq AlgebraicCurve.Divisor.degree_single AlgebraicCurve.Divisor.smul_single AlgebraicCurve.Place.smul_toValuationSubring AlgebraicCurve.Place.heightOneSpectrum_asIdeal AlgebraicCurve.Place.coe_algebraMap AlgebraicCurve.Place.ord_one AlgebraicCurve.Place.coe_smulRingEquiv_apply AlgebraicCurve.Pic0.coe_degZeroSMulHom AlgebraicCurve.Place.deg_smul AlgebraicCurve.Pic0.mk_zero AlgebraicCurve.Place.mk.sizeOf_spec AlgebraicCurve.Divisor.degree_smul AlgebraicCurve.Pic0.mk_add AlgebraicCurve.Place.ord_zero AlgebraicCurve.Place.ofHeightOneSpectrum_toValuationSubring"
p2m_attr_erase "simp" "AlgebraicCurve.CurveModel.coe_gInf AlgebraicCurve.CurveModel.coe_tInvChart AlgebraicCurve.CurveModel.ιInf_gluedToBase_assoc AlgebraicCurve.CurveModel.ιInf_gluedToBase AlgebraicCurve.CurveModel.primeOfι₀_asIdeal AlgebraicCurve.CurveModel.coe_tChart AlgebraicCurve.CurveModel.ι₀_gluedToBase_assoc AlgebraicCurve.CurveModel.primeOfιInf_asIdeal AlgebraicCurve.CurveModel.ι₀_gluedToBase AlgebraicCurve.CurveModel.coe_tma AlgebraicCurve.CurveModel.coe_primeEquivChartPlaces AlgebraicCurve.Place.congrEquiv_symm_apply AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply AlgebraicCurve.RationalFunctionField.deg_placeOfPoint"

set_option autoImplicit false

p2m_open "CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory AlgebraicGeometry NeronModelInfra~schemeHomOverComp GoodReductionJacobian AlgebraicGeometry.Polarisation"

open scoped CategoryTheory.MonObj

noncomputable section

namespace P2mWs30CF1k

section Mon

variable {X : Scheme.{0}}

def cancelL {M M' : X.Modules} (ε : M ⊗ M' ≅ 𝟙_ X.Modules) (N : X.Modules) : M ⊗ (M' ⊗ N) ≅ N :=
  (α_ M M' N).symm ≪≫ (ε ⊗ᵢ Iso.refl N) ≪≫ λ_ N

def middleSwap (M N P Q : X.Modules) : (M ⊗ N) ⊗ (P ⊗ Q) ≅ (M ⊗ P) ⊗ (N ⊗ Q) :=
  α_ M N (P ⊗ Q) ≪≫ whiskerLeftIso M ((α_ N P Q).symm ≪≫ (β_ N P ⊗ᵢ Iso.refl Q) ≪≫ α_ P N Q) ≪≫
    (α_ M P (N ⊗ Q)).symm

def rearrange (Mm U Mp V E : X.Modules) :
    ((Mm ⊗ U) ⊗ (Mp ⊗ V)) ⊗ E ≅ (Mp ⊗ (E ⊗ Mm)) ⊗ (U ⊗ V) :=
  (middleSwap Mm U Mp V ⊗ᵢ Iso.refl E) ≪≫ β_ _ E ≪≫ (α_ E (Mm ⊗ Mp) (U ⊗ V)).symm ≪≫
    (((α_ E Mm Mp).symm ≪≫ β_ (E ⊗ Mm) Mp) ⊗ᵢ Iso.refl (U ⊗ V))

end Mon

section GroupLawBits

variable {S : Type} [CommRing S] {A : Scheme.{0}} (f : A ⟶ Spec (CommRingCat.of S)) (L : RelativeGroupLaw S f)

theorem comp_addMor {T : Scheme.{0}} {t' : T ⟶ Spec (CommRingCat.of S)} (ψ : T ⟶ pullback f f)
    (hψ : ψ ≫ (pullback.fst f f ≫ f) = t') (P Q : SchemeHomOver t' f)
    (hP : ψ ≫ pullback.fst f f = P.1) (hQ : ψ ≫ pullback.snd f f = Q.1) :
    ψ ≫ addMor f L = (L.mul t' P Q).1 := by
  have nat := L.mul_natural (pullback.fst f f ≫ f) t' ψ hψ
    ⟨pullback.fst f f, rfl⟩ ⟨pullback.snd f f, pullback.condition.symm⟩
  have h1 : schemeHomOverComp ψ hψ ⟨pullback.fst f f, rfl⟩ = P := Subtype.ext hP
  have h2 : schemeHomOverComp ψ hψ ⟨pullback.snd f f, pullback.condition.symm⟩ = Q := Subtype.ext hQ
  rw [h1, h2] at nat
  have h3 := congrArg Subtype.val nat
  simpa [schemeHomOverComp, addMor] using h3

theorem inv_comp {T T' : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of S)) (t' : T' ⟶ Spec (CommRingCat.of S))
    (ψ : T' ⟶ T) (hψ : ψ ≫ t = t') (x : SchemeHomOver t f) :
    schemeHomOverComp ψ hψ (L.inv t x) = L.inv t' (schemeHomOverComp ψ hψ x) := by
  letI := L.pointGroup t
  letI := L.pointGroup t'
  exact map_inv (MonoidHom.mk' (schemeHomOverComp ψ hψ) (L.mul_natural t t' ψ hψ)) x

variable (𝓛 : A.Modules)

def pullbackMumfordIso {T : Scheme.{0}} (ψ : T ⟶ pullback f f) (g₁ g₂ g₃ : T ⟶ A)
    (h₁ : ψ ≫ addMor f L = g₁) (h₂ : ψ ≫ pullback.fst f f = g₂) (h₃ : ψ ≫ pullback.snd f f = g₃) :
    (Scheme.Modules.pullback ψ).obj (mumfordBundle f L 𝓛) ≅
      (Scheme.Modules.pullback g₁).obj 𝓛 ⊗
        ((Scheme.Modules.pullback g₂).obj (Scheme.Modules.dual 𝓛) ⊗
          (Scheme.Modules.pullback g₃).obj (Scheme.Modules.dual 𝓛)) := by
  unfold mumfordBundle
  exact Scheme.Modules.pullbackTensorObjIso _ _ _ ≪≫
    (((Scheme.Modules.pullbackComp ψ _).app 𝓛 ≪≫ (Scheme.Modules.pullbackCongr h₁).app 𝓛) ⊗ᵢ
      (Scheme.Modules.pullbackTensorObjIso _ _ _ ≪≫
        (((Scheme.Modules.pullbackComp ψ _).app _ ≪≫ (Scheme.Modules.pullbackCongr h₂).app _) ⊗ᵢ
          ((Scheme.Modules.pullbackComp ψ _).app _ ≪≫ (Scheme.Modules.pullbackCongr h₃).app _))))

def pairIso {T : Scheme.{0}} (g : T ⟶ A) (e𝓛 : 𝓛 ⊗ Scheme.Modules.dual 𝓛 ≅ 𝟙_ A.Modules) :
    (Scheme.Modules.pullback g).obj 𝓛 ⊗ (Scheme.Modules.pullback g).obj (Scheme.Modules.dual 𝓛) ≅ 𝟙_ T.Modules :=
  (Scheme.Modules.pullbackTensorObjIso g _ _).symm ≪≫ (Scheme.Modules.pullback g).mapIso e𝓛 ≪≫
    Scheme.Modules.pullbackTensorUnitObjIso g

end GroupLawBits

theorem main
    (S : Type) [CommRing S] {A : Scheme.{0}} (f : A ⟶ Spec (CommRingCat.of S))
    (L : RelativeGroupLaw S f) (hc : L.IsCommutative) (hA : AbelianSchemePropertyBundle S f) (𝓛 : A.Modules)
    (h𝓛 : Scheme.Modules.IsInvertible 𝓛)
    (R : Type) [CommRing R] (t : Spec (CommRingCat.of R) ⟶ Spec (CommRingCat.of S)) (x : SchemeHomOver t f)
    (n : pullback f t ⟶ pullback f t) (hn₁ : n ≫ pullback.fst f t = pullback.fst f t ≫ negMor f L)
    (hn₂ : n ≫ pullback.snd f t = pullback.snd f t) :
    LocIsoOnBase (pullback.snd f t)
      ((Scheme.Modules.pullback n).obj ((Scheme.Modules.pullback (sliceAt f x)).obj (mumfordBundle f L 𝓛)))
      (Scheme.Modules.dual ((Scheme.Modules.pullback (sliceAt f x)).obj (mumfordBundle f L 𝓛))) := by

  have Q := LocIsoOnBase.equivalence (S := R) (pullback.snd f t)
  have ofIso : ∀ {M M' : (pullback f t).Modules}, (M ≅ M') → LocIsoOnBase (pullback.snd f t) M M' :=
    fun e _ => ⟨⊤, trivial, ⟨(Scheme.Modules.pullback _).mapIso e⟩⟩
  have hdual := Scheme.Modules.IsInvertible.dual_monoidalV2 h𝓛
  obtain ⟨e𝓛⟩ := hdual.2

  let tT : pullback f t ⟶ Spec (CommRingCat.of S) := pullback.snd f t ≫ t
  let a : SchemeHomOver tT f := L.fstPoint t
  let b : SchemeHomOver tT f := L.sndPoint t x
  let c : SchemeHomOver tT f := L.inv tT a
  have hp₁f : pullback.fst f t ≫ f = tT := pullback.condition
  have hcval : c.1 = pullback.fst f t ≫ negMor f L := by
    have h := inv_comp f L f tT (pullback.fst f t) hp₁f (idPt f)
    have hid : schemeHomOverComp (pullback.fst f t) hp₁f (idPt f) = a :=
      Subtype.ext (by simp [schemeHomOverComp, idPt, a])
    rw [hid] at h
    have h' := congrArg Subtype.val h
    simpa [schemeHomOverComp, negMor] using h'.symm
  have heval : (L.one tT).1 = pullback.snd f t ≫ (L.one t).1 := by
    have h := congrArg Subtype.val (L.sndPoint_one t)
    simpa using h.symm

  have hg_abc : L.mul tT (L.mul tT a b) c = b := by
    letI := L.pointGroup tT
    show a * b * a⁻¹ = b
    rw [show a * b = b * a from hc tT a b]
    exact mul_inv_cancel_right b a
  have hg_ac : L.mul tT a c = L.one tT := L.mul_inv_cancel tT a
  have hg_bc : L.mul tT b c = L.mul tT c b := hc tT b c

  have hp1 : sliceAt f x ≫ pullback.fst f f = pullback.fst f t := by unfold sliceAt; exact pullback.lift_fst _ _ _
  have hp2 : sliceAt f x ≫ pullback.snd f f = pullback.snd f t ≫ x.1 := by unfold sliceAt; exact pullback.lift_snd _ _ _
  have hψ : sliceAt f x ≫ (pullback.fst f f ≫ f) = tT := by rw [← Category.assoc, hp1]; exact hp₁f
  have key : sliceAt f x ≫ addMor f L = (L.mul tT a b).1 := comp_addMor f L _ hψ a b hp1 hp2
  have hn1 : (n ≫ sliceAt f x) ≫ pullback.fst f f = pullback.fst f t ≫ negMor f L := by
    rw [Category.assoc, hp1, hn₁]
  have hn2 : (n ≫ sliceAt f x) ≫ pullback.snd f f = pullback.snd f t ≫ x.1 := by
    rw [Category.assoc, hp2, ← Category.assoc, hn₂]
  have hψn : (n ≫ sliceAt f x) ≫ (pullback.fst f f ≫ f) = tT := by
    rw [← Category.assoc, hn1, Category.assoc, negMor_over]; exact hp₁f
  have keyn : (n ≫ sliceAt f x) ≫ addMor f L = (L.mul tT c b).1 :=
    comp_addMor f L _ hψn c b (hn1.trans hcval.symm) hn2

  let La : (pullback f t).Modules := (Scheme.Modules.pullback (pullback.fst f t)).obj 𝓛
  let Lb : (pullback f t).Modules := (Scheme.Modules.pullback (pullback.snd f t ≫ x.1)).obj 𝓛
  let Lc : (pullback f t).Modules := (Scheme.Modules.pullback (pullback.fst f t ≫ negMor f L)).obj 𝓛
  let Da : (pullback f t).Modules := (Scheme.Modules.pullback (pullback.fst f t)).obj (Scheme.Modules.dual 𝓛)
  let Db : (pullback f t).Modules := (Scheme.Modules.pullback (pullback.snd f t ≫ x.1)).obj (Scheme.Modules.dual 𝓛)
  let Dc : (pullback f t).Modules :=
    (Scheme.Modules.pullback (pullback.fst f t ≫ negMor f L)).obj (Scheme.Modules.dual 𝓛)
  let Sp : (pullback f t).Modules := (Scheme.Modules.pullback (L.mul tT a b).1).obj 𝓛
  let Sm : (pullback f t).Modules := (Scheme.Modules.pullback (L.mul tT c b).1).obj 𝓛
  let E : (pullback f t).Modules := (Scheme.Modules.pullback (L.one tT).1).obj 𝓛
  let W : (pullback f t).Modules := (Scheme.Modules.pullback (sliceAt f x)).obj (mumfordBundle f L 𝓛)
  let nW : (pullback f t).Modules := (Scheme.Modules.pullback n).obj W

  have E0 : W ≅ Sp ⊗ (Da ⊗ Db) := pullbackMumfordIso f L 𝓛 (sliceAt f x) _ _ _ key hp1 hp2
  have E0' : nW ≅ Sm ⊗ (Dc ⊗ Db) :=
    (Scheme.Modules.pullbackComp n (sliceAt f x)).app _ ≪≫
      pullbackMumfordIso f L 𝓛 (n ≫ sliceAt f x) _ _ _ keyn hn1 hn2

  have εa : La ⊗ Da ≅ 𝟙_ _ := pairIso 𝓛 _ e𝓛
  have εb : Lb ⊗ Db ≅ 𝟙_ _ := pairIso 𝓛 _ e𝓛
  have εc : Lc ⊗ Dc ≅ 𝟙_ _ := pairIso 𝓛 _ e𝓛

  letI : GrpObj (Over.mk f) := L.grpObjOverMk
  haveI : IsCommMonObj (Over.mk f) := L.isCommMonObj_grpObjOverMk_iff_mul_comm.mpr (fun t x y => hc t x y)
  let a' : Over.mk tT ⟶ Over.mk f := schemeHomOverToOverHom a
  let b' : Over.mk tT ⟶ Over.mk f := schemeHomOverToOverHom b
  let c' : Over.mk tT ⟶ Over.mk f := schemeHomOverToOverHom c
  obtain ⟨CU0⟩ := AlgebraicGeometry.Polarisation.nonempty_pullback_mul_mul_tensor_iso_tensor_pullback_one_of_commRing
    f L hc hA 𝓛 h𝓛 (Y := Over.mk tT) a' b' c'

  let F : (pullback f t).Modules :=
    (Scheme.Modules.pullback (Over.mk tT).hom).obj ((Scheme.Modules.pullback (L.one (𝟙 (Spec (CommRingCat.of S)))).1).obj 𝓛)
  have hmul : ∀ φ ψ : Over.mk tT ⟶ Over.mk f,
      (φ * ψ).left = (L.mul tT (overHomToSchemeHomOver φ) (overHomToSchemeHomOver ψ)).1 := fun φ ψ =>
    congrArg Subtype.val (L.overHomToSchemeHomOver_mul tT φ ψ)
  have hrt : ∀ p : SchemeHomOver tT f, overHomToSchemeHomOver (schemeHomOverToOverHom p) = p :=
    fun p => overHomToSchemeHomOver_schemeHomOverToOverHom p
  have h_ab : (a' * b').left = (L.mul tT a b).1 := by rw [hmul, hrt, hrt]
  have h_ac : (a' * c').left = (L.one tT).1 := by rw [hmul, hrt, hrt, hg_ac]
  have h_bc : (b' * c').left = (L.mul tT c b).1 := by rw [hmul, hrt, hrt, hg_bc]
  have h_abc : (a' * b' * c').left = b.1 := by
    rw [hmul, hrt, L.overHomToSchemeHomOver_mul tT, hrt, hrt, hg_abc]
  have ha' : a'.left = pullback.fst f t := rfl
  have hb' : b'.left = pullback.snd f t ≫ x.1 := rfl
  have hc' : c'.left = pullback.fst f t ≫ negMor f L := hcval
  have cg : ∀ {g g' : pullback f t ⟶ A}, g = g' →
      ((Scheme.Modules.pullback g).obj 𝓛 ≅ (Scheme.Modules.pullback g').obj 𝓛) :=
    fun h => (Scheme.Modules.pullbackCongr h).app 𝓛
  have CU : Lb ⊗ (La ⊗ (Lb ⊗ Lc)) ≅ Sp ⊗ ((E ⊗ F) ⊗ Sm) :=
    (cg h_abc ⊗ᵢ (cg ha' ⊗ᵢ (cg hb' ⊗ᵢ cg hc'))).symm ≪≫ CU0 ≪≫ (cg h_ab ⊗ᵢ (cg h_ac ⊗ᵢ (cg h_bc ⊗ᵢ Iso.refl F))) ≪≫
      whiskerLeftIso Sp (whiskerLeftIso E (β_ Sm F) ≪≫ (α_ E F Sm).symm)

  have PD : (Lb ⊗ (La ⊗ (Lb ⊗ Lc))) ⊗ (Dc ⊗ (Db ⊗ (Da ⊗ Db))) ≅ 𝟙_ _ :=
    α_ _ _ _ ≪≫
      whiskerLeftIso Lb
        (α_ _ _ _ ≪≫ whiskerLeftIso La (α_ _ _ _ ≪≫ whiskerLeftIso Lb (cancelL εc _) ≪≫ cancelL εb _) ≪≫
          cancelL εa _) ≪≫ εb
  have G : (nW ⊗ W) ⊗ (E ⊗ F) ≅ 𝟙_ _ :=
    ((E0' ⊗ᵢ E0) ⊗ᵢ Iso.refl (E ⊗ F)) ≪≫ rearrange Sm (Dc ⊗ Db) Sp (Da ⊗ Db) (E ⊗ F) ≪≫
      (CU.symm ⊗ᵢ α_ Dc Db (Da ⊗ Db)) ≪≫ PD

  have heinv : Scheme.Modules.IsInvertible ((Scheme.Modules.pullback (L.one t).1).obj 𝓛) :=
    Scheme.Modules.IsInvertible.pullback _ h𝓛
  have hE : LocIsoOnBase (pullback.snd f t) E (𝟙_ _) := by
    intro s
    obtain ⟨U, hsU, ⟨eU⟩⟩ := heinv.1 s
    refine ⟨U, hsU, ⟨?_⟩⟩
    have hfact : (pullback.snd f t ⁻¹ᵁ U).ι ≫ (L.one tT).1 = ((pullback.snd f t ∣_ U) ≫ U.ι) ≫ (L.one t).1 := by
      rw [heval, ← Category.assoc, ← morphismRestrict_ι]
    exact (Scheme.Modules.pullbackComp _ _).app _ ≪≫ (Scheme.Modules.pullbackCongr hfact).app _ ≪≫
      ((Scheme.Modules.pullbackComp _ _).app _).symm ≪≫ ((Scheme.Modules.pullbackComp _ _).app _).symm ≪≫
      (Scheme.Modules.pullback (pullback.snd f t ∣_ U)).mapIso eU ≪≫
      Scheme.Modules.pullbackUnitIso _ ≪≫ (Scheme.Modules.pullbackTensorUnitObjIso _).symm

  have heinv' : Scheme.Modules.IsInvertible ((Scheme.Modules.pullback t).obj
      ((Scheme.Modules.pullback (L.one (𝟙 (Spec (CommRingCat.of S)))).1).obj 𝓛)) := (h𝓛.pullback _).pullback _
  have hF : LocIsoOnBase (pullback.snd f t) F (𝟙_ _) := by
    intro s
    obtain ⟨U, hsU, ⟨eU⟩⟩ := heinv'.1 s
    refine ⟨U, hsU, ⟨?_⟩⟩
    have hfact : (pullback.snd f t ⁻¹ᵁ U).ι ≫ (Over.mk tT).hom = ((pullback.snd f t ∣_ U) ≫ U.ι) ≫ t := by
      rw [morphismRestrict_ι, Category.assoc]; rfl
    exact (Scheme.Modules.pullbackComp _ _).app _ ≪≫ (Scheme.Modules.pullbackCongr hfact).app _ ≪≫
      ((Scheme.Modules.pullbackComp ((pullback.snd f t ∣_ U) ≫ U.ι) t).app _).symm ≪≫
      ((Scheme.Modules.pullbackComp (pullback.snd f t ∣_ U) U.ι).app _).symm ≪≫
      (Scheme.Modules.pullback (pullback.snd f t ∣_ U)).mapIso eU ≪≫
      Scheme.Modules.pullbackUnitIso _ ≪≫ (Scheme.Modules.pullbackTensorUnitObjIso _).symm
  have hEF : LocIsoOnBase (pullback.snd f t) (E ⊗ F) (𝟙_ _) :=
    Q.trans (LocIsoOnBase.tensor hE hF) (ofIso (λ_ _))

  have h1 : LocIsoOnBase (pullback.snd f t) (nW ⊗ W) (𝟙_ _) :=
    Q.trans (ofIso (ρ_ (nW ⊗ W)).symm) (Q.trans (LocIsoOnBase.tensor (Q.refl (nW ⊗ W)) (Q.symm hEF)) (ofIso G))

  have hWinv : Scheme.Modules.IsInvertible W := by
    change Scheme.Modules.IsInvertible ((Scheme.Modules.pullback (sliceAt f x)).obj (mumfordBundle f L 𝓛))
    unfold mumfordBundle
    exact Scheme.Modules.IsInvertible.pullback _
      (Scheme.Modules.IsInvertible.tensor_monoidalV2 (Scheme.Modules.IsInvertible.pullback _ h𝓛)
        (Scheme.Modules.IsInvertible.tensor_monoidalV2 (Scheme.Modules.IsInvertible.pullback _ hdual.1)
          (Scheme.Modules.IsInvertible.pullback _ hdual.1)))
  obtain ⟨eW⟩ := (Scheme.Modules.IsInvertible.dual_monoidalV2 hWinv).2
  have h2 : LocIsoOnBase (pullback.snd f t) nW (Scheme.Modules.dual W) :=
    Q.trans (ofIso ((ρ_ nW).symm ≪≫ (Iso.refl nW ⊗ᵢ eW.symm) ≪≫ (α_ _ _ _).symm))
      (Q.trans (LocIsoOnBase.tensor h1 (Q.refl _)) (ofIso (λ_ _)))
  exact h2

end P2mWs30CF1k

end

open P2mWs30CF1k in

theorem solution
    (S : Type) [CommRing S] {A : Scheme.{0}} (f : A ⟶ Spec (CommRingCat.of S))
    (L : RelativeGroupLaw S f) (hc : L.IsCommutative) (hA : AbelianSchemePropertyBundle S f) (𝓛 : A.Modules) (h𝓛 : Scheme.Modules.IsInvertible 𝓛)
    (R : Type) [CommRing R] (t : Spec (CommRingCat.of R) ⟶ Spec (CommRingCat.of S)) (x : SchemeHomOver t f) :
    LocIsoOnBase (pullback.snd f t)
      ((Scheme.Modules.pullback
        (pullback.lift (pullback.fst f t ≫ negMor f L) (pullback.snd f t)
          (by rw [Category.assoc, negMor_over]; exact pullback.condition))).obj ((Scheme.Modules.pullback (sliceAt f x)).obj (mumfordBundle f L 𝓛)))
      (Scheme.Modules.dual ((Scheme.Modules.pullback (sliceAt f x)).obj (mumfordBundle f L 𝓛))) :=
  main S f L hc hA 𝓛 h𝓛 R t x _ (pullback.lift_fst _ _ _) (pullback.lift_snd _ _ _)

end S_AlgebraicGeometry_Polarisation_locIsoOnBase_pullback_negMor_prod_sliceAt_mumfordBundle_dual_of_commRing
end P2MW
export P2MW.S_AlgebraicGeometry_Polarisation_locIsoOnBase_pullback_negMor_prod_sliceAt_mumfordBundle_dual_of_commRing (solution)
