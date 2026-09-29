-- Prove2me | solution 1 for AlgebraicGeometry.Polarisation.locIsoOnBase_sliceAt_mumfordBundle_mul_tensor_of_commRing
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:02.935278+00:00
-- url     : https://prove2.me/submissions/f4fc831b-32af-5686-b1e2-b15fa5cd104f

import Definitions.Def_AlgebraicGeometry_PolarisationPicZero
import Definitions.Def_AlgebraicGeometry_PolarisationRosati
import Definitions.Def_AlgebraicGeometry_ModulesPullbackMonoidalV2
import Definitions.Def_AlgebraicGeometry_RelativeGroupLawGrpObj
import Theorems.Thm_AlgebraicGeometry_Polarisation_nonempty_pullback_mul_mul_tensor_iso_tensor_pullback_one_of_commRing
import Theorems.Thm_AlgebraicGeometry_Polarisation_LocIsoOnBase_tensor
import Theorems.Thm_AlgebraicGeometry_Polarisation_LocIsoOnBase_equivalence
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_IsInvertible_dual_monoidalV2
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_IsInvertible_pullback_dual_monoidalV2
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_Polarisation_locIsoOnBase_sliceAt_mumfordBundle_mul_tensor_of_commRing
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

p2m_open "CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory AlgebraicGeometry NeronModelInfra~schemeHomOverComp~schemeHomOverComp_coe GoodReductionJacobian AlgebraicGeometry.Polarisation"

open scoped CategoryTheory.MonObj

noncomputable section

namespace SliceAdd

variable {S : Type} [CommRing S] {A : Scheme.{0}} {f : A ⟶ Spec (CommRingCat.of S)} (L : RelativeGroupLaw S f)
  {R : Type} [CommRing R] (t : Spec (CommRingCat.of R) ⟶ Spec (CommRingCat.of S))

abbrev Y : Over (Spec (CommRingCat.of S)) := Over.mk (pullback.snd f t ≫ t)

abbrev Fpt : Y (f := f) t ⟶ Over.mk f := schemeHomOverToOverHom (L.fstPoint t)
abbrev Spt (x : SchemeHomOver t f) : Y (f := f) t ⟶ Over.mk f := schemeHomOverToOverHom (L.sndPoint t x)

theorem sndPoint_mul (x y : SchemeHomOver t f) :
    L.sndPoint t (L.mul t x y) = L.mul (pullback.snd f t ≫ t) (L.sndPoint t x) (L.sndPoint t y) := by
  have e1 : ∀ z : SchemeHomOver t f, schemeHomOverComp (pullback.snd f t) rfl z = L.sndPoint t z :=
    fun z => Subtype.ext rfl
  have h := L.mul_natural t (pullback.snd f t ≫ t) (pullback.snd f t) rfl x y
  rw [e1, e1, e1] at h
  exact h

theorem left_Fpt_mul_Spt (x : SchemeHomOver t f) :
    letI := L.grpObjOverMk
    (Fpt L t * Spt L t x).left = L.mulRight t x := by
  letI := L.grpObjOverMk
  have h := L.overHomToSchemeHomOver_mul (pullback.snd f t ≫ t) (Fpt L t) (Spt L t x)
  rw [Fpt, Spt, overHomToSchemeHomOver_schemeHomOverToOverHom, overHomToSchemeHomOver_schemeHomOverToOverHom] at h
  exact congrArg Subtype.val h

theorem Spt_mul_Spt (x y : SchemeHomOver t f) :
    letI := L.grpObjOverMk
    Spt L t x * Spt L t y = Spt L t (L.mul t x y) := by
  letI := L.grpObjOverMk
  apply overHomToSchemeHomOver_injective
  rw [L.overHomToSchemeHomOver_mul, Spt, Spt, Spt, overHomToSchemeHomOver_schemeHomOverToOverHom,
    overHomToSchemeHomOver_schemeHomOverToOverHom, overHomToSchemeHomOver_schemeHomOverToOverHom, sndPoint_mul]

theorem left_Spt (x : SchemeHomOver t f) : (Spt L t x).left = pullback.snd f t ≫ x.1 := rfl
theorem left_Fpt : (Fpt L t).left = pullback.fst f t := rfl

abbrev Efac (𝓛 : A.Modules) : (pullback f t).Modules :=
  (Scheme.Modules.pullback (Y (f := f) t).hom).obj ((Scheme.Modules.pullback (L.one (𝟙 (Spec (CommRingCat.of S)))).1).obj 𝓛)

theorem cube (hc : L.IsCommutative) (hA : AbelianSchemePropertyBundle S f)
    (𝓛 : A.Modules) (h𝓛 : Scheme.Modules.IsInvertible 𝓛) (x y : SchemeHomOver t f) :
    letI := L.grpObjOverMk
    Nonempty (
      (Scheme.Modules.pullback (Fpt L t * Spt L t x * Spt L t y).left).obj 𝓛 ⊗
        (Scheme.Modules.pullback (Fpt L t).left).obj 𝓛 ⊗
          (Scheme.Modules.pullback (Spt L t x).left).obj 𝓛 ⊗ (Scheme.Modules.pullback (Spt L t y).left).obj 𝓛 ≅
      (Scheme.Modules.pullback (Fpt L t * Spt L t x).left).obj 𝓛 ⊗
        (Scheme.Modules.pullback (Fpt L t * Spt L t y).left).obj 𝓛 ⊗
          (Scheme.Modules.pullback (Spt L t x * Spt L t y).left).obj 𝓛 ⊗ Efac L t 𝓛) := by
  letI := L.grpObjOverMk
  exact AlgebraicGeometry.Polarisation.nonempty_pullback_mul_mul_tensor_iso_tensor_pullback_one_of_commRing f L hc hA 𝓛 h𝓛
    (Fpt L t) (Spt L t x) (Spt L t y)

theorem locIsoOnBase_Efac (𝓛 : A.Modules) (h𝓛 : Scheme.Modules.IsInvertible 𝓛) :
    LocIsoOnBase (pullback.snd f t) (Efac L t 𝓛) (𝟙_ _) := by
  intro s
  have hN : Scheme.Modules.IsInvertible ((Scheme.Modules.pullback t).obj
      ((Scheme.Modules.pullback (L.one (𝟙 (Spec (CommRingCat.of S)))).1).obj 𝓛)) := (h𝓛.pullback _).pullback _
  obtain ⟨U, hs, ⟨τ⟩⟩ := hN.1 s
  refine ⟨U, hs, ⟨?_⟩⟩
  refine (Scheme.Modules.pullbackComp _ _).app _ ≪≫ (Scheme.Modules.pullbackCongr (?_ : (pullback.snd f t ⁻¹ᵁ U).ι ≫ (Y (f := f) t).hom =
      ((pullback.snd f t) ∣_ U ≫ U.ι) ≫ t)).app _ ≪≫
    ((Scheme.Modules.pullbackComp ((pullback.snd f t) ∣_ U ≫ U.ι) t).app _).symm ≪≫
    ((Scheme.Modules.pullbackComp ((pullback.snd f t) ∣_ U) U.ι).app _).symm ≪≫
    (Scheme.Modules.pullback _).mapIso τ ≪≫ Scheme.Modules.pullbackUnitIso _ ≪≫ (Scheme.Modules.pullbackTensorUnitObjIso _).symm
  rw [morphismRestrict_ι, Category.assoc]
  rfl

section Tetris

universe v' u'

variable {C : Type u'} [Category.{v'} C] [MonoidalCategory C] [SymmetricCategory C]

def swapMid (a b c d : C) : (a ⊗ b) ⊗ (c ⊗ d) ≅ (a ⊗ c) ⊗ (b ⊗ d) :=
  α_ a b (c ⊗ d) ≪≫ whiskerLeftIso a ((α_ b c d).symm ≪≫ whiskerRightIso (β_ b c) d ≪≫ α_ c b d) ≪≫
    (α_ a c (b ⊗ d)).symm

def tetris {Pfg Pfh Pgh P3 U V W DU DV DW Dgh : C}
    (cube : P3 ⊗ (U ⊗ (V ⊗ W)) ≅ Pfg ⊗ (Pfh ⊗ Pgh))
    (eU : U ⊗ DU ≅ 𝟙_ C) (eV : V ⊗ DV ≅ 𝟙_ C) (eW : W ⊗ DW ≅ 𝟙_ C) (eGH : Pgh ⊗ Dgh ≅ 𝟙_ C) :
    (Pfg ⊗ (DU ⊗ DV)) ⊗ (Pfh ⊗ (DU ⊗ DW)) ≅ P3 ⊗ (DU ⊗ Dgh) :=
  let M : C := U ⊗ (V ⊗ W)
  let N : C := DU ⊗ (DV ⊗ DW)

  let stepB : Pfg ⊗ Pfh ≅ (P3 ⊗ Dgh) ⊗ M :=
    (ρ_ (Pfg ⊗ Pfh)).symm ≪≫ whiskerLeftIso (Pfg ⊗ Pfh) eGH.symm ≪≫ (α_ (Pfg ⊗ Pfh) Pgh Dgh).symm ≪≫
      whiskerRightIso (α_ Pfg Pfh Pgh ≪≫ cube.symm) Dgh ≪≫
      α_ P3 M Dgh ≪≫ whiskerLeftIso P3 (β_ M Dgh) ≪≫ (α_ P3 Dgh M).symm

  let stepD : (DU ⊗ DV) ⊗ (DU ⊗ DW) ≅ DU ⊗ N := swapMid DU DV DU DW ≪≫ α_ DU DU (DV ⊗ DW)

  let MN : M ⊗ N ≅ 𝟙_ C :=
    swapMid U (V ⊗ W) DU (DV ⊗ DW) ≪≫ (eU ⊗ᵢ (swapMid V W DV DW ≪≫ (eV ⊗ᵢ eW) ≪≫ λ_ (𝟙_ C))) ≪≫ λ_ (𝟙_ C)
  swapMid Pfg (DU ⊗ DV) Pfh (DU ⊗ DW) ≪≫ (stepB ⊗ᵢ stepD) ≪≫ swapMid (P3 ⊗ Dgh) M DU N ≪≫
    whiskerLeftIso ((P3 ⊗ Dgh) ⊗ DU) MN ≪≫ ρ_ ((P3 ⊗ Dgh) ⊗ DU) ≪≫ α_ P3 Dgh DU ≪≫ whiskerLeftIso P3 (β_ Dgh DU)

end Tetris

theorem sliceAt_addMor (z : SchemeHomOver t f) :
    letI := L.grpObjOverMk
    sliceAt f z ≫ addMor f L = (Fpt L t * Spt L t z).left := by
  letI := L.grpObjOverMk
  rw [left_Fpt_mul_Spt]
  have hψ : sliceAt f z ≫ (pullback.fst f f ≫ f) = pullback.snd f t ≫ t := by
    rw [← Category.assoc, sliceAt, pullback.lift_fst]; exact pullback.condition
  have nat := L.mul_natural (pullback.fst f f ≫ f) (pullback.snd f t ≫ t) (sliceAt f z) hψ
    ⟨pullback.fst f f, rfl⟩ ⟨pullback.snd f f, pullback.condition.symm⟩
  have hP : schemeHomOverComp (sliceAt f z) hψ ⟨pullback.fst f f, rfl⟩ = L.fstPoint t :=
    Subtype.ext (by rw [schemeHomOverComp_coe, RelativeGroupLaw.fstPoint_coe]; unfold sliceAt; exact pullback.lift_fst _ _ _)
  have hQ : schemeHomOverComp (sliceAt f z) hψ ⟨pullback.snd f f, pullback.condition.symm⟩ = L.sndPoint t z :=
    Subtype.ext (by rw [schemeHomOverComp_coe, RelativeGroupLaw.sndPoint_coe]; unfold sliceAt; exact pullback.lift_snd _ _ _)
  rw [hP, hQ] at nat
  have h1 := congrArg Subtype.val nat
  simpa [schemeHomOverComp, addMor, RelativeGroupLaw.mulRight] using h1

theorem sliceAt_fst (z : SchemeHomOver t f) : sliceAt f z ≫ pullback.fst f f = (Fpt L t).left := by
  unfold sliceAt; exact pullback.lift_fst _ _ _

theorem sliceAt_snd (z : SchemeHomOver t f) : sliceAt f z ≫ pullback.snd f f = (Spt L t z).left := by
  unfold sliceAt; exact pullback.lift_snd _ _ _

def cmp (z : SchemeHomOver t f) (g : pullback f f ⟶ A) (g' : pullback f t ⟶ A) (hg : sliceAt f z ≫ g = g')
    (M : A.Modules) :
    (Scheme.Modules.pullback (sliceAt f z)).obj ((Scheme.Modules.pullback g).obj M) ≅ (Scheme.Modules.pullback g').obj M :=
  (Scheme.Modules.pullbackComp (sliceAt f z) g).app M ≪≫ (Scheme.Modules.pullbackCongr hg).app M

def sliceIso (𝓛 : A.Modules) (z : SchemeHomOver t f) :
    letI := L.grpObjOverMk
    (Scheme.Modules.pullback (sliceAt f z)).obj (mumfordBundle f L 𝓛) ≅
      (Scheme.Modules.pullback (Fpt L t * Spt L t z).left).obj 𝓛 ⊗
        ((Scheme.Modules.pullback (Fpt L t).left).obj (Scheme.Modules.dual 𝓛) ⊗
          (Scheme.Modules.pullback (Spt L t z).left).obj (Scheme.Modules.dual 𝓛)) := by
  letI := L.grpObjOverMk
  unfold mumfordBundle
  exact Scheme.Modules.pullbackTensorObjIso _ _ _ ≪≫
    (cmp t z _ _ (sliceAt_addMor L t z) 𝓛 ⊗ᵢ (Scheme.Modules.pullbackTensorObjIso _ _ _ ≪≫
      (cmp t z _ _ (sliceAt_fst L t z) _ ⊗ᵢ cmp t z _ _ (sliceAt_snd L t z) _)))

def cancelIso {X : Scheme.{0}} (φ : X ⟶ A) (𝓛 : A.Modules) (e𝓛 : 𝓛 ⊗ Scheme.Modules.dual 𝓛 ≅ 𝟙_ A.Modules) :
    (Scheme.Modules.pullback φ).obj 𝓛 ⊗ (Scheme.Modules.pullback φ).obj (Scheme.Modules.dual 𝓛) ≅ 𝟙_ X.Modules :=
  (Scheme.Modules.pullbackTensorObjIso φ _ _).symm ≪≫ (Scheme.Modules.pullback φ).mapIso e𝓛 ≪≫
    Scheme.Modules.pullbackTensorUnitObjIso φ

def pairCancel {P Q DP DQ : (pullback f t).Modules} (eP : P ⊗ DP ≅ 𝟙_ _) (eQ : Q ⊗ DQ ≅ 𝟙_ _) :
    (P ⊗ Q) ⊗ (DP ⊗ DQ) ≅ 𝟙_ _ :=
  swapMid P Q DP DQ ≪≫ (eP ⊗ᵢ eQ) ≪≫ λ_ _

theorem main (hc : L.IsCommutative) (hA : AbelianSchemePropertyBundle S f)
    (𝓛 : A.Modules) (h𝓛 : Scheme.Modules.IsInvertible 𝓛) (x y : SchemeHomOver t f) :
    Nonempty ((Scheme.Modules.pullback (sliceAt f x)).obj (mumfordBundle f L 𝓛) ⊗
        (Scheme.Modules.pullback (sliceAt f y)).obj (mumfordBundle f L 𝓛) ≅
      (Scheme.Modules.pullback (sliceAt f (L.mul t x y))).obj (mumfordBundle f L 𝓛) ⊗
        (Scheme.Modules.pullback (Y (f := f) t).hom).obj
          (Scheme.Modules.dual ((Scheme.Modules.pullback (L.one (𝟙 (Spec (CommRingCat.of S)))).1).obj 𝓛))) := by
  letI := L.grpObjOverMk
  obtain ⟨e𝓛⟩ := (Scheme.Modules.IsInvertible.dual_monoidalV2 h𝓛).2
  have he : Scheme.Modules.IsInvertible ((Scheme.Modules.pullback (L.one (𝟙 (Spec (CommRingCat.of S)))).1).obj 𝓛) := h𝓛.pullback _
  obtain ⟨eE⟩ := (Scheme.Modules.IsInvertible.dual_monoidalV2 he).2
  obtain ⟨c⟩ := cube L t hc hA 𝓛 h𝓛 x y
  have hFS : (Fpt L t * Spt L t x * Spt L t y).left = (Fpt L t * Spt L t (L.mul t x y)).left := by
    rw [mul_assoc, Spt_mul_Spt]
  have hS : (Spt L t x * Spt L t y).left = (Spt L t (L.mul t x y)).left := by
    rw [Spt_mul_Spt]
  have T := tetris c (cancelIso (Fpt L t).left 𝓛 e𝓛) (cancelIso (Spt L t x).left 𝓛 e𝓛)
    (cancelIso (Spt L t y).left 𝓛 e𝓛)
    (pairCancel t (cancelIso (Spt L t x * Spt L t y).left 𝓛 e𝓛) (cancelIso (Y (f := f) t).hom _ eE))
  let B := ((Scheme.Modules.pullbackCongr hFS).app 𝓛 ⊗ᵢ
      (Iso.refl ((Scheme.Modules.pullback (Fpt L t).left).obj (Scheme.Modules.dual 𝓛)) ⊗ᵢ
        (Scheme.Modules.pullbackCongr hS).app (Scheme.Modules.dual 𝓛))) ≪≫ (sliceIso L t 𝓛 (L.mul t x y)).symm
  exact ⟨(sliceIso L t 𝓛 x ⊗ᵢ sliceIso L t 𝓛 y) ≪≫ T ≪≫ whiskerLeftIso _ (α_ _ _ _).symm ≪≫ (α_ _ _ _).symm ≪≫
    (B ⊗ᵢ Iso.refl _)⟩

end SliceAdd

end

theorem solution
    (S : Type) [CommRing S] {A : Scheme.{0}} (f : A ⟶ Spec (CommRingCat.of S))
    (L : RelativeGroupLaw S f) (hc : L.IsCommutative) (hA : AbelianSchemePropertyBundle S f) (𝓛 : A.Modules) (h𝓛 : Scheme.Modules.IsInvertible 𝓛)
    (R : Type) [CommRing R] (t : Spec (CommRingCat.of R) ⟶ Spec (CommRingCat.of S)) (x y : SchemeHomOver t f) :
    LocIsoOnBase (pullback.snd f t) ((Scheme.Modules.pullback (sliceAt f (L.mul t x y))).obj (mumfordBundle f L 𝓛)) ((Scheme.Modules.pullback (sliceAt f x)).obj (mumfordBundle f L 𝓛) ⊗ (Scheme.Modules.pullback (sliceAt f y)).obj (mumfordBundle f L 𝓛)) := by
  obtain ⟨e⟩ := SliceAdd.main L t hc hA 𝓛 h𝓛 x y
  have Q := LocIsoOnBase.equivalence (S := R) (pullback.snd f t)
  have ofIso : ∀ {M M' : (pullback f t).Modules}, (M ≅ M') → LocIsoOnBase (pullback.snd f t) M M' :=
    fun e _ => ⟨⊤, trivial, ⟨(Scheme.Modules.pullback _).mapIso e⟩⟩

  have hE := SliceAdd.locIsoOnBase_Efac L t (Scheme.Modules.dual 𝓛) (Scheme.Modules.IsInvertible.dual_monoidalV2 h𝓛).1
  have hD : LocIsoOnBase (pullback.snd f t)
      ((Scheme.Modules.pullback (SliceAdd.Y (f := f) t).hom).obj
        (Scheme.Modules.dual ((Scheme.Modules.pullback (L.one (𝟙 (Spec (CommRingCat.of S)))).1).obj 𝓛))) (𝟙_ _) := by
    obtain ⟨d⟩ := Scheme.Modules.IsInvertible.pullback_dual_monoidalV2 (L.one (𝟙 (Spec (CommRingCat.of S)))).1 h𝓛
    exact Q.trans (ofIso ((Scheme.Modules.pullback _).mapIso d.symm)) hE
  exact Q.symm (Q.trans (ofIso e) (Q.trans (LocIsoOnBase.tensor (Q.refl _) hD) (ofIso (ρ_ _))))

end S_AlgebraicGeometry_Polarisation_locIsoOnBase_sliceAt_mumfordBundle_mul_tensor_of_commRing
end P2MW
export P2MW.S_AlgebraicGeometry_Polarisation_locIsoOnBase_sliceAt_mumfordBundle_mul_tensor_of_commRing (solution)
