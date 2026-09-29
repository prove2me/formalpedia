-- Prove2me | solution 1 for AlgebraicGeometry.Polarisation.nonempty_pullback_mul_mul_tensor_iso_tensor_pullback_one_of_commRing
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:02.935278+00:00
-- url     : https://prove2.me/submissions/973efab6-628c-5e25-b18f-43cc4b0fc5a9

import Mathlib
import Definitions.Def_AlgebraicGeometry_PolarisationRosati
import Definitions.Def_AlgebraicGeometry_RelativeGroupLawGrpObj
import Definitions.Def_AlgebraicGeometry_ModulesPullbackMonoidalV2
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import Definitions.Def_GoodReductionJacobian_RelativeGroupLawProd
import Theorems.Thm_AlgebraicGeometry_RelPicard_RigidifiedLineBundle_nonempty_iso_unit_of_locIsoOnBase_unit_faces
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_IsInvertible_dual_monoidalV2
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_IsInvertible_pullback_dual_monoidalV2
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_IsInvertible_tensor_monoidalV2
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_Polarisation_nonempty_pullback_mul_mul_tensor_iso_tensor_pullback_one_of_commRing
p2m_attr_erase "instance" "TwoChartCech.Sections.M0_moduleA TwoChartCech.Sections.M1_module TwoChartCech.Cover.A01_algebra TwoChartCech.Cover.A0_algebra TwoChartCech.Cover.A1_commRing TwoChartCech.Cover.A1_algebra TwoChartCech.Sections.M01_module TwoChartCech.Sections.M0_addCommGroup TwoChartCech.Sections.M0_tower TwoChartCech.Sections.M01_addCommGroup TwoChartCech.Cover.A0_commRing TwoChartCech.Sections.M1_tower TwoChartCech.Sections.M01_moduleA TwoChartCech.Sections.M0_module TwoChartCech.Sections.M1_moduleA TwoChartCech.Sections.M1_addCommGroup TwoChartCech.Cover.A01_commRing TwoChartCech.Sections.M01_tower CoherentBaseChange.TwoTermComplex.C0_module CoherentBaseChange.TwoTermComplex.C0_addCommGroup CoherentBaseChange.TwoTermComplex.C1_module CoherentBaseChange.TwoTermComplex.C1_addCommGroup CoherentBaseChange.TwoTermComplex.C0_free CoherentBaseChange.TwoTermComplex.C1_finite CoherentBaseChange.TwoTermComplex.C0_finite CoherentBaseChange.TwoTermComplex.C1_free AlgebraicGeometry.SubalgebraStages.compactSpace_pullback AlgebraicGeometry.SubalgebraStages.quasiSeparatedSpace_pullback AlgebraicGeometry.SubalgebraStages.compactSpace_obj AlgebraicGeometry.SubalgebraStages.quasiSeparatedSpace_obj AlgebraicGeometry.SubalgebraStages.quasiCompact_snd AlgebraicGeometry.SubalgebraStages.isAffineHom_leg AlgebraicGeometry.SubalgebraStages.isAffineHom_trans AlgebraicGeometry.SubalgebraStages.isAffineHom_diagram_map AlgebraicGeometry.SubalgebraStages.quasiSeparated_snd AlgebraicGeometry.SubalgebraStages.isCofiltered_op IsDirectLimit.Module.instDirectLimitCoeLinearMapIdOfOfNonempty AdicCompletion.instIsLocalRingMaximalIdeal AlgebraicGeometry.OModulePresheaf.isScalarTower AlgebraicGeometry.Scheme.OrderedAffineCover.instLinearOrder"
p2m_attr_erase "instance" "AlgebraicGeometry.OModulePresheaf.module AlgebraicGeometry.Scheme.OrderedAffineCover.instFintype AlgebraicGeometry.Scheme.OrderedAffineCover.instFintypeIdx AlgebraicGeometry.OModulePresheaf.addCommGroup AlgebraicGeometry.Scheme.OrderedAffineCover.instDecidableEqIdx AlgebraicGeometry.OModulePresheaf.moduleSections AlgebraicGeometry.OModulePresheaf.instSubsingletonObjZero AlgebraicGeometry.OModulePresheaf.Leray.relAltC_scalarTower AlgebraicGeometry.OModulePresheaf.Leray.ker_relAltd_modΓ AlgebraicGeometry.OModulePresheaf.Leray.relAltC_modΓ AlgebraicGeometry.OModulePresheaf.Leray.biC_abGrp AlgebraicGeometry.OModulePresheaf.Leray.relAltH_modΓ AlgebraicGeometry.OModulePresheaf.Leray.ker_relAltd_smul AlgebraicGeometry.OModulePresheaf.Leray.relAltH_scalarTower AlgebraicGeometry.OModulePresheaf.Leray.relAltH_smul AlgebraicGeometry.OModulePresheaf.Leray.biC_module AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instDecidableEqIdx AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instFintype AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instLinearOrder AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instFintypeIdx DoubleComplex.instModuleE₂I DoubleComplex.Bounded.modR DoubleComplex.instModuleE₂II DoubleComplex.instAddCommGroupE₂II DoubleComplex.Bounded.abGrp DoubleComplex.instAddCommGroupE₂I ProjSpaceCech.GradedModule.H.module ProjSpaceCech.GradedModule.H.addCommGroup ProjSpaceCech.GradedModule.sec.instAdd ProjSpaceCech.GradedModule.sec.instNeg ProjSpaceCech.GradedModule.acg ProjSpaceCech.GradedModule.Frac.setoid ProjSpaceCech.GradedModule.modR ProjSpaceCech.GradedModule.sec.instModule ProjSpaceCech.GradedModule.sec.instAddCommGroup ProjSpaceCech.GradedModule.sec.instZero ProjSpaceCech.GradedModule.Presentation.fJ ProjSpaceCech.GradedModule.sec.instSMul ProjSpaceCech.Twist.H.module ProjSpaceCech.Idx.instFintype"
p2m_attr_erase "instance" "ProjSpaceCech.Twist.H.addCommGroup ProjSpaceCech.Idx.instDecidableEq ProjSpaceCech.Twist.Mon.instDecidableEq ProjSpaceCech.Twist.cochain.instAddCommGroup ProjSpaceCech.Twist.cochain.instModule AlgebraicGeometry.Scheme.Modules.GlueOfCocycle.instSMulCarrierObjOppositeOpensCarrierCarrierCommRingCatPresheafOpOpensSubtypeForallMinMemAddSubgroupFamilies AlgebraicGeometry.Scheme.Modules.GlueOfCocycle.instModulePreGlue AlgebraicGeometry.Scheme.Modules.GlueOfCocycle.instModuleCarrierObjOppositeOpensCarrierCarrierCommRingCatPresheafOpOpensSubtypeForallMinMemAddSubgroupFamilies SheafOfModules.isIso_ihomModelToIhom PresheafOfModules.ExteriorPower.instModulePresheafAb AlgebraicGeometry.Scheme.OrderedOpenFamily.instFintype AlgebraicGeometry.Scheme.OrderedOpenFamily.instDecidableEqIdx AlgebraicGeometry.Scheme.OrderedOpenFamily.instLinearOrder AlgebraicGeometry.Scheme.OrderedOpenFamily.instFintypeIdx CochainCx.Bounded.abGrp CochainCx.Bounded.modR instTopologicallyFGOfFiniteType AlgebraicCurve.CurveModel.isProper AlgebraicCurve.CurveModel.isIntegral AlgebraicCurve.CurveModel.smooth AlgebraicCurve.Place.instIsScalarTowerSubtypeMemValuationSubringToValuationSubring AlgebraicCurve.Divisor.instDistribMulActionAlgEquiv AlgebraicCurve.Place.instSMulAlgEquiv AlgebraicCurve.Place.instIsPrincipalIdealRingSubtypeMemValuationSubringToValuationSubring AlgebraicCurve.Place.instIsDiscreteValuationRingSubtypeMemValuationSubringToValuationSubring AlgebraicCurve.Pic0.instDistribMulActionAlgEquiv AlgebraicCurve.Place.instAlgebraSubtypeMemValuationSubringToValuationSubring AlgebraicCurve.Place.instMulActionAlgEquiv AlgebraicCurve.Pic0.instSMulAlgEquiv AlgebraicCurve.CurveModel.locallyOfFiniteType_gluedToBase AlgebraicCurve.CurveModel.isFractionRing_overlap AlgebraicCurve.CurveModel.isLocallyNoetherian_glued AlgebraicCurve.CurveModel.jacobsonSpace_glued AlgebraicCurve.CurveModel.isOpenImmersion_ι₀ AlgebraicCurve.CurveModel.isIntegral_glued AlgebraicCurve.CurveModel.quasiSeparated_gluedToBase AlgebraicCurve.CurveModel.compactSpace_glued AlgebraicCurve.CurveModel.isIntegral_adjoin_chartRing AlgebraicCurve.CurveModel.isFractionRing_overlap_functionField AlgebraicCurve.CurveModel.isProper_gluedToBase"
p2m_attr_erase "instance" "AlgebraicCurve.CurveModel.isOpenImmersion_ιU AlgebraicCurve.CurveModel.isOpenImmersion_f₀ AlgebraicCurve.CurveModel.isOpenImmersion_fInf AlgebraicCurve.CurveModel.isOpenImmersion_ιInf AlgebraicCurve.CurveModel.algebra_overlap_functionField AlgebraicCurve.CurveModel.quasiCompact_gluedToBase AlgebraicCurve.CurveModel.algebraAdjoin AlgebraicCurve.CurveModel.isDedekindDomain_chartRing AlgebraicCurve.CurveModel.isIntegralClosure AlgebraicCurve.CurveModel.finite_chartRing AlgebraicCurve.CurveModel.centre_isPrime AlgebraicCurve.CurveModel.isFractionRing_chartRing AlgebraicCurve.CurveModel.finiteType_chartRing AlgebraicCurve.CurveModel.isNoetherianRing_chartRing AlgebraicCurve.CurveModel.isScalarTower_base_adjoin AlgebraicCurve.CurveModel.isScalarTower_adjoin AlgebraicCurve.CurveModel.chartRing_finitePresentation AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation"
p2m_attr_erase "simp" "AlgebraicGeometry.RelPicard.RepresentsRelSubPic.mk.injEq AlgebraicGeometry.RelPicard.SubPicCondition.mk.injEq AlgebraicGeometry.RelPicard.SubPicCondition.mk.sizeOf_spec AlgebraicGeometry.RelPicard.RepresentsRelSubPic.mk.sizeOf_spec AlgebraicGeometry.Scheme.TwoAffineOpenCover.mk.injEq AlgebraicGeometry.Scheme.TwoAffineOpenCover.mk.sizeOf_spec AlgebraicGeometry.Scheme.TwoAffineOpenCover.pullback_U1 AlgebraicGeometry.Scheme.TwoAffineOpenCover.pullback_U0 TwoChartCech.Sections.mk.injEq TwoChartCech.Cover.mk.injEq TwoChartCech.GrothendieckComplex.mk.injEq TwoChartCech.Sections.mk.sizeOf_spec TwoChartCech.Cover.mk.sizeOf_spec TwoChartCech.Cover.lineBundle_r0_apply TwoChartCech.GrothendieckComplex.mk.sizeOf_spec TwoChartCech.Cover.lineBundle_r1_apply CoherentBaseChange.TwoTermComplex.mk.sizeOf_spec CoherentBaseChange.TwoTermComplex.mk.injEq AlgebraicGeometry.SubalgebraStages.specCone_π_app AlgebraicGeometry.SubalgebraStages.specLeg_specHom AlgebraicGeometry.SubalgebraStages.specLeg_specTrans AlgebraicGeometry.SubalgebraStages.cone_pt AlgebraicGeometry.SubalgebraStages.trans_fst AlgebraicGeometry.SubalgebraStages.diagram_obj AlgebraicGeometry.SubalgebraStages.leg_snd AlgebraicGeometry.SubalgebraStages.diagram_map AlgebraicGeometry.SubalgebraStages.specTrans_refl AlgebraicGeometry.SubalgebraStages.trans_snd AlgebraicGeometry.SubalgebraStages.specTrans_specHom AlgebraicGeometry.SubalgebraStages.specCone_pt AlgebraicGeometry.SubalgebraStages.cone_π_app AlgebraicGeometry.SubalgebraStages.specDiagram_map AlgebraicGeometry.SubalgebraStages.specDiagram_obj AlgebraicGeometry.SubalgebraStages.leg_fst AlgebraicGeometry.SubalgebraStages.leg_trans IsDirectLimit.Module.linearEquiv_symm_apply IsDirectLimit.linearEquiv_symm_apply IsDirectLimit.lift_of IsDirectLimit.Module.linearEquiv_apply IsDirectLimit.Module.lift_of"
p2m_attr_erase "simp" "IsDirectLimit.Equiv_apply RegularLocalRingQuotientAscent.dualNumberFst_apply GoodReductionJacobian.RelativeGroupLaw.baseChangePointToBase_ofBase GoodReductionJacobian.RelativeGroupLaw.baseChangePointToBase_coe GoodReductionJacobian.RelativeGroupLaw.baseChangePointOfBase_coe GoodReductionJacobian.RelativeGroupLaw.baseChange_inv GoodReductionJacobian.RelativeGroupLaw.baseChangePointOfBase_toBase GoodReductionJacobian.RelativeGroupLaw.baseChange_mul GoodReductionJacobian.RelativeGroupLaw.baseChange_one NeronSpecialFibreInfra.specialFibreRestrict_coe_comp_fst NeronSpecialFibreInfra.fibreRestrictAlong_coe_comp_snd NeronSpecialFibreInfra.fibreRestrictAlong_coe_comp_fst NeronSpecialFibreInfra.neronEndRestrictEquiv_apply NeronSpecialFibreInfra.fibreRestrictAlong_coe_comp_fst_assoc NeronSpecialFibreInfra.specialFibreRestrict_coe_comp_snd NeronSpecialFibreInfra.neronEndExtension_genericFibreRestrict NeronSpecialFibreInfra.specClosedFibreInclusion_eq NeronSpecialFibreInfra.specialFibreRestrict_coe_comp_fst_assoc NeronSpecialFibreInfra.specialFibreRestrict_coe_comp_snd_assoc NeronSpecialFibreInfra.genericFibreRestrict_neronEndExtension NeronSpecialFibreInfra.homOverId_coe NeronSpecialFibreInfra.homOverComp_coe NeronSpecialFibreInfra.fibreRestrictAlong_coe_comp_snd_assoc GoodReductionJacobian.RelativeGroupLaw.fibre_inv GoodReductionJacobian.RelativeGroupLaw.fibrePointToBase_coe GoodReductionJacobian.RelativeGroupLaw.fibrePointOfBase_toBase GoodReductionJacobian.RelativeGroupLaw.fibre_mul GoodReductionJacobian.RelativeGroupLaw.fibrePointToBase_ofBase GoodReductionJacobian.RelativeGroupLaw.fibre_one GoodReductionJacobian.RelativeGroupLaw.fibrePointOfBase_coe AlgebraicGeometry.schemeFibreEndo_snd AlgebraicGeometry.schemeFibreEndo_fst AlgebraicGeometry.Scheme.OrderedAffineCover.mk.injEq AlgebraicGeometry.OModulePresheaf.mk.sizeOf_spec AlgebraicGeometry.Scheme.OrderedAffineCover.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.mk.injEq AlgebraicGeometry.OModulePresheaf.prod_obj AlgebraicGeometry.OModulePresheaf.restrOpen_obj AlgebraicGeometry.OModulePresheaf.DevissageStep.mk.injEq AlgebraicGeometry.OModulePresheaf.pushforward_obj"
p2m_attr_erase "simp" "AlgebraicGeometry.OModulePresheaf.im_obj AlgebraicGeometry.OModulePresheaf.pow_obj AlgebraicGeometry.OModulePresheaf.fstHom_app AlgebraicGeometry.OModulePresheaf.ker_obj AlgebraicGeometry.OModulePresheaf.coker_obj AlgebraicGeometry.OModulePresheaf.DevissageStep.mk.sizeOf_spec AlgebraicGeometry.Scheme.OrderedAffineCover.preimage_U AlgebraicGeometry.OModulePresheaf.sndHom_app AlgebraicGeometry.OModulePresheaf.Hom.mk.injEq AlgebraicGeometry.OModulePresheaf.Hom.id_app AlgebraicGeometry.OModulePresheaf.AffHom.appSections_apply AlgebraicGeometry.OModulePresheaf.AffHom.comp_app AlgebraicGeometry.OModulePresheaf.AffSES.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.AffHom.kerMap_coe AlgebraicGeometry.OModulePresheaf.AffHom.id_app AlgebraicGeometry.OModulePresheaf.Hom.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.Hom.toAffHom_app AlgebraicGeometry.OModulePresheaf.SES.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.AffHom.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.Hom.comp_app AlgebraicGeometry.OModulePresheaf.SES.mk.injEq AlgebraicGeometry.OModulePresheaf.AffHom.mk.injEq AlgebraicGeometry.OModulePresheaf.Hom.appSections_apply AlgebraicGeometry.OModulePresheaf.AffSES.mk.injEq AlgebraicGeometry.OModulePresheaf.Leray.restrictToPreimage_U AlgebraicGeometry.Scheme.OrderedAffineCover.toCoverOf_U AlgebraicGeometry.Scheme.OrderedAffineCoverOf.mk.sizeOf_spec AlgebraicGeometry.Scheme.OrderedAffineCoverOf.mk.injEq AlgebraicGeometry.Scheme.OrderedAffineCover.restrict_U DoubleComplex.Bounded.mk.injEq DoubleComplex.Bounded.mk.sizeOf_spec DoubleComplex.Convergence.mk.injEq DoubleComplex.Convergence.mk.sizeOf_spec DoubleComplex.SubQuot.mk.sizeOf_spec DoubleComplex.SubQuot.mk.injEq ProjSpaceCech.GradedModule.mk.injEq ProjSpaceCech.GradedModule.mk.sizeOf_spec ProjSpaceCech.GradedModule.Frac.mk.sizeOf_spec ProjSpaceCech.GradedModule.Presentation.mk.injEq ProjSpaceCech.GradedModule.Frac.mk.injEq"
p2m_attr_erase "simp" "ProjSpaceCech.GradedModule.Presentation.mk.sizeOf_spec ProjSpaceCech.GradedModule.Hom.shift_toLinearMap ProjSpaceCech.GradedModule.Hom.mk.sizeOf_spec ProjSpaceCech.GradedModule.Hom.mk.injEq AlgebraicGeometry.Scheme.Modules.tensorSections_zero_right AlgebraicGeometry.Scheme.Modules.map_unitSection AlgebraicGeometry.Scheme.Modules.tensorSectionsBilin_apply AlgebraicGeometry.Scheme.Modules.tensorPowSection_zero AlgebraicGeometry.Scheme.Modules.tensorSections_zero_left AlgebraicGeometry.Scheme.Modules.tensorPow_zero AlgebraicGeometry.Scheme.Modules.tensorPow_succ AlgebraicGeometry.Scheme.Modules.glueComponent_glueMk AlgebraicGeometry.Scheme.Modules.UnitCocycle.mk.injEq AlgebraicGeometry.Scheme.Modules.UnitCocycle.mk.sizeOf_spec AlgebraicGeometry.Scheme.Modules.pullbackLocalSection_neg AlgebraicGeometry.Scheme.Modules.pullbackLocalSection_zero AlgebraicGeometry.Scheme.Modules.pullbackLocalSection_sub AlgebraicGeometry.Scheme.Modules.pullbackLocalSection_add PresheafOfModules.InternalHom.IsSheafAux.appAt_toPresheafHom SheafOfModules.ihomSectionsEquivFamily_unit AlgebraicGeometry.Scheme.Modules.restrictHomEquivFamily_apply SheafOfModules.ihomEval_unit_app AlgebraicGeometry.Scheme.Modules.ihomEval_zero_right AlgebraicGeometry.Scheme.Modules.ihomEval_zero_left AlgebraicGeometry.Scheme.Modules.homOfFamily_app_apply SheafOfModules.unit_ihomSectionsEquivFamily AlgebraicGeometry.Scheme.Modules.familyOfHom_app AlgebraicGeometry.Scheme.Modules.restrictUnitIso_hom_app_apply AlgebraicGeometry.Scheme.Modules.restrictUnitIso_inv_app_apply AlgebraicGeometry.Scheme.Modules.restrictHomOfFamily_app_apply AlgebraicGeometry.Scheme.Modules.restrictHomEquivFamily_symm_apply GoodReductionJacobian.RelativeGroupLaw.sndPoint_coe GoodReductionJacobian.RelativeGroupLaw.fstPoint_coe AlgebraicGeometry.tilde.functorCompPullbackSpecIso_app AlgebraicGeometry.Scheme.Hom.kaehlerPresheaf_obj PresheafOfModules.exteriorPower_map_ιMulti PresheafOfModules.ExteriorPower.appₗ_apply AlgebraicGeometry.Scheme.Modules.exteriorPower_obj AlgebraicGeometry.Scheme.OrderedOpenFamily.mk.injEq AlgebraicGeometry.Scheme.OrderedOpenFamily.mk.sizeOf_spec"
p2m_attr_erase "simp" "CochainCx.Bounded.mk.sizeOf_spec CochainCx.Bounded.mk.injEq AlgebraicCurve.CurveModel.mk.injEq AlgebraicCurve.CurveModel.mk.sizeOf_spec AlgebraicCurve.Place.mk.injEq AlgebraicCurve.Divisor.degree_single AlgebraicCurve.Divisor.smul_single AlgebraicCurve.Place.smul_toValuationSubring AlgebraicCurve.Place.heightOneSpectrum_asIdeal AlgebraicCurve.Place.coe_algebraMap AlgebraicCurve.Place.ord_one AlgebraicCurve.Place.coe_smulRingEquiv_apply AlgebraicCurve.Pic0.coe_degZeroSMulHom AlgebraicCurve.Place.deg_smul AlgebraicCurve.Pic0.mk_zero AlgebraicCurve.Place.mk.sizeOf_spec AlgebraicCurve.Divisor.degree_smul AlgebraicCurve.Pic0.mk_add AlgebraicCurve.Place.ord_zero AlgebraicCurve.Place.ofHeightOneSpectrum_toValuationSubring AlgebraicCurve.CurveModel.coe_gInf AlgebraicCurve.CurveModel.coe_tInvChart AlgebraicCurve.CurveModel.ιInf_gluedToBase_assoc AlgebraicCurve.CurveModel.ιInf_gluedToBase AlgebraicCurve.CurveModel.primeOfι₀_asIdeal AlgebraicCurve.CurveModel.coe_tChart AlgebraicCurve.CurveModel.ι₀_gluedToBase_assoc AlgebraicCurve.CurveModel.primeOfιInf_asIdeal AlgebraicCurve.CurveModel.ι₀_gluedToBase AlgebraicCurve.CurveModel.coe_tma AlgebraicCurve.CurveModel.coe_primeEquivChartPlaces AlgebraicCurve.Place.congrEquiv_symm_apply AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply AlgebraicCurve.RationalFunctionField.deg_placeOfPoint"

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

p2m_open "CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory AlgebraicGeometry NeronModelInfra GoodReductionJacobian AlgebraicGeometry.Polarisation"

open scoped CategoryTheory.MonObj

noncomputable section

namespace CubePBS

p2m_open "CategoryTheory.CartesianMonoidalCategory AlgebraicGeometry.RelPicard"

section Skel

universe v' u'
variable {C : Type u'} [Category.{v'} C] [MonoidalCategory C]

theorem cls_tensor (A B : C) : toSkeleton (A ⊗ B) = toSkeleton A * toSkeleton B :=
  Skeleton.toSkeleton_tensorObj A B

theorem cls_unit : toSkeleton (𝟙_ C) = (1 : Skeleton C) := Skeleton.one_eq.symm

theorem cls_congr {A B : C} (e : A ≅ B) : toSkeleton A = toSkeleton B :=
  toSkeleton_eq_toSkeleton_iff.mpr ⟨e⟩

theorem cls_of_nonempty {A B : C} (e : Nonempty (A ≅ B)) : toSkeleton A = toSkeleton B :=
  toSkeleton_eq_toSkeleton_iff.mpr e

end Skel

section Pull

universe u
variable {S T V : Scheme.{u}}

noncomputable abbrev pcls (φ : S ⟶ T) (A : T.Modules) : Skeleton S.Modules :=
  toSkeleton ((Scheme.Modules.pullback φ).obj A)

theorem pcls_tensor (φ : S ⟶ T) (A B : T.Modules) :
    pcls φ (A ⊗ B) = pcls φ A * pcls φ B := by
  rw [pcls, cls_congr (Scheme.Modules.pullbackTensorObjIso φ A B), cls_tensor]

theorem pcls_unit (φ : S ⟶ T) : pcls φ (𝟙_ T.Modules) = 1 := by
  rw [pcls, cls_congr (Scheme.Modules.pullbackTensorUnitObjIso φ), cls_unit]

theorem pcls_comp (φ : S ⟶ T) (ψ : T ⟶ V) (A : V.Modules) :
    pcls φ ((Scheme.Modules.pullback ψ).obj A) = pcls (φ ≫ ψ) A :=
  cls_congr ((Scheme.Modules.pullbackComp φ ψ).app A)

theorem pcls_congr_hom {φ ψ : S ⟶ T} (h : φ = ψ) (A : T.Modules) : pcls φ A = pcls ψ A := by
  subst h; rfl

theorem pcls_congr_obj (φ : S ⟶ T) {A B : T.Modules} (h : toSkeleton A = toSkeleton B) :
    pcls φ A = pcls φ B :=
  cls_congr ((Scheme.Modules.pullback φ).mapIso (Skeleton.isoOfEq h))

theorem pcls_eq_one_of_cls_eq_one (φ : S ⟶ T) {A : T.Modules} (h : toSkeleton A = 1) :
    pcls φ A = 1 := by
  rw [pcls_congr_obj φ (h.trans cls_unit.symm), pcls_unit]

theorem cls_mul_cls_dual {A : T.Modules} (hA : Scheme.Modules.IsInvertible A) :
    toSkeleton A * toSkeleton (Scheme.Modules.dual A) = 1 := by
  rw [← cls_tensor, cls_of_nonempty hA.dual_monoidalV2.2, cls_unit]

theorem pcls_dual (φ : S ⟶ T) {A : T.Modules} (hA : Scheme.Modules.IsInvertible A) :
    pcls φ (Scheme.Modules.dual A) =
      toSkeleton (Scheme.Modules.dual ((Scheme.Modules.pullback φ).obj A)) :=
  cls_of_nonempty (hA.pullback_dual_monoidalV2 φ)

end Pull

section Generic

variable {S : Type} [CommRing S] {X : Scheme.{0}} (f : X ⟶ Spec (CommRingCat.of S))
    [GrpObj (Over.mk f)] (𝓛 : X.Modules) (e : Spec (CommRingCat.of S) ⟶ X)

noncomputable abbrev P {T : Over (Spec (CommRingCat.of S))} (g : T ⟶ Over.mk f) : T.left.Modules :=
  (Scheme.Modules.pullback g.left).obj 𝓛

noncomputable abbrev Λ {T : Over (Spec (CommRingCat.of S))} (g : T ⟶ Over.mk f) : Skeleton T.left.Modules :=
  pcls g.left 𝓛

theorem Λ_comp {T T' : Over (Spec (CommRingCat.of S))} (σ : T' ⟶ T) (g : T ⟶ Over.mk f) :
    pcls σ.left (P f 𝓛 g) = Λ f 𝓛 (σ ≫ g) := by
  rw [Λ, Over.comp_left]; exact pcls_comp _ _ _

noncomputable abbrev EM (T : Over (Spec (CommRingCat.of S))) : T.left.Modules :=
  (Scheme.Modules.pullback T.hom).obj ((Scheme.Modules.pullback e).obj 𝓛)

noncomputable abbrev Ecls (T : Over (Spec (CommRingCat.of S))) : Skeleton T.left.Modules :=
  pcls T.hom ((Scheme.Modules.pullback e).obj 𝓛)

theorem Ecls_comp {T T' : Over (Spec (CommRingCat.of S))} (σ : T' ⟶ T) :
    pcls σ.left (EM 𝓛 e T) = Ecls 𝓛 e T' := by
  rw [EM, pcls_comp, pcls_congr_hom (Over.w σ)]

abbrev A3 : Over (Spec (CommRingCat.of S)) := (Over.mk f ⊗ Over.mk f) ⊗ Over.mk f

abbrev p₁ : A3 f ⟶ Over.mk f := fst _ _ ≫ fst _ _
abbrev p₂ : A3 f ⟶ Over.mk f := fst _ _ ≫ snd _ _
abbrev p₃ : A3 f ⟶ Over.mk f := snd _ _

noncomputable abbrev M₁ : (A3 f).left.Modules :=
  P f 𝓛 (p₁ f * p₂ f * p₃ f) ⊗ (P f 𝓛 (p₁ f) ⊗ (P f 𝓛 (p₂ f) ⊗ P f 𝓛 (p₃ f)))

noncomputable abbrev M₂ : (A3 f).left.Modules :=
  P f 𝓛 (p₁ f * p₂ f) ⊗ (P f 𝓛 (p₁ f * p₃ f) ⊗ (P f 𝓛 (p₂ f * p₃ f) ⊗ EM 𝓛 e (A3 f)))

theorem isInvertible_M₁ (hL : Scheme.Modules.IsInvertible 𝓛) :
    Scheme.Modules.IsInvertible (M₁ f 𝓛) :=
  (hL.pullback _).tensor_monoidalV2 ((hL.pullback _).tensor_monoidalV2
    ((hL.pullback _).tensor_monoidalV2 (hL.pullback _)))

theorem isInvertible_M₂ (hL : Scheme.Modules.IsInvertible 𝓛) :
    Scheme.Modules.IsInvertible (M₂ f 𝓛 e) :=
  (hL.pullback _).tensor_monoidalV2 ((hL.pullback _).tensor_monoidalV2
    ((hL.pullback _).tensor_monoidalV2 ((hL.pullback _).pullback _)))

theorem pcls_M₁ {T : Over (Spec (CommRingCat.of S))} (σ : T ⟶ A3 f) (a b c : T ⟶ Over.mk f)
    (ha : σ ≫ p₁ f = a) (hb : σ ≫ p₂ f = b) (hc : σ ≫ p₃ f = c) :
    pcls σ.left (M₁ f 𝓛) =
      Λ f 𝓛 (a * b * c) * (Λ f 𝓛 a * (Λ f 𝓛 b * Λ f 𝓛 c)) := by
  rw [M₁, pcls_tensor, pcls_tensor, pcls_tensor, Λ_comp, Λ_comp, Λ_comp, Λ_comp,
    MonObj.comp_mul, MonObj.comp_mul, ha, hb, hc]

theorem pcls_M₂ {T : Over (Spec (CommRingCat.of S))} (σ : T ⟶ A3 f) (a b c : T ⟶ Over.mk f)
    (ha : σ ≫ p₁ f = a) (hb : σ ≫ p₂ f = b) (hc : σ ≫ p₃ f = c) :
    pcls σ.left (M₂ f 𝓛 e) =
      Λ f 𝓛 (a * b) * (Λ f 𝓛 (a * c) * (Λ f 𝓛 (b * c) * Ecls 𝓛 e T)) := by
  rw [M₂, pcls_tensor, pcls_tensor, pcls_tensor, Λ_comp, Λ_comp, Λ_comp, Ecls_comp,
    MonObj.comp_mul, MonObj.comp_mul, MonObj.comp_mul, ha, hb, hc]

noncomputable abbrev N : (A3 f).left.Modules :=
  M₁ f 𝓛 ⊗ Scheme.Modules.dual (M₂ f 𝓛 e)

theorem isInvertible_N (hL : Scheme.Modules.IsInvertible 𝓛) :
    Scheme.Modules.IsInvertible (N f 𝓛 e) :=
  (isInvertible_M₁ f 𝓛 hL).tensor_monoidalV2 (isInvertible_M₂ f 𝓛 e hL).dual_monoidalV2.1

theorem slice_trivial (hL : Scheme.Modules.IsInvertible 𝓛) {T : Over (Spec (CommRingCat.of S))}
    (σ : T ⟶ A3 f)
    (h : pcls σ.left (M₁ f 𝓛) = pcls σ.left (M₂ f 𝓛 e)) :
    Nonempty ((Scheme.Modules.pullback σ.left).obj (N f 𝓛 e) ≅ 𝟙_ _) := by
  apply toSkeleton_eq_toSkeleton_iff.mp
  rw [← pcls, N, pcls_tensor, h, pcls_dual _ (isInvertible_M₂ f 𝓛 e hL), pcls,
    cls_mul_cls_dual ((isInvertible_M₂ f 𝓛 e hL).pullback _), cls_unit]

theorem cls_M₁_eq_cls_M₂ (hL : Scheme.Modules.IsInvertible 𝓛) (hN : Nonempty (N f 𝓛 e ≅ 𝟙_ _)) :
    toSkeleton (M₁ f 𝓛) = toSkeleton (M₂ f 𝓛 e) := by
  have h1 : toSkeleton (N f 𝓛 e) = 1 := by rw [cls_of_nonempty hN, cls_unit]
  rw [N, cls_tensor] at h1
  have h2 := cls_mul_cls_dual (isInvertible_M₂ f 𝓛 e hL)
  calc toSkeleton (M₁ f 𝓛)
      = toSkeleton (M₁ f 𝓛) * (toSkeleton (M₂ f 𝓛 e) * toSkeleton (Scheme.Modules.dual (M₂ f 𝓛 e))) := by
        rw [h2, mul_one]
    _ = toSkeleton (M₁ f 𝓛) * toSkeleton (Scheme.Modules.dual (M₂ f 𝓛 e)) * toSkeleton (M₂ f 𝓛 e) := by
        rw [mul_assoc, mul_comm (toSkeleton (M₂ f 𝓛 e))]
    _ = toSkeleton (M₂ f 𝓛 e) := by rw [h1, one_mul]

theorem main (hL : Scheme.Modules.IsInvertible 𝓛) (hN : Nonempty (N f 𝓛 e ≅ 𝟙_ _))
    {Y : Over (Spec (CommRingCat.of S))} (g₁ g₂ g₃ : Y ⟶ Over.mk f) :
    Nonempty (
      (Scheme.Modules.pullback (g₁ * g₂ * g₃).left).obj 𝓛 ⊗ (Scheme.Modules.pullback g₁.left).obj 𝓛 ⊗
          (Scheme.Modules.pullback g₂.left).obj 𝓛 ⊗ (Scheme.Modules.pullback g₃.left).obj 𝓛 ≅
        (Scheme.Modules.pullback (g₁ * g₂).left).obj 𝓛 ⊗ (Scheme.Modules.pullback (g₁ * g₃).left).obj 𝓛 ⊗
          (Scheme.Modules.pullback (g₂ * g₃).left).obj 𝓛 ⊗
            (Scheme.Modules.pullback Y.hom).obj ((Scheme.Modules.pullback e).obj 𝓛)) := by
  apply toSkeleton_eq_toSkeleton_iff.mp
  let φ : Y ⟶ A3 f := lift (lift g₁ g₂) g₃
  have ha : φ ≫ p₁ f = g₁ := by rw [lift_fst_assoc, lift_fst]
  have hb : φ ≫ p₂ f = g₂ := by rw [lift_fst_assoc, lift_snd]
  have hc : φ ≫ p₃ f = g₃ := lift_snd _ _
  have E := pcls_congr_obj φ.left (cls_M₁_eq_cls_M₂ f 𝓛 e hL hN)
  rw [pcls_M₁ f 𝓛 φ g₁ g₂ g₃ ha hb hc, pcls_M₂ f 𝓛 e φ g₁ g₂ g₃ ha hb hc] at E
  simpa only [cls_tensor] using E

end Generic

section WithLaw

variable {S : Type} [CommRing S] {X : Scheme.{0}} (f : X ⟶ Spec (CommRingCat.of S))
    (G : RelativeGroupLaw S f) (𝓛 : X.Modules)

abbrev eG : Spec (CommRingCat.of S) ⟶ X := (G.one (𝟙 (Spec (CommRingCat.of S)))).1

theorem one_left (T : Over (Spec (CommRingCat.of S))) :
    letI := G.grpObjOverMk
    (1 : T ⟶ Over.mk f).left = (G.one T.hom).1 := by
  letI := G.grpObjOverMk
  exact congrArg Subtype.val (G.overHomEquivSchemeHomOver_one T)

theorem one_left' (T : Over (Spec (CommRingCat.of S))) :
    letI := G.grpObjOverMk
    (1 : T ⟶ Over.mk f).left = T.hom ≫ eG f G := by
  letI := G.grpObjOverMk
  rw [one_left]
  have h := G.one_natural (𝟙 (Spec (CommRingCat.of S))) T.hom T.hom (Category.comp_id _)
  exact (congrArg Subtype.val h).symm

theorem Λ_one (T : Over (Spec (CommRingCat.of S))) :
    letI := G.grpObjOverMk
    Λ f 𝓛 (1 : T ⟶ Over.mk f) = Ecls 𝓛 (eG f G) T := by
  letI := G.grpObjOverMk
  rw [Λ, pcls_congr_hom (one_left' f G T)]
  exact (pcls_comp _ _ _).symm

abbrev F₁ : pullback f f ⟶ pullback (prodStr f f) f :=
  pullback.lift
    (pullback.lift (G.one (prodStr f f)).1 (pullback.fst f f) (by rw [(G.one _).2]))
    (pullback.snd f f)
    (by rw [pullback.lift_fst_assoc, (G.one _).2]; exact pullback.condition)

abbrev F₂ : pullback f f ⟶ pullback (prodStr f f) f :=
  pullback.lift
    (pullback.lift (pullback.fst f f) (G.one (prodStr f f)).1 (by rw [(G.one _).2]))
    (pullback.snd f f)
    (by rw [pullback.lift_fst_assoc]; exact pullback.condition)

abbrev F₃ : pullback f f ⟶ pullback (prodStr f f) f :=
  pullback.lift (𝟙 _) (G.one (prodStr f f)).1 (by rw [Category.id_comp, (G.one _).2])

abbrev F₀ : X ⟶ pullback (prodStr f f) f :=
  rigSection (prodStr f f) f ((G.prod G).one (𝟙 (Spec (CommRingCat.of S))))

theorem F₁_fst_fst : F₁ f G ≫ pullback.fst _ _ ≫ pullback.fst f f = (G.one (prodStr f f)).1 := by
  rw [pullback.lift_fst_assoc, pullback.lift_fst]
theorem F₁_fst_snd : F₁ f G ≫ pullback.fst _ _ ≫ pullback.snd f f = pullback.fst f f := by
  rw [pullback.lift_fst_assoc, pullback.lift_snd]
theorem F₁_snd : F₁ f G ≫ pullback.snd _ _ = pullback.snd f f := by
  rw [pullback.lift_snd]
theorem F₂_fst_fst : F₂ f G ≫ pullback.fst _ _ ≫ pullback.fst f f = pullback.fst f f := by
  rw [pullback.lift_fst_assoc, pullback.lift_fst]
theorem F₂_fst_snd : F₂ f G ≫ pullback.fst _ _ ≫ pullback.snd f f = (G.one (prodStr f f)).1 := by
  rw [pullback.lift_fst_assoc, pullback.lift_snd]
theorem F₂_snd : F₂ f G ≫ pullback.snd _ _ = pullback.snd f f := by
  rw [pullback.lift_snd]
theorem F₃_fst_fst : F₃ f G ≫ pullback.fst _ _ ≫ pullback.fst f f = pullback.fst f f := by
  rw [pullback.lift_fst_assoc, Category.id_comp]
theorem F₃_fst_snd : F₃ f G ≫ pullback.fst _ _ ≫ pullback.snd f f = pullback.snd f f := by
  rw [pullback.lift_fst_assoc, Category.id_comp]
theorem F₃_snd : F₃ f G ≫ pullback.snd _ _ = (G.one (prodStr f f)).1 := by
  rw [pullback.lift_snd]
theorem F₀_fst_fst : F₀ f G ≫ pullback.fst _ _ ≫ pullback.fst f f = f ≫ eG f G := by
  simp only [F₀, rigSection, RelativeGroupLaw.prod_one, prodPairPt_coe, pullback.lift_fst_assoc, pullback.lift_fst,
    Category.assoc]
theorem F₀_fst_snd : F₀ f G ≫ pullback.fst _ _ ≫ pullback.snd f f = f ≫ eG f G := by
  simp only [F₀, rigSection, RelativeGroupLaw.prod_one, prodPairPt_coe, pullback.lift_fst_assoc, pullback.lift_snd,
    Category.assoc]
theorem F₀_snd : F₀ f G ≫ pullback.snd _ _ = 𝟙 X := by
  simp only [F₀, rigSection, pullback.lift_snd]

def σ₁ : Over.mk f ⊗ Over.mk f ⟶ A3 f :=
  Over.homMk (F₁ f G) (by
    show F₁ f G ≫ pullback.fst (prodStr f f) f ≫ pullback.fst f f ≫ f = pullback.fst f f ≫ f
    rw [pullback.lift_fst_assoc, pullback.lift_fst_assoc]; exact (G.one _).2)

def σ₂ : Over.mk f ⊗ Over.mk f ⟶ A3 f :=
  Over.homMk (F₂ f G) (by
    show F₂ f G ≫ pullback.fst (prodStr f f) f ≫ pullback.fst f f ≫ f = pullback.fst f f ≫ f
    rw [pullback.lift_fst_assoc, pullback.lift_fst_assoc])

def σ₃ : Over.mk f ⊗ Over.mk f ⟶ A3 f :=
  Over.homMk (F₃ f G) (by
    show F₃ f G ≫ pullback.fst (prodStr f f) f ≫ pullback.fst f f ≫ f = pullback.fst f f ≫ f
    rw [pullback.lift_fst_assoc, Category.id_comp])

def σ₀ : Over.mk f ⟶ A3 f :=
  Over.homMk (F₀ f G) (by
    show F₀ f G ≫ pullback.fst (prodStr f f) f ≫ prodStr f f = f
    rw [F₀, rigSection, pullback.lift_fst_assoc, Category.assoc, ((G.prod G).one _).2, Category.comp_id])

theorem σ₁_p₁ : letI := G.grpObjOverMk; σ₁ f G ≫ p₁ f = 1 := by
  letI := G.grpObjOverMk
  apply Over.OverMorphism.ext; rw [one_left]; exact F₁_fst_fst f G
theorem σ₁_p₂ : σ₁ f G ≫ p₂ f = fst _ _ := by
  apply Over.OverMorphism.ext; exact F₁_fst_snd f G
theorem σ₁_p₃ : σ₁ f G ≫ p₃ f = snd _ _ := by
  apply Over.OverMorphism.ext; exact F₁_snd f G
theorem σ₂_p₁ : σ₂ f G ≫ p₁ f = fst _ _ := by
  apply Over.OverMorphism.ext; exact F₂_fst_fst f G
theorem σ₂_p₂ : letI := G.grpObjOverMk; σ₂ f G ≫ p₂ f = 1 := by
  letI := G.grpObjOverMk
  apply Over.OverMorphism.ext; rw [one_left]; exact F₂_fst_snd f G
theorem σ₂_p₃ : σ₂ f G ≫ p₃ f = snd _ _ := by
  apply Over.OverMorphism.ext; exact F₂_snd f G
theorem σ₃_p₁ : σ₃ f G ≫ p₁ f = fst _ _ := by
  apply Over.OverMorphism.ext; exact F₃_fst_fst f G
theorem σ₃_p₂ : σ₃ f G ≫ p₂ f = snd _ _ := by
  apply Over.OverMorphism.ext; exact F₃_fst_snd f G
theorem σ₃_p₃ : letI := G.grpObjOverMk; σ₃ f G ≫ p₃ f = 1 := by
  letI := G.grpObjOverMk
  apply Over.OverMorphism.ext; rw [one_left]; exact F₃_snd f G
theorem σ₀_p₁ : letI := G.grpObjOverMk; σ₀ f G ≫ p₁ f = 1 := by
  letI := G.grpObjOverMk
  apply Over.OverMorphism.ext; rw [one_left']; exact F₀_fst_fst f G
theorem σ₀_p₂ : letI := G.grpObjOverMk; σ₀ f G ≫ p₂ f = 1 := by
  letI := G.grpObjOverMk
  apply Over.OverMorphism.ext; rw [one_left']; exact F₀_fst_snd f G
theorem σ₀_p₃ : σ₀ f G ≫ p₃ f = 𝟙 _ := by
  apply Over.OverMorphism.ext; exact F₀_snd f G

theorem pcls_σ₁ : letI := G.grpObjOverMk
    pcls (σ₁ f G).left (M₁ f 𝓛) = pcls (σ₁ f G).left (M₂ f 𝓛 (eG f G)) := by
  letI := G.grpObjOverMk
  rw [pcls_M₁ f 𝓛 (σ₁ f G) 1 (fst _ _) (snd _ _) (σ₁_p₁ f G) (σ₁_p₂ f G) (σ₁_p₃ f G),
    pcls_M₂ f 𝓛 (eG f G) (σ₁ f G) 1 (fst _ _) (snd _ _) (σ₁_p₁ f G) (σ₁_p₂ f G) (σ₁_p₃ f G)]
  simp only [one_mul, mul_one, Λ_one]
  all_goals ac_rfl

theorem pcls_σ₂ : letI := G.grpObjOverMk
    pcls (σ₂ f G).left (M₁ f 𝓛) = pcls (σ₂ f G).left (M₂ f 𝓛 (eG f G)) := by
  letI := G.grpObjOverMk
  rw [pcls_M₁ f 𝓛 (σ₂ f G) (fst _ _) 1 (snd _ _) (σ₂_p₁ f G) (σ₂_p₂ f G) (σ₂_p₃ f G),
    pcls_M₂ f 𝓛 (eG f G) (σ₂ f G) (fst _ _) 1 (snd _ _) (σ₂_p₁ f G) (σ₂_p₂ f G) (σ₂_p₃ f G)]
  simp only [one_mul, mul_one, Λ_one]
  all_goals ac_rfl

theorem pcls_σ₃ : letI := G.grpObjOverMk
    pcls (σ₃ f G).left (M₁ f 𝓛) = pcls (σ₃ f G).left (M₂ f 𝓛 (eG f G)) := by
  letI := G.grpObjOverMk
  rw [pcls_M₁ f 𝓛 (σ₃ f G) (fst _ _) (snd _ _) 1 (σ₃_p₁ f G) (σ₃_p₂ f G) (σ₃_p₃ f G),
    pcls_M₂ f 𝓛 (eG f G) (σ₃ f G) (fst _ _) (snd _ _) 1 (σ₃_p₁ f G) (σ₃_p₂ f G) (σ₃_p₃ f G)]
  simp only [one_mul, mul_one, Λ_one]

theorem pcls_σ₀ : letI := G.grpObjOverMk
    pcls (σ₀ f G).left (M₁ f 𝓛) = pcls (σ₀ f G).left (M₂ f 𝓛 (eG f G)) := by
  letI := G.grpObjOverMk
  rw [pcls_M₁ f 𝓛 (σ₀ f G) 1 1 (𝟙 _) (σ₀_p₁ f G) (σ₀_p₂ f G) (σ₀_p₃ f G),
    pcls_M₂ f 𝓛 (eG f G) (σ₀ f G) 1 1 (𝟙 _) (σ₀_p₁ f G) (σ₀_p₂ f G) (σ₀_p₃ f G)]
  simp only [one_mul, mul_one, Λ_one]
  all_goals ac_rfl

theorem locIsoOnBase_of_nonempty {S' : Type} [CommRing S'] {Z : Scheme.{0}} (g : Z ⟶ Spec (CommRingCat.of S'))
    {M M' : Z.Modules} (h : Nonempty (M ≅ M')) : LocIsoOnBase g M M' :=
  fun _ => ⟨⊤, trivial, ⟨(Scheme.Modules.pullback _).mapIso h.some⟩⟩

def Nrig (hL : Scheme.Modules.IsInvertible 𝓛) :
    letI := G.grpObjOverMk
    RigidifiedLineBundle (prodStr f f) ((G.prod G).one (𝟙 (Spec (CommRingCat.of S)))) f := by
  letI := G.grpObjOverMk
  exact
    { L := N f 𝓛 (eG f G)
      isInvertible := isInvertible_N f 𝓛 (eG f G) hL
      rigidified := slice_trivial f 𝓛 (eG f G) hL (σ₀ f G) (pcls_σ₀ f G 𝓛) }

theorem N_trivial (hA : AbelianSchemePropertyBundle S f) (hL : Scheme.Modules.IsInvertible 𝓛) :
    letI := G.grpObjOverMk
    Nonempty (N f 𝓛 (eG f G) ≅ 𝟙_ _) := by
  letI := G.grpObjOverMk
  obtain ⟨i⟩ := RigidifiedLineBundle.nonempty_iso_unit_of_locIsoOnBase_unit_faces G hA (Nrig f G 𝓛 hL)
    (locIsoOnBase_of_nonempty _ (slice_trivial f 𝓛 (eG f G) hL (σ₁ f G) (pcls_σ₁ f G 𝓛)))
    (locIsoOnBase_of_nonempty _ (slice_trivial f 𝓛 (eG f G) hL (σ₂ f G) (pcls_σ₂ f G 𝓛)))
    (locIsoOnBase_of_nonempty _ (slice_trivial f 𝓛 (eG f G) hL (σ₃ f G) (pcls_σ₃ f G 𝓛)))
  exact ⟨i⟩

end WithLaw

end CubePBS

end

theorem solution
    {S : Type} [CommRing S] {A : Scheme.{0}} (f : A ⟶ Spec (CommRingCat.of S))
    (L : RelativeGroupLaw S f) (hc : L.IsCommutative) (hA : AbelianSchemePropertyBundle S f)
    (𝓛 : A.Modules) (h𝓛 : Scheme.Modules.IsInvertible 𝓛)
    {Y : Over (Spec (CommRingCat.of S))} (g₁ g₂ g₃ : Y ⟶ Over.mk f) :
    letI := L.grpObjOverMk
    Nonempty (
      (Scheme.Modules.pullback (g₁ * g₂ * g₃).left).obj 𝓛 ⊗ (Scheme.Modules.pullback g₁.left).obj 𝓛 ⊗
          (Scheme.Modules.pullback g₂.left).obj 𝓛 ⊗ (Scheme.Modules.pullback g₃.left).obj 𝓛 ≅
        (Scheme.Modules.pullback (g₁ * g₂).left).obj 𝓛 ⊗ (Scheme.Modules.pullback (g₁ * g₃).left).obj 𝓛 ⊗
          (Scheme.Modules.pullback (g₂ * g₃).left).obj 𝓛 ⊗
            (Scheme.Modules.pullback Y.hom).obj
              ((Scheme.Modules.pullback (L.one (𝟙 (Spec (CommRingCat.of S)))).1).obj 𝓛)) := by
  letI := L.grpObjOverMk
  exact CubePBS.main f 𝓛 (CubePBS.eG f L) h𝓛 (CubePBS.N_trivial f L 𝓛 hA h𝓛) g₁ g₂ g₃

end S_AlgebraicGeometry_Polarisation_nonempty_pullback_mul_mul_tensor_iso_tensor_pullback_one_of_commRing
end P2MW
export P2MW.S_AlgebraicGeometry_Polarisation_nonempty_pullback_mul_mul_tensor_iso_tensor_pullback_one_of_commRing (solution)
