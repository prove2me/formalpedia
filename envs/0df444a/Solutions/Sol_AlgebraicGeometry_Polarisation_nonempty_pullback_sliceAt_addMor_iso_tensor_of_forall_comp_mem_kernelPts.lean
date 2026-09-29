-- Prove2me | solution 1 for AlgebraicGeometry.Polarisation.nonempty_pullback_sliceAt_addMor_iso_tensor_of_forall_comp_mem_kernelPts
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:02.935278+00:00
-- url     : https://prove2.me/submissions/b7d85e0d-f6c2-5aa7-a976-4280ee0e06cc

import Mathlib
import Definitions.Def_AlgebraicGeometry_PolarisedAbelianScheme
import Definitions.Def_AlgebraicGeometry_PolarisationRosati
import Definitions.Def_AlgebraicGeometry_PolarisationPicZero
import Definitions.Def_AlgebraicGeometry_ModulesTensorPowV2
import Definitions.Def_AlgebraicGeometry_ModulesPullbackMonoidalV2
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import Definitions.Def_AlgebraicGeometry_OrderedAffineCoverCech
import Definitions.Def_AlgebraicGeometry_OModulePresheafOfModules
import Definitions.Def_AlgebraicGeometry_OModulePresheafEulerChar
import Theorems.Thm_AlgebraicGeometry_RelPicard_RigidifiedLineBundle_nonempty_iso_unit_of_forall_pullbackAlong_point
import Theorems.Thm_AlgebraicGeometry_Polarisation_mem_kernelPts_iff_nonempty_pullback_sliceAt_mumfordBundle_iso_unit
import Theorems.Thm_AlgebraicGeometry_Polarisation_nonempty_pullback_pullbackSymmetry_mumfordBundle_iso
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_IsInvertible_dual_monoidalV2
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_IsInvertible_pullback_dual_monoidalV2
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_IsInvertible_tensor_monoidalV2
import Theorems.Thm_GoodReductionJacobian_AbelianSchemePropertyBundle_geometricallyIntegral
import Theorems.Thm_GoodReductionJacobian_AbelianSchemePropertyBundle_isCommutative
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_Polarisation_nonempty_pullback_sliceAt_addMor_iso_tensor_of_forall_comp_mem_kernelPts
p2m_attr_erase "instance" "AlgebraicGeometry.OModulePresheaf.instSubsingletonObjZero AlgebraicGeometry.OModulePresheaf.Leray.relAltC_scalarTower AlgebraicGeometry.OModulePresheaf.Leray.ker_relAltd_modΓ AlgebraicGeometry.OModulePresheaf.Leray.relAltC_modΓ AlgebraicGeometry.OModulePresheaf.Leray.biC_abGrp AlgebraicGeometry.OModulePresheaf.Leray.relAltH_modΓ AlgebraicGeometry.OModulePresheaf.Leray.ker_relAltd_smul AlgebraicGeometry.OModulePresheaf.Leray.relAltH_scalarTower AlgebraicGeometry.OModulePresheaf.Leray.relAltH_smul AlgebraicGeometry.OModulePresheaf.Leray.biC_module AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instDecidableEqIdx AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instFintype AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instLinearOrder AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instFintypeIdx DoubleComplex.instModuleE₂I DoubleComplex.Bounded.modR DoubleComplex.instModuleE₂II DoubleComplex.instAddCommGroupE₂II DoubleComplex.Bounded.abGrp DoubleComplex.instAddCommGroupE₂I ProjSpaceCech.GradedModule.H.module ProjSpaceCech.GradedModule.H.addCommGroup ProjSpaceCech.GradedModule.sec.instAdd ProjSpaceCech.GradedModule.sec.instNeg ProjSpaceCech.GradedModule.acg ProjSpaceCech.GradedModule.Frac.setoid ProjSpaceCech.GradedModule.modR ProjSpaceCech.GradedModule.sec.instModule ProjSpaceCech.GradedModule.sec.instAddCommGroup ProjSpaceCech.GradedModule.sec.instZero ProjSpaceCech.GradedModule.Presentation.fJ ProjSpaceCech.GradedModule.sec.instSMul ProjSpaceCech.Twist.H.module ProjSpaceCech.Idx.instFintype ProjSpaceCech.Twist.H.addCommGroup ProjSpaceCech.Idx.instDecidableEq ProjSpaceCech.Twist.Mon.instDecidableEq ProjSpaceCech.Twist.cochain.instAddCommGroup ProjSpaceCech.Twist.cochain.instModule instTopologicallyFGOfFiniteType"
p2m_attr_erase "instance" "AlgebraicCurve.CurveModel.isProper AlgebraicCurve.CurveModel.isIntegral AlgebraicCurve.CurveModel.smooth AlgebraicCurve.Place.instIsScalarTowerSubtypeMemValuationSubringToValuationSubring AlgebraicCurve.Divisor.instDistribMulActionAlgEquiv AlgebraicCurve.Place.instSMulAlgEquiv AlgebraicCurve.Place.instIsPrincipalIdealRingSubtypeMemValuationSubringToValuationSubring AlgebraicCurve.Place.instIsDiscreteValuationRingSubtypeMemValuationSubringToValuationSubring AlgebraicCurve.Pic0.instDistribMulActionAlgEquiv AlgebraicCurve.Place.instAlgebraSubtypeMemValuationSubringToValuationSubring AlgebraicCurve.Place.instMulActionAlgEquiv AlgebraicCurve.Pic0.instSMulAlgEquiv AlgebraicCurve.CurveModel.locallyOfFiniteType_gluedToBase AlgebraicCurve.CurveModel.isFractionRing_overlap AlgebraicCurve.CurveModel.isLocallyNoetherian_glued AlgebraicCurve.CurveModel.jacobsonSpace_glued AlgebraicCurve.CurveModel.isOpenImmersion_ι₀ AlgebraicCurve.CurveModel.isIntegral_glued AlgebraicCurve.CurveModel.quasiSeparated_gluedToBase AlgebraicCurve.CurveModel.compactSpace_glued AlgebraicCurve.CurveModel.isIntegral_adjoin_chartRing AlgebraicCurve.CurveModel.isFractionRing_overlap_functionField AlgebraicCurve.CurveModel.isProper_gluedToBase AlgebraicCurve.CurveModel.isOpenImmersion_ιU AlgebraicCurve.CurveModel.isOpenImmersion_f₀ AlgebraicCurve.CurveModel.isOpenImmersion_fInf AlgebraicCurve.CurveModel.isOpenImmersion_ιInf AlgebraicCurve.CurveModel.algebra_overlap_functionField AlgebraicCurve.CurveModel.quasiCompact_gluedToBase AlgebraicCurve.CurveModel.algebraAdjoin AlgebraicCurve.CurveModel.isDedekindDomain_chartRing AlgebraicCurve.CurveModel.isIntegralClosure AlgebraicCurve.CurveModel.finite_chartRing AlgebraicCurve.CurveModel.centre_isPrime AlgebraicCurve.CurveModel.isFractionRing_chartRing AlgebraicCurve.CurveModel.finiteType_chartRing AlgebraicCurve.CurveModel.isNoetherianRing_chartRing AlgebraicCurve.CurveModel.isScalarTower_base_adjoin AlgebraicCurve.CurveModel.isScalarTower_adjoin AlgebraicCurve.CurveModel.chartRing_finitePresentation"
p2m_attr_erase "instance" "AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation AlgebraicGeometry.SubalgebraStages.compactSpace_pullback AlgebraicGeometry.SubalgebraStages.quasiSeparatedSpace_pullback AlgebraicGeometry.SubalgebraStages.compactSpace_obj AlgebraicGeometry.SubalgebraStages.quasiSeparatedSpace_obj AlgebraicGeometry.SubalgebraStages.quasiCompact_snd AlgebraicGeometry.SubalgebraStages.isAffineHom_leg AlgebraicGeometry.SubalgebraStages.isAffineHom_trans AlgebraicGeometry.SubalgebraStages.isAffineHom_diagram_map AlgebraicGeometry.SubalgebraStages.quasiSeparated_snd AlgebraicGeometry.SubalgebraStages.isCofiltered_op IsDirectLimit.Module.instDirectLimitCoeLinearMapIdOfOfNonempty AdicCompletion.instIsLocalRingMaximalIdeal"
p2m_attr_erase "simp" "AlgebraicGeometry.tilde.functorCompPullbackSpecIso_app AlgebraicGeometry.OModulePresheaf.prod_obj AlgebraicGeometry.OModulePresheaf.restrOpen_obj AlgebraicGeometry.OModulePresheaf.DevissageStep.mk.injEq AlgebraicGeometry.OModulePresheaf.pushforward_obj AlgebraicGeometry.OModulePresheaf.im_obj AlgebraicGeometry.OModulePresheaf.pow_obj AlgebraicGeometry.OModulePresheaf.fstHom_app AlgebraicGeometry.OModulePresheaf.ker_obj AlgebraicGeometry.OModulePresheaf.coker_obj AlgebraicGeometry.OModulePresheaf.DevissageStep.mk.sizeOf_spec AlgebraicGeometry.Scheme.OrderedAffineCover.preimage_U AlgebraicGeometry.OModulePresheaf.sndHom_app AlgebraicGeometry.OModulePresheaf.Hom.mk.injEq AlgebraicGeometry.OModulePresheaf.Hom.id_app AlgebraicGeometry.OModulePresheaf.AffHom.appSections_apply AlgebraicGeometry.OModulePresheaf.AffHom.comp_app AlgebraicGeometry.OModulePresheaf.AffSES.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.AffHom.kerMap_coe AlgebraicGeometry.OModulePresheaf.AffHom.id_app AlgebraicGeometry.OModulePresheaf.Hom.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.Hom.toAffHom_app AlgebraicGeometry.OModulePresheaf.SES.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.AffHom.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.Hom.comp_app AlgebraicGeometry.OModulePresheaf.SES.mk.injEq AlgebraicGeometry.OModulePresheaf.AffHom.mk.injEq AlgebraicGeometry.OModulePresheaf.Hom.appSections_apply AlgebraicGeometry.OModulePresheaf.AffSES.mk.injEq AlgebraicGeometry.OModulePresheaf.Leray.restrictToPreimage_U AlgebraicGeometry.Scheme.OrderedAffineCover.toCoverOf_U AlgebraicGeometry.Scheme.OrderedAffineCoverOf.mk.sizeOf_spec AlgebraicGeometry.Scheme.OrderedAffineCoverOf.mk.injEq AlgebraicGeometry.Scheme.OrderedAffineCover.restrict_U DoubleComplex.Bounded.mk.injEq DoubleComplex.Bounded.mk.sizeOf_spec DoubleComplex.Convergence.mk.injEq DoubleComplex.Convergence.mk.sizeOf_spec DoubleComplex.SubQuot.mk.sizeOf_spec DoubleComplex.SubQuot.mk.injEq"
p2m_attr_erase "simp" "ProjSpaceCech.GradedModule.mk.injEq ProjSpaceCech.GradedModule.mk.sizeOf_spec ProjSpaceCech.GradedModule.Frac.mk.sizeOf_spec ProjSpaceCech.GradedModule.Presentation.mk.injEq ProjSpaceCech.GradedModule.Frac.mk.injEq ProjSpaceCech.GradedModule.Presentation.mk.sizeOf_spec ProjSpaceCech.GradedModule.Hom.shift_toLinearMap ProjSpaceCech.GradedModule.Hom.mk.sizeOf_spec ProjSpaceCech.GradedModule.Hom.mk.injEq AlgebraicGeometry.Scheme.Modules.tensorSections_zero_right AlgebraicGeometry.Scheme.Modules.map_unitSection AlgebraicGeometry.Scheme.Modules.tensorSectionsBilin_apply AlgebraicGeometry.Scheme.Modules.tensorPowSection_zero AlgebraicGeometry.Scheme.Modules.tensorSections_zero_left RegularLocalRingQuotientAscent.dualNumberFst_apply GoodReductionJacobian.RelativeGroupLaw.baseChangePointToBase_ofBase GoodReductionJacobian.RelativeGroupLaw.baseChangePointToBase_coe GoodReductionJacobian.RelativeGroupLaw.baseChangePointOfBase_coe GoodReductionJacobian.RelativeGroupLaw.baseChange_inv GoodReductionJacobian.RelativeGroupLaw.baseChangePointOfBase_toBase GoodReductionJacobian.RelativeGroupLaw.baseChange_mul GoodReductionJacobian.RelativeGroupLaw.baseChange_one NeronSpecialFibreInfra.specialFibreRestrict_coe_comp_fst NeronSpecialFibreInfra.fibreRestrictAlong_coe_comp_snd NeronSpecialFibreInfra.fibreRestrictAlong_coe_comp_fst NeronSpecialFibreInfra.neronEndRestrictEquiv_apply NeronSpecialFibreInfra.fibreRestrictAlong_coe_comp_fst_assoc NeronSpecialFibreInfra.specialFibreRestrict_coe_comp_snd NeronSpecialFibreInfra.neronEndExtension_genericFibreRestrict NeronSpecialFibreInfra.specClosedFibreInclusion_eq NeronSpecialFibreInfra.specialFibreRestrict_coe_comp_fst_assoc NeronSpecialFibreInfra.specialFibreRestrict_coe_comp_snd_assoc NeronSpecialFibreInfra.genericFibreRestrict_neronEndExtension NeronSpecialFibreInfra.homOverId_coe NeronSpecialFibreInfra.homOverComp_coe NeronSpecialFibreInfra.fibreRestrictAlong_coe_comp_snd_assoc GoodReductionJacobian.RelativeGroupLaw.fibre_inv GoodReductionJacobian.RelativeGroupLaw.fibrePointToBase_coe GoodReductionJacobian.RelativeGroupLaw.fibrePointOfBase_toBase GoodReductionJacobian.RelativeGroupLaw.fibre_mul"
p2m_attr_erase "simp" "GoodReductionJacobian.RelativeGroupLaw.fibrePointToBase_ofBase GoodReductionJacobian.RelativeGroupLaw.fibre_one GoodReductionJacobian.RelativeGroupLaw.fibrePointOfBase_coe AlgebraicGeometry.schemeFibreEndo_snd AlgebraicGeometry.schemeFibreEndo_fst AlgebraicCurve.CurveModel.mk.injEq AlgebraicCurve.CurveModel.mk.sizeOf_spec AlgebraicCurve.Place.mk.injEq AlgebraicCurve.Divisor.degree_single AlgebraicCurve.Divisor.smul_single AlgebraicCurve.Place.smul_toValuationSubring AlgebraicCurve.Place.heightOneSpectrum_asIdeal AlgebraicCurve.Place.coe_algebraMap AlgebraicCurve.Place.ord_one AlgebraicCurve.Place.coe_smulRingEquiv_apply AlgebraicCurve.Pic0.coe_degZeroSMulHom AlgebraicCurve.Place.deg_smul AlgebraicCurve.Pic0.mk_zero AlgebraicCurve.Place.mk.sizeOf_spec AlgebraicCurve.Divisor.degree_smul AlgebraicCurve.Pic0.mk_add AlgebraicCurve.Place.ord_zero AlgebraicCurve.Place.ofHeightOneSpectrum_toValuationSubring AlgebraicCurve.CurveModel.coe_gInf AlgebraicCurve.CurveModel.coe_tInvChart AlgebraicCurve.CurveModel.ιInf_gluedToBase_assoc AlgebraicCurve.CurveModel.ιInf_gluedToBase AlgebraicCurve.CurveModel.primeOfι₀_asIdeal AlgebraicCurve.CurveModel.coe_tChart AlgebraicCurve.CurveModel.ι₀_gluedToBase_assoc AlgebraicCurve.CurveModel.primeOfιInf_asIdeal AlgebraicCurve.CurveModel.ι₀_gluedToBase AlgebraicCurve.CurveModel.coe_tma AlgebraicCurve.CurveModel.coe_primeEquivChartPlaces AlgebraicCurve.Place.congrEquiv_symm_apply AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply AlgebraicCurve.RationalFunctionField.deg_placeOfPoint"
p2m_attr_erase "simp" "AlgebraicGeometry.SubalgebraStages.specCone_π_app AlgebraicGeometry.SubalgebraStages.specLeg_specHom AlgebraicGeometry.SubalgebraStages.specLeg_specTrans AlgebraicGeometry.SubalgebraStages.cone_pt AlgebraicGeometry.SubalgebraStages.trans_fst AlgebraicGeometry.SubalgebraStages.diagram_obj AlgebraicGeometry.SubalgebraStages.leg_snd AlgebraicGeometry.SubalgebraStages.diagram_map AlgebraicGeometry.SubalgebraStages.specTrans_refl AlgebraicGeometry.SubalgebraStages.trans_snd AlgebraicGeometry.SubalgebraStages.specTrans_specHom AlgebraicGeometry.SubalgebraStages.specCone_pt AlgebraicGeometry.SubalgebraStages.cone_π_app AlgebraicGeometry.SubalgebraStages.specDiagram_map AlgebraicGeometry.SubalgebraStages.specDiagram_obj AlgebraicGeometry.SubalgebraStages.leg_fst AlgebraicGeometry.SubalgebraStages.leg_trans IsDirectLimit.Module.linearEquiv_symm_apply IsDirectLimit.linearEquiv_symm_apply IsDirectLimit.lift_of IsDirectLimit.Module.linearEquiv_apply IsDirectLimit.Module.lift_of IsDirectLimit.Equiv_apply"

set_option autoImplicit false

p2m_open "CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory AlgebraicGeometry AlgebraicGeometry.RelPicard NeronModelInfra GoodReductionJacobian AlgebraicGeometry.Polarisation"

namespace SeesawSplit

variable {k : Type} [Field k] [IsAlgClosed k] {A : Scheme.{0}} (f : A ⟶ Spec (CommRingCat.of k))
  (L : RelativeGroupLaw k f)

noncomputable def shuffleIso {X : Scheme.{0}} (A B C D : X.Modules) :
    (A ⊗ B) ⊗ (C ⊗ D) ≅ (A ⊗ C) ⊗ (B ⊗ D) :=
  α_ A B (C ⊗ D) ≪≫ whiskerLeftIso A ((α_ B C D).symm ≪≫ whiskerRightIso (β_ B C) D ≪≫ α_ C B D) ≪≫
    (α_ A C (B ⊗ D)).symm

theorem nonempty_dual_tensor_iso_unit {X : Scheme.{0}} {P : X.Modules} (hP : Scheme.Modules.IsInvertible P) :
    Nonempty (Scheme.Modules.dual P ⊗ P ≅ 𝟙_ X.Modules) := by
  obtain ⟨u⟩ := hP.dual_monoidalV2.2
  exact ⟨β_ _ _ ≪≫ u⟩

theorem nonempty_iso_tensor_of_tensor_duals_iso_unit {X : Scheme.{0}} {M P Q : X.Modules}
    (hP : Scheme.Modules.IsInvertible P) (hQ : Scheme.Modules.IsInvertible Q)
    (e : M ⊗ (Scheme.Modules.dual P ⊗ Scheme.Modules.dual Q) ≅ 𝟙_ X.Modules) : Nonempty (M ≅ P ⊗ Q) := by
  obtain ⟨uP⟩ := nonempty_dual_tensor_iso_unit hP
  obtain ⟨uQ⟩ := nonempty_dual_tensor_iso_unit hQ
  let D := Scheme.Modules.dual P ⊗ Scheme.Modules.dual Q
  have c : D ⊗ (P ⊗ Q) ≅ 𝟙_ X.Modules := shuffleIso _ _ P Q ≪≫ tensorIso uP uQ ≪≫ λ_ _
  exact ⟨(ρ_ M).symm ≪≫ whiskerLeftIso M c.symm ≪≫ (α_ M D (P ⊗ Q)).symm ≪≫ whiskerRightIso e (P ⊗ Q) ≪≫ λ_ _⟩

theorem isInvertible_mumfordBundle {𝓛 : A.Modules} (h𝓛 : Scheme.Modules.IsInvertible 𝓛) :
    Scheme.Modules.IsInvertible (mumfordBundle f L 𝓛) :=
  (h𝓛.pullback _).tensor_monoidalV2 ((h𝓛.dual_monoidalV2.1.pullback _).tensor_monoidalV2 (h𝓛.dual_monoidalV2.1.pullback _))

theorem baseChangeSnd_comp_sliceAt {Y : Scheme.{0}} (fY : Y ⟶ Spec (CommRingCat.of k)) (j : Y ⟶ A) (hjf : j ≫ f = fY)
    (τ : SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) fY) :
    baseChangeSnd f τ ≫ sliceAt f (⟨j, hjf⟩ : SchemeHomOver fY f) =
      sliceAt f (⟨τ.1 ≫ j, by rw [Category.assoc, hjf, τ.2]⟩ : SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) f) := by
  unfold baseChangeSnd sliceAt
  apply pullback.hom_ext
  · simp only [Category.assoc, pullback.lift_fst, pullback.lift_fst_assoc, Category.comp_id]
  · simp only [Category.assoc, pullback.lift_snd, pullback.lift_snd_assoc]

theorem lift_id_comp_sliceAt (ε : SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) f) :
    pullback.lift (𝟙 A) f (by rw [Category.id_comp, Category.comp_id]) ≫ sliceAt f ε =
      pullback.lift (𝟙 A) (f ≫ ε.1) (by rw [Category.id_comp, Category.assoc, ε.2, Category.comp_id]) := by
  unfold sliceAt
  apply pullback.hom_ext
  · simp only [Category.assoc, pullback.lift_fst]
  · simp only [Category.assoc, pullback.lift_snd, pullback.lift_snd_assoc]

theorem lift_comp_symmetry (ε : SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) f) :
    pullback.lift (𝟙 A) (f ≫ ε.1) (by rw [Category.id_comp, Category.assoc, ε.2, Category.comp_id]) ≫ (pullbackSymmetry f f).hom =
      pullback.lift (f ≫ ε.1) (𝟙 A) (by rw [Category.id_comp, Category.assoc, ε.2, Category.comp_id]) := by
  apply pullback.hom_ext
  · simp only [Category.assoc, pullbackSymmetry_hom_comp_fst, pullback.lift_snd, pullback.lift_fst]
  · simp only [Category.assoc, pullbackSymmetry_hom_comp_snd, pullback.lift_fst, pullback.lift_snd]

theorem rigSection_comp_sliceAt {Y : Scheme.{0}} (fY : Y ⟶ Spec (CommRingCat.of k)) (j : Y ⟶ A) (hjf : j ≫ f = fY)
    (ε : SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) f) :
    rigSection f fY ε ≫ sliceAt f (⟨j, hjf⟩ : SchemeHomOver fY f) =
      j ≫ pullback.lift (f ≫ ε.1) (𝟙 A) (by rw [Category.id_comp, Category.assoc, ε.2, Category.comp_id]) := by
  unfold rigSection sliceAt
  apply pullback.hom_ext
  · simp only [Category.assoc, pullback.lift_fst, pullback.lift_fst_assoc]
    rw [← Category.assoc, hjf]
  · simp only [Category.assoc, pullback.lift_snd, pullback.lift_snd_assoc, Category.id_comp, Category.comp_id]

end SeesawSplit

open SeesawSplit in
theorem solution
    (k : Type) [Field k] [IsAlgClosed k] {A : Scheme.{0}} (f : A ⟶ Spec (CommRingCat.of k))
    (L : RelativeGroupLaw k f) (hA : AbelianSchemePropertyBundle k f)
    {Y : Scheme.{0}} (fY : Y ⟶ Spec (CommRingCat.of k)) (j : Y ⟶ A) [IsClosedImmersion j] (hjf : j ≫ f = fY)
    (hY : AbelianSchemePropertyBundle k fY)
    (𝓛 : A.Modules) (h𝓛 : Scheme.Modules.IsInvertible 𝓛)
    (hstab : ∀ y : SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) fY,
      (⟨y.1 ≫ j, by rw [Category.assoc, hjf, y.2]⟩ : SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) f) ∈ kernelPts f L 𝓛) :
    Nonempty ((Scheme.Modules.pullback (sliceAt f (⟨j, hjf⟩ : SchemeHomOver fY f) ≫ addMor f L)).obj 𝓛 ≅
      (Scheme.Modules.pullback (pullback.fst f fY)).obj 𝓛 ⊗
        (Scheme.Modules.pullback (pullback.snd f fY)).obj ((Scheme.Modules.pullback j).obj 𝓛)) := by
  have hc : L.IsCommutative := hA.isCommutative L
  haveI : IsProper f := hA.proper
  haveI : Smooth fY := hY.smooth
  haveI : GeometricallyIntegral f := hA.geometricallyIntegral
  haveI : Nonempty ↥A := ⟨(L.one (𝟙 _)).1.base (IsLocalRing.closedPoint k)⟩
  haveI : IsIntegral A := GeometricallyIntegral.isIntegral_of_subsingleton f
  haveI : GeometricallyIntegral fY := hY.geometricallyIntegral
  haveI : Nonempty ↥Y := ⟨((hY.hasGroupLaw.some).one (𝟙 _)).1.base (IsLocalRing.closedPoint k)⟩
  haveI : IsIntegral Y := GeometricallyIntegral.isIntegral_of_subsingleton fY

  let s : pullback f fY ⟶ pullback f f := sliceAt f (⟨j, hjf⟩ : SchemeHomOver fY f)
  let Λ := mumfordBundle f L 𝓛
  let N := (Scheme.Modules.pullback s).obj Λ
  have hΛ : Scheme.Modules.IsInvertible Λ := isInvertible_mumfordBundle f L h𝓛
  have hN : Scheme.Modules.IsInvertible N := hΛ.pullback s
  let ε : SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) f := L.one (𝟙 _)

  have hε : ε ∈ kernelPts f L 𝓛 := L.isInStabilizer_one 𝓛 (𝟙 _)
  obtain ⟨e₁⟩ := (mem_kernelPts_iff_nonempty_pullback_sliceAt_mumfordBundle_iso_unit k f L 𝓛 h𝓛 ε).mp hε
  obtain ⟨esym⟩ := nonempty_pullback_pullbackSymmetry_mumfordBundle_iso k f L hc 𝓛
  have e₂ : (Scheme.Modules.pullback (pullback.lift (f ≫ ε.1) (𝟙 A)
      (by rw [Category.id_comp, Category.assoc, ε.2, Category.comp_id]))).obj Λ ≅ 𝟙_ A.Modules := by
    refine (Scheme.Modules.pullbackCongr (lift_comp_symmetry f ε).symm).app Λ ≪≫
      ((Scheme.Modules.pullbackComp _ _).app Λ).symm ≪≫
      (Scheme.Modules.pullback _).mapIso esym ≪≫
      (Scheme.Modules.pullbackCongr (lift_id_comp_sliceAt f ε).symm).app Λ ≪≫
      ((Scheme.Modules.pullbackComp _ _).app Λ).symm ≪≫
      (Scheme.Modules.pullback _).mapIso e₁ ≪≫ Scheme.Modules.pullbackTensorUnitObjIso _

  let M : RigidifiedLineBundle f ε fY :=
    { L := N
      isInvertible := hN
      rigidified := ⟨(Scheme.Modules.pullbackComp _ _).app Λ ≪≫
        (Scheme.Modules.pullbackCongr (rigSection_comp_sliceAt f fY j hjf ε)).app Λ ≪≫
        ((Scheme.Modules.pullbackComp _ _).app Λ).symm ≪≫ (Scheme.Modules.pullback j).mapIso e₂ ≪≫
        Scheme.Modules.pullbackTensorUnitObjIso j⟩ }

  have hM : ∀ τ : SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) fY,
      Nonempty ((M.pullbackAlong τ).L ≅ SheafOfModules.unit (Limits.pullback f (𝟙 (Spec (CommRingCat.of k)))).ringCatSheaf) := by
    intro τ
    obtain ⟨eτ⟩ := (mem_kernelPts_iff_nonempty_pullback_sliceAt_mumfordBundle_iso_unit k f L 𝓛 h𝓛 _).mp (hstab τ)
    exact ⟨(Scheme.Modules.pullbackComp _ _).app Λ ≪≫
      (Scheme.Modules.pullbackCongr (baseChangeSnd_comp_sliceAt f fY j hjf τ)).app Λ ≪≫ eτ⟩

  obtain ⟨eN⟩ := RigidifiedLineBundle.nonempty_iso_unit_of_forall_pullbackAlong_point k f ε fY M hM

  have hs1 : s ≫ pullback.fst f f = pullback.fst f fY := pullback.lift_fst _ _ _
  have hs2 : s ≫ pullback.snd f f = pullback.snd f fY ≫ j := pullback.lift_snd _ _ _
  obtain ⟨d1⟩ := h𝓛.pullback_dual_monoidalV2 (pullback.fst f fY)
  obtain ⟨d2⟩ := h𝓛.pullback_dual_monoidalV2 (pullback.snd f fY ≫ j)
  let P := (Scheme.Modules.pullback (pullback.fst f fY)).obj 𝓛
  let Q' := (Scheme.Modules.pullback (pullback.snd f fY ≫ j)).obj 𝓛
  have hP : Scheme.Modules.IsInvertible P := h𝓛.pullback _
  have hQ' : Scheme.Modules.IsInvertible Q' := h𝓛.pullback _
  have e0 : N ≅ (Scheme.Modules.pullback (s ≫ addMor f L)).obj 𝓛 ⊗ (Scheme.Modules.dual P ⊗ Scheme.Modules.dual Q') :=
    Scheme.Modules.pullbackTensorObjIso s _ _ ≪≫
      tensorIso ((Scheme.Modules.pullbackComp s (addMor f L)).app 𝓛)
        (Scheme.Modules.pullbackTensorObjIso s _ _ ≪≫
          tensorIso
            ((Scheme.Modules.pullbackComp s (pullback.fst f f)).app _ ≪≫
              (Scheme.Modules.pullbackCongr hs1).app _ ≪≫ d1)
            ((Scheme.Modules.pullbackComp s (pullback.snd f f)).app _ ≪≫
              (Scheme.Modules.pullbackCongr hs2).app _ ≪≫ d2))
  obtain ⟨e1⟩ := nonempty_iso_tensor_of_tensor_duals_iso_unit hP hQ' (e0.symm ≪≫ eN)
  exact ⟨e1 ≪≫ whiskerLeftIso P ((Scheme.Modules.pullbackComp (pullback.snd f fY) j).app 𝓛).symm⟩

end S_AlgebraicGeometry_Polarisation_nonempty_pullback_sliceAt_addMor_iso_tensor_of_forall_comp_mem_kernelPts
end P2MW
export P2MW.S_AlgebraicGeometry_Polarisation_nonempty_pullback_sliceAt_addMor_iso_tensor_of_forall_comp_mem_kernelPts (solution)
