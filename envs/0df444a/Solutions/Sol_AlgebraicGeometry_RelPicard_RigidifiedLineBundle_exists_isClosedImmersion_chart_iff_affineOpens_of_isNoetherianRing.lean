-- Prove2me | solution 1 for AlgebraicGeometry.RelPicard.RigidifiedLineBundle.exists_isClosedImmersion_chart_iff_affineOpens_of_isNoetherianRing
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:03.589526+00:00
-- url     : https://prove2.me/submissions/9bd76f2d-c59d-5f60-9c12-afc21e95ecff

import Mathlib
import Definitions.Def_JacJ1Iface
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import Definitions.Def_AlgebraicGeometry_RepresentsRelSubPic
import Definitions.Def_AlgebraicGeometry_RelPicardAlgEquivZeroCut
import Definitions.Def_AlgebraicGeometry_PolarisationRosati
import Definitions.Def_GoodReductionJacobian_RelativeGroupLawTranslate
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_IsInvertible_exists_isClosedImmersion_forall_iff_locallyIsoOver_of_flat_of_isProper
import Theorems.Thm_GoodReductionJacobian_AbelianSchemePropertyBundle_bijective_specIso_inv_comp_appTop_of_isPullback
import Theorems.Thm_GoodReductionJacobian_AbelianSchemePropertyBundle_geometricallyIntegral_of_commRing
import Theorems.Thm_AlgebraicGeometry_RelPicard_RigidifiedLineBundle_nonempty_iso_unit_iff_forall_openCover
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_RelPicard_RigidifiedLineBundle_exists_isClosedImmersion_chart_iff_affineOpens_of_isNoetherianRing
p2m_attr_erase "instance" "PresheafOfModules.PullbackMonoidal.pullback_monoidal PresheafOfModules.PullbackMonoidal.isIso_δ PresheafOfModules.pushforward_laxMonoidal PresheafOfModules.PullbackMonoidal.isIso_η PresheafOfModules.free_monoidal PresheafOfModules.restrictScalars_laxMonoidal PresheafOfModules.PullbackMonoidal.isIso_δ_gS PresheafOfModules.pullback_oplaxMonoidal PresheafOfModules.PullbackMonoidal.instPreservesColimitsOfSizeCompOppositeCommRingCatRingCatForget₂RingHomCarrierCarrierPb PresheafOfModules.pullback_monoidal' AlgebraicGeometry.Scheme.Modules.preservesBinaryProducts_opensMap AlgebraicGeometry.Scheme.Modules.pullback_monoidal AlgebraicGeometry.Scheme.Modules.sheafify_isLocalization' AlgebraicGeometry.Scheme.Modules.preservesTerminal_opensMap AlgebraicGeometry.Scheme.Modules.pullback₀_monoidal AlgebraicGeometry.Scheme.Modules.preservesFiniteProducts_opensMap AlgebraicGeometry.Scheme.Modules.instLiftingPresheafOfModulesSheafifyPresheafWOpensCarrierCarrierCommRingCatGrothendieckTopologyObjFunctorOppositeIsSheafSheafCompPullback₀Pullback TwoChartCech.Sections.M0_moduleA TwoChartCech.Sections.M1_module TwoChartCech.Cover.A01_algebra TwoChartCech.Cover.A0_algebra TwoChartCech.Cover.A1_commRing TwoChartCech.Cover.A1_algebra TwoChartCech.Sections.M01_module TwoChartCech.Sections.M0_addCommGroup TwoChartCech.Sections.M0_tower TwoChartCech.Sections.M01_addCommGroup TwoChartCech.Cover.A0_commRing TwoChartCech.Sections.M1_tower TwoChartCech.Sections.M01_moduleA TwoChartCech.Sections.M0_module TwoChartCech.Sections.M1_moduleA TwoChartCech.Sections.M1_addCommGroup TwoChartCech.Cover.A01_commRing TwoChartCech.Sections.M01_tower CoherentBaseChange.TwoTermComplex.C0_module CoherentBaseChange.TwoTermComplex.C0_addCommGroup CoherentBaseChange.TwoTermComplex.C1_module CoherentBaseChange.TwoTermComplex.C1_addCommGroup CoherentBaseChange.TwoTermComplex.C0_free"
p2m_attr_erase "instance" "CoherentBaseChange.TwoTermComplex.C1_finite CoherentBaseChange.TwoTermComplex.C0_finite CoherentBaseChange.TwoTermComplex.C1_free AlgebraicGeometry.OModulePresheaf.isScalarTower AlgebraicGeometry.Scheme.OrderedAffineCover.instLinearOrder AlgebraicGeometry.OModulePresheaf.module AlgebraicGeometry.Scheme.OrderedAffineCover.instFintype AlgebraicGeometry.Scheme.OrderedAffineCover.instFintypeIdx AlgebraicGeometry.OModulePresheaf.addCommGroup AlgebraicGeometry.Scheme.OrderedAffineCover.instDecidableEqIdx AlgebraicGeometry.OModulePresheaf.moduleSections AlgebraicGeometry.OModulePresheaf.instSubsingletonObjZero AlgebraicGeometry.OModulePresheaf.Leray.relAltC_scalarTower AlgebraicGeometry.OModulePresheaf.Leray.ker_relAltd_modΓ AlgebraicGeometry.OModulePresheaf.Leray.relAltC_modΓ AlgebraicGeometry.OModulePresheaf.Leray.biC_abGrp AlgebraicGeometry.OModulePresheaf.Leray.relAltH_modΓ AlgebraicGeometry.OModulePresheaf.Leray.ker_relAltd_smul AlgebraicGeometry.OModulePresheaf.Leray.relAltH_scalarTower AlgebraicGeometry.OModulePresheaf.Leray.relAltH_smul AlgebraicGeometry.OModulePresheaf.Leray.biC_module AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instDecidableEqIdx AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instFintype AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instLinearOrder AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instFintypeIdx DoubleComplex.instModuleE₂I DoubleComplex.Bounded.modR DoubleComplex.instModuleE₂II DoubleComplex.instAddCommGroupE₂II DoubleComplex.Bounded.abGrp DoubleComplex.instAddCommGroupE₂I ProjSpaceCech.GradedModule.H.module ProjSpaceCech.GradedModule.H.addCommGroup ProjSpaceCech.GradedModule.sec.instAdd ProjSpaceCech.GradedModule.sec.instNeg ProjSpaceCech.GradedModule.acg ProjSpaceCech.GradedModule.Frac.setoid ProjSpaceCech.GradedModule.modR ProjSpaceCech.GradedModule.sec.instModule ProjSpaceCech.GradedModule.sec.instAddCommGroup"
p2m_attr_erase "instance" "ProjSpaceCech.GradedModule.sec.instZero ProjSpaceCech.GradedModule.Presentation.fJ ProjSpaceCech.GradedModule.sec.instSMul ProjSpaceCech.Twist.H.module ProjSpaceCech.Idx.instFintype ProjSpaceCech.Twist.H.addCommGroup ProjSpaceCech.Idx.instDecidableEq ProjSpaceCech.Twist.Mon.instDecidableEq ProjSpaceCech.Twist.cochain.instAddCommGroup ProjSpaceCech.Twist.cochain.instModule AlgebraicGeometry.SubalgebraStages.compactSpace_pullback AlgebraicGeometry.SubalgebraStages.quasiSeparatedSpace_pullback AlgebraicGeometry.SubalgebraStages.compactSpace_obj AlgebraicGeometry.SubalgebraStages.quasiSeparatedSpace_obj AlgebraicGeometry.SubalgebraStages.quasiCompact_snd AlgebraicGeometry.SubalgebraStages.isAffineHom_leg AlgebraicGeometry.SubalgebraStages.isAffineHom_trans AlgebraicGeometry.SubalgebraStages.isAffineHom_diagram_map AlgebraicGeometry.SubalgebraStages.quasiSeparated_snd AlgebraicGeometry.SubalgebraStages.isCofiltered_op IsDirectLimit.Module.instDirectLimitCoeLinearMapIdOfOfNonempty AdicCompletion.instIsLocalRingMaximalIdeal"
p2m_attr_erase "simp" "PresheafOfModules.freeεIso_hom_app PresheafOfModules.freeμIso_hom_app AlgebraicGeometry.Scheme.TwoAffineOpenCover.mk.injEq AlgebraicGeometry.Scheme.TwoAffineOpenCover.mk.sizeOf_spec AlgebraicGeometry.Scheme.TwoAffineOpenCover.pullback_U1 AlgebraicGeometry.Scheme.TwoAffineOpenCover.pullback_U0 TwoChartCech.Sections.mk.injEq TwoChartCech.Cover.mk.injEq TwoChartCech.GrothendieckComplex.mk.injEq TwoChartCech.Sections.mk.sizeOf_spec TwoChartCech.Cover.mk.sizeOf_spec TwoChartCech.Cover.lineBundle_r0_apply TwoChartCech.GrothendieckComplex.mk.sizeOf_spec TwoChartCech.Cover.lineBundle_r1_apply CoherentBaseChange.TwoTermComplex.mk.sizeOf_spec CoherentBaseChange.TwoTermComplex.mk.injEq AlgebraicGeometry.Scheme.OrderedAffineCover.mk.injEq AlgebraicGeometry.OModulePresheaf.mk.sizeOf_spec AlgebraicGeometry.Scheme.OrderedAffineCover.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.mk.injEq AlgebraicGeometry.OModulePresheaf.prod_obj AlgebraicGeometry.OModulePresheaf.restrOpen_obj AlgebraicGeometry.OModulePresheaf.DevissageStep.mk.injEq AlgebraicGeometry.OModulePresheaf.pushforward_obj AlgebraicGeometry.OModulePresheaf.im_obj AlgebraicGeometry.OModulePresheaf.pow_obj AlgebraicGeometry.OModulePresheaf.fstHom_app AlgebraicGeometry.OModulePresheaf.ker_obj AlgebraicGeometry.OModulePresheaf.coker_obj AlgebraicGeometry.OModulePresheaf.DevissageStep.mk.sizeOf_spec AlgebraicGeometry.Scheme.OrderedAffineCover.preimage_U AlgebraicGeometry.OModulePresheaf.sndHom_app AlgebraicGeometry.OModulePresheaf.Hom.mk.injEq AlgebraicGeometry.OModulePresheaf.Hom.id_app AlgebraicGeometry.OModulePresheaf.AffHom.appSections_apply AlgebraicGeometry.OModulePresheaf.AffHom.comp_app AlgebraicGeometry.OModulePresheaf.AffSES.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.AffHom.kerMap_coe AlgebraicGeometry.OModulePresheaf.AffHom.id_app AlgebraicGeometry.OModulePresheaf.Hom.mk.sizeOf_spec"
p2m_attr_erase "simp" "AlgebraicGeometry.OModulePresheaf.Hom.toAffHom_app AlgebraicGeometry.OModulePresheaf.SES.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.AffHom.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.Hom.comp_app AlgebraicGeometry.OModulePresheaf.SES.mk.injEq AlgebraicGeometry.OModulePresheaf.AffHom.mk.injEq AlgebraicGeometry.OModulePresheaf.Hom.appSections_apply AlgebraicGeometry.OModulePresheaf.AffSES.mk.injEq AlgebraicGeometry.OModulePresheaf.Leray.restrictToPreimage_U AlgebraicGeometry.Scheme.OrderedAffineCover.toCoverOf_U AlgebraicGeometry.Scheme.OrderedAffineCoverOf.mk.sizeOf_spec AlgebraicGeometry.Scheme.OrderedAffineCoverOf.mk.injEq AlgebraicGeometry.Scheme.OrderedAffineCover.restrict_U DoubleComplex.Bounded.mk.injEq DoubleComplex.Bounded.mk.sizeOf_spec DoubleComplex.Convergence.mk.injEq DoubleComplex.Convergence.mk.sizeOf_spec DoubleComplex.SubQuot.mk.sizeOf_spec DoubleComplex.SubQuot.mk.injEq ProjSpaceCech.GradedModule.mk.injEq ProjSpaceCech.GradedModule.mk.sizeOf_spec ProjSpaceCech.GradedModule.Frac.mk.sizeOf_spec ProjSpaceCech.GradedModule.Presentation.mk.injEq ProjSpaceCech.GradedModule.Frac.mk.injEq ProjSpaceCech.GradedModule.Presentation.mk.sizeOf_spec ProjSpaceCech.GradedModule.Hom.shift_toLinearMap ProjSpaceCech.GradedModule.Hom.mk.sizeOf_spec ProjSpaceCech.GradedModule.Hom.mk.injEq AlgebraicGeometry.tilde.functorCompPullbackSpecIso_app AlgebraicGeometry.Scheme.Modules.tensorSections_zero_right AlgebraicGeometry.Scheme.Modules.map_unitSection AlgebraicGeometry.Scheme.Modules.tensorSectionsBilin_apply AlgebraicGeometry.Scheme.Modules.tensorPowSection_zero AlgebraicGeometry.Scheme.Modules.tensorSections_zero_left AlgebraicGeometry.Scheme.Modules.tensorPow_zero AlgebraicGeometry.Scheme.Modules.tensorPow_succ AlgebraicGeometry.SubalgebraStages.specCone_π_app AlgebraicGeometry.SubalgebraStages.specLeg_specHom AlgebraicGeometry.SubalgebraStages.specLeg_specTrans AlgebraicGeometry.SubalgebraStages.cone_pt"
p2m_attr_erase "simp" "AlgebraicGeometry.SubalgebraStages.trans_fst AlgebraicGeometry.SubalgebraStages.diagram_obj AlgebraicGeometry.SubalgebraStages.leg_snd AlgebraicGeometry.SubalgebraStages.diagram_map AlgebraicGeometry.SubalgebraStages.specTrans_refl AlgebraicGeometry.SubalgebraStages.trans_snd AlgebraicGeometry.SubalgebraStages.specTrans_specHom AlgebraicGeometry.SubalgebraStages.specCone_pt AlgebraicGeometry.SubalgebraStages.cone_π_app AlgebraicGeometry.SubalgebraStages.specDiagram_map AlgebraicGeometry.SubalgebraStages.specDiagram_obj AlgebraicGeometry.SubalgebraStages.leg_fst AlgebraicGeometry.SubalgebraStages.leg_trans IsDirectLimit.Module.linearEquiv_symm_apply IsDirectLimit.linearEquiv_symm_apply IsDirectLimit.lift_of IsDirectLimit.Module.linearEquiv_apply IsDirectLimit.Module.lift_of IsDirectLimit.Equiv_apply RegularLocalRingQuotientAscent.dualNumberFst_apply GoodReductionJacobian.RelativeGroupLaw.baseChangePointToBase_ofBase GoodReductionJacobian.RelativeGroupLaw.baseChangePointToBase_coe GoodReductionJacobian.RelativeGroupLaw.baseChangePointOfBase_coe GoodReductionJacobian.RelativeGroupLaw.baseChange_inv GoodReductionJacobian.RelativeGroupLaw.baseChangePointOfBase_toBase GoodReductionJacobian.RelativeGroupLaw.baseChange_mul GoodReductionJacobian.RelativeGroupLaw.baseChange_one NeronModelInfra.NeronModelPropertyBundle.endExtensionEquiv_symm_restrict NeronModelInfra.schemeHomOverComp_id_left NeronModelInfra.schemeHomOverComp_id_right NeronModelInfra.schemeHomOverId_coe NeronModelInfra.NeronModelPropertyBundle.endExtensionEquiv_apply NeronModelInfra.NeronModelPropertyBundle.restrict_endExtensionEquiv_symm NeronModelInfra.schemeHomOverComp_coe NeronSpecialFibreInfra.specialFibreRestrict_coe_comp_fst NeronSpecialFibreInfra.fibreRestrictAlong_coe_comp_snd NeronSpecialFibreInfra.fibreRestrictAlong_coe_comp_fst NeronSpecialFibreInfra.neronEndRestrictEquiv_apply NeronSpecialFibreInfra.fibreRestrictAlong_coe_comp_fst_assoc NeronSpecialFibreInfra.specialFibreRestrict_coe_comp_snd"
p2m_attr_erase "simp" "NeronSpecialFibreInfra.neronEndExtension_genericFibreRestrict NeronSpecialFibreInfra.specClosedFibreInclusion_eq NeronSpecialFibreInfra.specialFibreRestrict_coe_comp_fst_assoc NeronSpecialFibreInfra.specialFibreRestrict_coe_comp_snd_assoc NeronSpecialFibreInfra.genericFibreRestrict_neronEndExtension NeronSpecialFibreInfra.homOverId_coe NeronSpecialFibreInfra.homOverComp_coe NeronSpecialFibreInfra.fibreRestrictAlong_coe_comp_snd_assoc GoodReductionJacobian.RelativeGroupLaw.fibre_inv GoodReductionJacobian.RelativeGroupLaw.fibrePointToBase_coe GoodReductionJacobian.RelativeGroupLaw.fibrePointOfBase_toBase GoodReductionJacobian.RelativeGroupLaw.fibre_mul GoodReductionJacobian.RelativeGroupLaw.fibrePointToBase_ofBase GoodReductionJacobian.RelativeGroupLaw.fibre_one GoodReductionJacobian.RelativeGroupLaw.fibrePointOfBase_coe AlgebraicGeometry.schemeFibreEndo_snd AlgebraicGeometry.schemeFibreEndo_fst"

set_option autoImplicit false

p2m_open "CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory AlgebraicGeometry AlgebraicGeometry.RelPicard NeronModelInfra GoodReductionJacobian AlgebraicGeometry.Polarisation"

namespace DockHelpers

theorem hH0 {R : Type} [CommRing R] {A : Scheme.{0}} {f : A ⟶ Spec (CommRingCat.of R)}
    (hA : AbelianSchemePropertyBundle R f) (B : Type) [CommRing B] [Algebra R B] :
    Function.Bijective (Limits.pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap R B)))).appTop := by
  have hb := GoodReductionJacobian.AbelianSchemePropertyBundle.bijective_specIso_inv_comp_appTop_of_isPullback hA
    (algebraMap R B) (Limits.pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap R B))))
    (Limits.pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap R B)))) (IsPullback.of_hasPullback _ _)
  have hi : Function.Bijective (Scheme.ΓSpecIso (CommRingCat.of B)).inv.hom :=
    (Scheme.ΓSpecIso (CommRingCat.of B)).symm.commRingCatIsoToRingEquiv.bijective
  exact (Function.Bijective.of_comp_iff _ hi).mp hb

section Geometry

variable {R : Type} [CommRing R] {A : Scheme.{0}} {f : A ⟶ Spec (CommRingCat.of R)}
  (L : RelativeGroupLaw R f) (hA : AbelianSchemePropertyBundle R f)
  {X : Scheme.{0}} (g : X ⟶ Spec (CommRingCat.of R))
  (M : RigidifiedLineBundle f (L.one (𝟙 (Spec (CommRingCat.of R)))) g)
  (U : X.Opens)
  {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of R)) (ψU : T ⟶ (U : Scheme.{0})) (hψ : (ψU ≫ U.ι) ≫ g = t)

noncomputable def α : Limits.pullback (Limits.pullback.snd f (U.ι ≫ g)) ψU ⟶ Limits.pullback f t :=
  Limits.pullback.lift
    (Limits.pullback.fst (Limits.pullback.snd f (U.ι ≫ g)) ψU ≫ Limits.pullback.fst f (U.ι ≫ g))
    (Limits.pullback.snd (Limits.pullback.snd f (U.ι ≫ g)) ψU)
    (by rw [Category.assoc, Limits.pullback.condition, ← Category.assoc, Limits.pullback.condition, Category.assoc, ← hψ,
          Category.assoc])

theorem α_comp_baseChangeSnd :
    α g U t ψU hψ ≫ baseChangeSnd f (⟨ψU ≫ U.ι, hψ⟩ : SchemeHomOver t g) =
      Limits.pullback.fst (Limits.pullback.snd f (U.ι ≫ g)) ψU ≫ baseChangeSnd f (⟨U.ι, rfl⟩ : SchemeHomOver (U.ι ≫ g) g) := by
  unfold α baseChangeSnd
  apply Limits.pullback.hom_ext
  · simp only [Category.assoc, Limits.pullback.lift_fst, Category.comp_id]
  · simp only [Category.assoc, Limits.pullback.lift_snd, Limits.pullback.lift_snd_assoc, Limits.pullback.condition_assoc]

include hψ in

theorem iso_of_trivial
    (e : (M.pullbackAlong (⟨ψU ≫ U.ι, hψ⟩ : SchemeHomOver t g)).L ≅
      (RigidifiedLineBundle.unit (c := f) (ε := L.one (𝟙 (Spec (CommRingCat.of R)))) t).L) :
    Nonempty ((Scheme.Modules.pullback (Limits.pullback.fst (Limits.pullback.snd f (U.ι ≫ g)) ψU)).obj
        ((Scheme.Modules.pullback (baseChangeSnd f (⟨U.ι, rfl⟩ : SchemeHomOver (U.ι ≫ g) g))).obj M.L) ≅
      (Scheme.Modules.pullback (Limits.pullback.fst (Limits.pullback.snd f (U.ι ≫ g)) ψU)).obj
        (SheafOfModules.unit (Limits.pullback f (U.ι ≫ g)).ringCatSheaf)) :=
  ⟨(Scheme.Modules.pullbackComp _ _).app M.L ≪≫
    (Scheme.Modules.pullbackCongr (α_comp_baseChangeSnd g U t ψU hψ).symm).app M.L ≪≫
    ((Scheme.Modules.pullbackComp _ _).app M.L).symm ≪≫
    (Scheme.Modules.pullback (α g U t ψU hψ)).mapIso e ≪≫
    Scheme.Modules.pullbackUnitIso (α g U t ψU hψ) ≪≫
    (Scheme.Modules.pullbackUnitIso _).symm⟩

include hψ in

noncomputable def δ {T' : Scheme.{0}} (v : T' ⟶ T) :
    Limits.pullback f (v ≫ t) ⟶ Limits.pullback (Limits.pullback.snd f (U.ι ≫ g)) ψU :=
  Limits.pullback.lift
    (Limits.pullback.lift (Limits.pullback.fst f (v ≫ t)) (Limits.pullback.snd f (v ≫ t) ≫ v ≫ ψU)
      (by rw [Limits.pullback.condition, ← hψ]; simp only [Category.assoc]))
    (Limits.pullback.snd f (v ≫ t) ≫ v)
    (by rw [Limits.pullback.lift_snd, Category.assoc])

theorem δ_comp {T' : Scheme.{0}} (v : T' ⟶ T) (hv : (v ≫ ψU ≫ U.ι) ≫ g = v ≫ t) :
    δ g U t ψU hψ v ≫ Limits.pullback.fst (Limits.pullback.snd f (U.ι ≫ g)) ψU ≫
        baseChangeSnd f (⟨U.ι, rfl⟩ : SchemeHomOver (U.ι ≫ g) g) =
      baseChangeSnd f (⟨v ≫ ψU ≫ U.ι, hv⟩ : SchemeHomOver (v ≫ t) g) := by
  unfold δ baseChangeSnd
  apply Limits.pullback.hom_ext
  · simp only [Category.assoc, Limits.pullback.lift_fst, Limits.pullback.lift_fst_assoc, Category.comp_id]
  · simp only [Category.assoc, Limits.pullback.lift_snd, Limits.pullback.lift_snd_assoc, Limits.pullback.lift_fst_assoc]

theorem δ_comp_snd {T' : Scheme.{0}} (v : T' ⟶ T) :
    δ g U t ψU hψ v ≫ Limits.pullback.snd (Limits.pullback.snd f (U.ι ≫ g)) ψU = Limits.pullback.snd f (v ≫ t) ≫ v := by
  unfold δ
  rw [Limits.pullback.lift_snd]

include hψ in

theorem trivial_of_iso_on (V : T.Opens)
    (e : (Scheme.Modules.pullback ((Limits.pullback.snd (Limits.pullback.snd f (U.ι ≫ g)) ψU) ⁻¹ᵁ V).ι).obj
        ((Scheme.Modules.pullback (Limits.pullback.fst (Limits.pullback.snd f (U.ι ≫ g)) ψU)).obj
          ((Scheme.Modules.pullback (baseChangeSnd f (⟨U.ι, rfl⟩ : SchemeHomOver (U.ι ≫ g) g))).obj M.L)) ≅
      (Scheme.Modules.pullback ((Limits.pullback.snd (Limits.pullback.snd f (U.ι ≫ g)) ψU) ⁻¹ᵁ V).ι).obj
        ((Scheme.Modules.pullback (Limits.pullback.fst (Limits.pullback.snd f (U.ι ≫ g)) ψU)).obj
          (SheafOfModules.unit (Limits.pullback f (U.ι ≫ g)).ringCatSheaf)))
    (hv : (V.ι ≫ ψU ≫ U.ι) ≫ g = V.ι ≫ t) :
    Nonempty ((M.pullbackAlong (⟨V.ι ≫ ψU ≫ U.ι, hv⟩ : SchemeHomOver (V.ι ≫ t) g)).L ≅
      (RigidifiedLineBundle.unit (c := f) (ε := L.one (𝟙 (Spec (CommRingCat.of R)))) (V.ι ≫ t)).L) := by

  have hr : Set.range (δ g U t ψU hψ V.ι) ⊆
      Set.range ((Limits.pullback.snd (Limits.pullback.snd f (U.ι ≫ g)) ψU) ⁻¹ᵁ V).ι := by
    rw [Scheme.Opens.range_ι]
    rintro _ ⟨w, rfl⟩
    show (Limits.pullback.snd (Limits.pullback.snd f (U.ι ≫ g)) ψU) (δ g U t ψU hψ V.ι w) ∈ V
    rw [← Scheme.Hom.comp_apply, δ_comp_snd, Scheme.Hom.comp_apply]
    exact (Limits.pullback.snd f (V.ι ≫ t) w).2
  let γ := IsOpenImmersion.lift ((Limits.pullback.snd (Limits.pullback.snd f (U.ι ≫ g)) ψU) ⁻¹ᵁ V).ι
    (δ g U t ψU hψ V.ι) hr
  have hγ : γ ≫ ((Limits.pullback.snd (Limits.pullback.snd f (U.ι ≫ g)) ψU) ⁻¹ᵁ V).ι = δ g U t ψU hψ V.ι :=
    IsOpenImmersion.lift_fac _ _ hr
  have hcomp : baseChangeSnd f (⟨V.ι ≫ ψU ≫ U.ι, hv⟩ : SchemeHomOver (V.ι ≫ t) g) =
      (γ ≫ ((Limits.pullback.snd (Limits.pullback.snd f (U.ι ≫ g)) ψU) ⁻¹ᵁ V).ι) ≫
        (Limits.pullback.fst (Limits.pullback.snd f (U.ι ≫ g)) ψU ≫
          baseChangeSnd f (⟨U.ι, rfl⟩ : SchemeHomOver (U.ι ≫ g) g)) := by
    rw [hγ, δ_comp]
  exact ⟨(Scheme.Modules.pullbackCongr hcomp).app M.L ≪≫
    ((Scheme.Modules.pullbackComp _ _).app M.L).symm ≪≫
    (Scheme.Modules.pullback _).mapIso ((Scheme.Modules.pullbackComp _ _).app M.L).symm ≪≫
    ((Scheme.Modules.pullbackComp γ _).app _).symm ≪≫
    (Scheme.Modules.pullback γ).mapIso e ≪≫
    (Scheme.Modules.pullbackComp γ _).app _ ≪≫
    (Scheme.Modules.pullbackComp _ _).app _ ≪≫
    Scheme.Modules.pullbackUnitIso _⟩

end Geometry

end DockHelpers

theorem solution
    {R : Type} [CommRing R] [IsNoetherianRing R] {A : Scheme.{0}} {f : A ⟶ Spec (CommRingCat.of R)}
    (L : RelativeGroupLaw R f) (hA : AbelianSchemePropertyBundle R f)
    {X : Scheme.{0}} (g : X ⟶ Spec (CommRingCat.of R)) [LocallyOfFiniteType g]
    (M : RigidifiedLineBundle f (L.one (𝟙 (Spec (CommRingCat.of R)))) g) (U : X.affineOpens) :
    ∃ (ZU : Scheme.{0}) (ιU : ZU ⟶ ((U : X.Opens) : Scheme.{0})), IsClosedImmersion ιU ∧
        ∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of R)) (ψU : T ⟶ ((U : X.Opens) : Scheme.{0}))
          (hψ : (ψU ≫ (U : X.Opens).ι) ≫ g = t),
          (Nonempty ((M.pullbackAlong (⟨ψU ≫ (U : X.Opens).ι, hψ⟩ : SchemeHomOver t g)).L ≅
              (RigidifiedLineBundle.unit (c := f) (ε := L.one (𝟙 (Spec (CommRingCat.of R)))) t).L) ↔
            ∃ ψ₀ : T ⟶ ZU, ψ₀ ≫ ιU = ψU) := by

  haveI : IsProper f := hA.proper
  haveI : Smooth f := hA.smooth
  haveI : GeometricallyIntegral f :=
    GoodReductionJacobian.AbelianSchemePropertyBundle.geometricallyIntegral_of_commRing hA
  haveI : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian g

  obtain ⟨Z, ι, hι, hZ⟩ :=
    AlgebraicGeometry.Scheme.Modules.IsInvertible.exists_isClosedImmersion_forall_iff_locallyIsoOver_of_flat_of_isProper
      f (DockHelpers.hH0 hA) ((U : X.Opens).ι ≫ g)
      ((Scheme.Modules.pullback (baseChangeSnd f (⟨(U : X.Opens).ι, rfl⟩ : SchemeHomOver ((U : X.Opens).ι ≫ g) g))).obj M.L)
      (SheafOfModules.unit (Limits.pullback f ((U : X.Opens).ι ≫ g)).ringCatSheaf)
      (M.isInvertible.pullback _) (Scheme.Modules.isInvertible_unit _)
  refine ⟨Z, ι, hι, ?_⟩
  intro T t ψU hψ
  refine Iff.trans ?_ (hZ ψU).symm
  constructor
  · rintro ⟨e⟩
    obtain ⟨e'⟩ := DockHelpers.iso_of_trivial L g M (U : X.Opens) t ψU hψ e
    exact Scheme.Modules.LocallyIsoOver.of_iso _ e'
  · intro hloc
    choose V hVmem hViso using hloc
    let 𝒰 : T.OpenCover := Scheme.Cover.mkOfCovers (↥T) (fun τ => ((V τ : T.Opens) : Scheme.{0})) (fun τ => (V τ).ι)
      (fun x => ⟨x, ⟨x, hVmem x⟩, rfl⟩)
    refine (AlgebraicGeometry.RelPicard.RigidifiedLineBundle.nonempty_iso_unit_iff_forall_openCover L hA g M t
      (⟨ψU ≫ (U : X.Opens).ι, hψ⟩ : SchemeHomOver t g) 𝒰).mpr fun τ => ?_
    obtain ⟨e⟩ := hViso τ
    exact DockHelpers.trivial_of_iso_on L g M (U : X.Opens) t ψU hψ (V τ) e _

end S_AlgebraicGeometry_RelPicard_RigidifiedLineBundle_exists_isClosedImmersion_chart_iff_affineOpens_of_isNoetherianRing
end P2MW
export P2MW.S_AlgebraicGeometry_RelPicard_RigidifiedLineBundle_exists_isClosedImmersion_chart_iff_affineOpens_of_isNoetherianRing (solution)
