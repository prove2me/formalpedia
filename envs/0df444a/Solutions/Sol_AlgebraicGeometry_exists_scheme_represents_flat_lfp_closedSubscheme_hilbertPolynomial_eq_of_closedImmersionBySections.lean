-- Prove2me | solution 1 for AlgebraicGeometry.exists_scheme_represents_flat_lfp_closedSubscheme_hilbertPolynomial_eq_of_closedImmersionBySections
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.553648+00:00
-- url     : https://prove2.me/submissions/4c2cb018-c45f-5c1f-b74e-24d1e5f7a678

import Definitions.Def_JacJ1Iface
import Definitions.Def_AlgebraicGeometry_RelativeGroupLaw
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import Definitions.Def_AlgebraicGeometry_ModulesProjPresentation
import Definitions.Def_AlgebraicGeometry_PolarisedAbelianScheme
import Definitions.Def_SheafOfModules_MonoidalV2
import Definitions.Def_AlgebraicGeometry_ProjSpace
import Definitions.Def_AlgebraicGeometry_HilbertFunctor
import Theorems.Thm_AlgebraicGeometry_ProjSpace_isPullback_map
import Theorems.Thm_AlgebraicGeometry_ProjSpace_exists_idealSheafData_ideal_basicOpen_eq_span
import Theorems.Thm_AlgebraicGeometry_ProjSpace_eq_ker_of_ideal_basicOpen_eq_span_of_isClosedImmersion
import Theorems.Thm_AlgebraicGeometry_ProjSpace_eq_comap_map_of_ideal_basicOpen_eq_span
import Theorems.Thm_AlgebraicGeometry_ProjSpace_exists_iso_hom_comp_eq_of_isPullback_of_comp_eq_map
import Theorems.Thm_AlgebraicGeometry_HilbertFunctor_exists_point_I_eq_span_of_isClosedImmersion_of_flat_of_locallyOfFinitePresentation
import Theorems.Thm_AlgebraicGeometry_HilbertFunctor_exists_scheme_represents_isProper_locallyOfFinitePresentation_hilbertFunctionOf
import Theorems.Thm_AlgebraicGeometry_HilbertFunctor_exists_uniform_cover_forall_geomFibre_ideal_eq_point_of_isClosedImmersion_of_flat_of_locallyOfFinitePresentation
import Theorems.Thm_AlgebraicGeometry_HilbertFunctor_exists_closedImmersion_flat_lfp_forall_mem_iff_ker_ideal_eq_of_point_hilbertFunctionOf
import Theorems.Thm_AlgebraicGeometry_exists_forall_geomFibreH0Finrank_tensorPow_eq_hilbertFunctionOf_of_point_geomFibre_of_hom
import Theorems.Thm_AlgebraicGeometry_ProjSpace_exists_ideal_fg_forall_ker_ideal_basicOpen_eq_span_of_isClosedImmersion
import Theorems.Thm_AlgebraicGeometry_HilbertFunctor_exists_isClosedImmersion_locallyOfFinitePresentation_forall_factors_iff_forall_mem_of_isHomogeneous_of_le_of_fg
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_exists_scheme_represents_flat_lfp_closedSubscheme_hilbertPolynomial_eq_of_closedImmersionBySections
p2m_attr_erase "instance" "AlgebraicGeometry.OModulePresheaf.isScalarTower AlgebraicGeometry.Scheme.OrderedAffineCover.instLinearOrder AlgebraicGeometry.OModulePresheaf.module AlgebraicGeometry.Scheme.OrderedAffineCover.instFintype AlgebraicGeometry.Scheme.OrderedAffineCover.instFintypeIdx AlgebraicGeometry.OModulePresheaf.addCommGroup AlgebraicGeometry.Scheme.OrderedAffineCover.instDecidableEqIdx AlgebraicGeometry.OModulePresheaf.moduleSections TwoChartCech.Sections.M0_moduleA TwoChartCech.Sections.M1_module TwoChartCech.Cover.A01_algebra TwoChartCech.Cover.A0_algebra TwoChartCech.Cover.A1_commRing TwoChartCech.Cover.A1_algebra TwoChartCech.Sections.M01_module TwoChartCech.Sections.M0_addCommGroup TwoChartCech.Sections.M0_tower TwoChartCech.Sections.M01_addCommGroup TwoChartCech.Cover.A0_commRing TwoChartCech.Sections.M1_tower TwoChartCech.Sections.M01_moduleA TwoChartCech.Sections.M0_module TwoChartCech.Sections.M1_moduleA TwoChartCech.Sections.M1_addCommGroup TwoChartCech.Cover.A01_commRing TwoChartCech.Sections.M01_tower CoherentBaseChange.TwoTermComplex.C0_module CoherentBaseChange.TwoTermComplex.C0_addCommGroup CoherentBaseChange.TwoTermComplex.C1_module CoherentBaseChange.TwoTermComplex.C1_addCommGroup CoherentBaseChange.TwoTermComplex.C0_free CoherentBaseChange.TwoTermComplex.C1_finite CoherentBaseChange.TwoTermComplex.C0_finite CoherentBaseChange.TwoTermComplex.C1_free AlgebraicGeometry.ProjSpace.twistObj.addCommGroup AlgebraicGeometry.ProjSpace.twistFam.module AlgebraicGeometry.ProjSpace.twistObj.module AlgebraicGeometry.ProjSpace.twistObj.moduleSections AlgebraicGeometry.ProjSpace.twistFam.addCommGroup ProjSpaceCech.GradedModule.H.module"
p2m_attr_erase "instance" "ProjSpaceCech.GradedModule.H.addCommGroup ProjSpaceCech.GradedModule.sec.instAdd ProjSpaceCech.GradedModule.sec.instNeg ProjSpaceCech.GradedModule.acg ProjSpaceCech.GradedModule.Frac.setoid ProjSpaceCech.GradedModule.modR ProjSpaceCech.GradedModule.sec.instModule ProjSpaceCech.GradedModule.sec.instAddCommGroup ProjSpaceCech.GradedModule.sec.instZero ProjSpaceCech.GradedModule.Presentation.fJ ProjSpaceCech.GradedModule.sec.instSMul ProjSpaceCech.Twist.H.module ProjSpaceCech.Idx.instFintype ProjSpaceCech.Twist.H.addCommGroup ProjSpaceCech.Idx.instDecidableEq ProjSpaceCech.Twist.Mon.instDecidableEq ProjSpaceCech.Twist.cochain.instAddCommGroup ProjSpaceCech.Twist.cochain.instModule AlgebraicGeometry.OModulePresheaf.instSubsingletonObjZero PresheafOfModules.PullbackMonoidal.pullback_monoidal PresheafOfModules.PullbackMonoidal.isIso_δ PresheafOfModules.pushforward_laxMonoidal PresheafOfModules.PullbackMonoidal.isIso_η PresheafOfModules.free_monoidal PresheafOfModules.restrictScalars_laxMonoidal PresheafOfModules.PullbackMonoidal.isIso_δ_gS PresheafOfModules.pullback_oplaxMonoidal PresheafOfModules.PullbackMonoidal.instPreservesColimitsOfSizeCompOppositeCommRingCatRingCatForget₂RingHomCarrierCarrierPb PresheafOfModules.pullback_monoidal' AlgebraicGeometry.Scheme.Modules.preservesBinaryProducts_opensMap AlgebraicGeometry.Scheme.Modules.pullback_monoidal AlgebraicGeometry.Scheme.Modules.sheafify_isLocalization' AlgebraicGeometry.Scheme.Modules.preservesTerminal_opensMap AlgebraicGeometry.Scheme.Modules.pullback₀_monoidal AlgebraicGeometry.Scheme.Modules.preservesFiniteProducts_opensMap AlgebraicGeometry.Scheme.Modules.instLiftingPresheafOfModulesSheafifyPresheafWOpensCarrierCarrierCommRingCatGrothendieckTopologyObjFunctorOppositeIsSheafSheafCompPullback₀Pullback AlgebraicGeometry.OModulePresheaf.Leray.relAltC_scalarTower AlgebraicGeometry.OModulePresheaf.Leray.ker_relAltd_modΓ AlgebraicGeometry.OModulePresheaf.Leray.relAltC_modΓ AlgebraicGeometry.OModulePresheaf.Leray.biC_abGrp"
p2m_attr_erase "instance" "AlgebraicGeometry.OModulePresheaf.Leray.relAltH_modΓ AlgebraicGeometry.OModulePresheaf.Leray.ker_relAltd_smul AlgebraicGeometry.OModulePresheaf.Leray.relAltH_scalarTower AlgebraicGeometry.OModulePresheaf.Leray.relAltH_smul AlgebraicGeometry.OModulePresheaf.Leray.biC_module AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instDecidableEqIdx AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instFintype AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instLinearOrder AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instFintypeIdx DoubleComplex.instModuleE₂I DoubleComplex.Bounded.modR DoubleComplex.instModuleE₂II DoubleComplex.instAddCommGroupE₂II DoubleComplex.Bounded.abGrp DoubleComplex.instAddCommGroupE₂I AlgebraicGeometry.Scheme.Modules.GlueOfCocycle.instSMulCarrierObjOppositeOpensCarrierCarrierCommRingCatPresheafOpOpensSubtypeForallMinMemAddSubgroupFamilies AlgebraicGeometry.Scheme.Modules.GlueOfCocycle.instModulePreGlue AlgebraicGeometry.Scheme.Modules.GlueOfCocycle.instModuleCarrierObjOppositeOpensCarrierCarrierCommRingCatPresheafOpOpensSubtypeForallMinMemAddSubgroupFamilies IsDirectLimit.Module.instDirectLimitCoeLinearMapIdOfOfNonempty AlgebraicGeometry.SubalgebraStages.compactSpace_pullback AlgebraicGeometry.SubalgebraStages.quasiSeparatedSpace_pullback AlgebraicGeometry.SubalgebraStages.compactSpace_obj AlgebraicGeometry.SubalgebraStages.quasiSeparatedSpace_obj AlgebraicGeometry.SubalgebraStages.quasiCompact_snd AlgebraicGeometry.SubalgebraStages.isAffineHom_leg AlgebraicGeometry.SubalgebraStages.isAffineHom_trans AlgebraicGeometry.SubalgebraStages.isAffineHom_diagram_map AlgebraicGeometry.SubalgebraStages.quasiSeparated_snd AlgebraicGeometry.SubalgebraStages.isCofiltered_op"
p2m_attr_erase "simp" "AlgebraicGeometry.Scheme.OrderedAffineCover.mk.injEq AlgebraicGeometry.OModulePresheaf.mk.sizeOf_spec AlgebraicGeometry.Scheme.OrderedAffineCover.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.mk.injEq AlgebraicGeometry.Scheme.TwoAffineOpenCover.mk.injEq AlgebraicGeometry.Scheme.TwoAffineOpenCover.mk.sizeOf_spec AlgebraicGeometry.Scheme.TwoAffineOpenCover.pullback_U1 AlgebraicGeometry.Scheme.TwoAffineOpenCover.pullback_U0 TwoChartCech.Sections.mk.injEq TwoChartCech.Cover.mk.injEq TwoChartCech.GrothendieckComplex.mk.injEq TwoChartCech.Sections.mk.sizeOf_spec TwoChartCech.Cover.mk.sizeOf_spec TwoChartCech.Cover.lineBundle_r0_apply TwoChartCech.GrothendieckComplex.mk.sizeOf_spec TwoChartCech.Cover.lineBundle_r1_apply CoherentBaseChange.TwoTermComplex.mk.sizeOf_spec CoherentBaseChange.TwoTermComplex.mk.injEq AlgebraicGeometry.ProjSpace.twistObj.mk.injEq AlgebraicGeometry.ProjSpace.twistObj.zero_val AlgebraicGeometry.ProjSpace.twistObj.add_val AlgebraicGeometry.ProjSpace.twist_res_val AlgebraicGeometry.ProjSpace.twist_smul_val AlgebraicGeometry.ProjSpace.twistGradeToObj_val AlgebraicGeometry.ProjSpace.twistObj.smul_val AlgebraicGeometry.ProjSpace.twistGradeEquiv_apply_val AlgebraicGeometry.ProjSpace.twistObj.mk.sizeOf_spec ProjSpaceCech.GradedModule.mk.injEq ProjSpaceCech.GradedModule.mk.sizeOf_spec ProjSpaceCech.GradedModule.Frac.mk.sizeOf_spec ProjSpaceCech.GradedModule.Presentation.mk.injEq ProjSpaceCech.GradedModule.Frac.mk.injEq ProjSpaceCech.GradedModule.Presentation.mk.sizeOf_spec ProjSpaceCech.GradedModule.Hom.shift_toLinearMap ProjSpaceCech.GradedModule.Hom.mk.sizeOf_spec ProjSpaceCech.GradedModule.Hom.mk.injEq AlgebraicGeometry.OModulePresheaf.Hom.mk.injEq AlgebraicGeometry.OModulePresheaf.Hom.id_app AlgebraicGeometry.OModulePresheaf.AffHom.appSections_apply AlgebraicGeometry.OModulePresheaf.AffHom.comp_app"
p2m_attr_erase "simp" "AlgebraicGeometry.OModulePresheaf.AffSES.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.AffHom.kerMap_coe AlgebraicGeometry.OModulePresheaf.AffHom.id_app AlgebraicGeometry.OModulePresheaf.Hom.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.Hom.toAffHom_app AlgebraicGeometry.OModulePresheaf.SES.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.AffHom.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.Hom.comp_app AlgebraicGeometry.OModulePresheaf.SES.mk.injEq AlgebraicGeometry.OModulePresheaf.AffHom.mk.injEq AlgebraicGeometry.OModulePresheaf.Hom.appSections_apply AlgebraicGeometry.OModulePresheaf.AffSES.mk.injEq AlgebraicGeometry.OModulePresheaf.prod_obj AlgebraicGeometry.OModulePresheaf.restrOpen_obj AlgebraicGeometry.OModulePresheaf.DevissageStep.mk.injEq AlgebraicGeometry.OModulePresheaf.pushforward_obj AlgebraicGeometry.OModulePresheaf.im_obj AlgebraicGeometry.OModulePresheaf.pow_obj AlgebraicGeometry.OModulePresheaf.fstHom_app AlgebraicGeometry.OModulePresheaf.ker_obj AlgebraicGeometry.OModulePresheaf.coker_obj AlgebraicGeometry.OModulePresheaf.DevissageStep.mk.sizeOf_spec AlgebraicGeometry.Scheme.OrderedAffineCover.preimage_U AlgebraicGeometry.OModulePresheaf.sndHom_app AlgebraicGeometry.Scheme.Modules.tensorPow_zero AlgebraicGeometry.Scheme.Modules.tensorPow_succ PresheafOfModules.freeεIso_hom_app PresheafOfModules.freeμIso_hom_app AlgebraicGeometry.Scheme.Modules.tensorSections_zero_right AlgebraicGeometry.Scheme.Modules.map_unitSection AlgebraicGeometry.Scheme.Modules.tensorSectionsBilin_apply AlgebraicGeometry.Scheme.Modules.tensorPowSection_zero AlgebraicGeometry.Scheme.Modules.tensorSections_zero_left AlgebraicGeometry.OModulePresheaf.Leray.restrictToPreimage_U AlgebraicGeometry.Scheme.OrderedAffineCover.toCoverOf_U AlgebraicGeometry.Scheme.OrderedAffineCoverOf.mk.sizeOf_spec AlgebraicGeometry.Scheme.OrderedAffineCoverOf.mk.injEq AlgebraicGeometry.Scheme.OrderedAffineCover.restrict_U DoubleComplex.Bounded.mk.injEq DoubleComplex.Bounded.mk.sizeOf_spec"
p2m_attr_erase "simp" "DoubleComplex.Convergence.mk.injEq DoubleComplex.Convergence.mk.sizeOf_spec DoubleComplex.SubQuot.mk.sizeOf_spec DoubleComplex.SubQuot.mk.injEq AlgebraicGeometry.Scheme.Modules.glueComponent_glueMk AlgebraicGeometry.Scheme.Modules.UnitCocycle.mk.injEq AlgebraicGeometry.Scheme.Modules.UnitCocycle.mk.sizeOf_spec IsDirectLimit.Module.linearEquiv_symm_apply IsDirectLimit.linearEquiv_symm_apply IsDirectLimit.lift_of IsDirectLimit.Module.linearEquiv_apply IsDirectLimit.Module.lift_of IsDirectLimit.Equiv_apply AlgebraicGeometry.SubalgebraStages.specCone_π_app AlgebraicGeometry.SubalgebraStages.specLeg_specHom AlgebraicGeometry.SubalgebraStages.specLeg_specTrans AlgebraicGeometry.SubalgebraStages.cone_pt AlgebraicGeometry.SubalgebraStages.trans_fst AlgebraicGeometry.SubalgebraStages.diagram_obj AlgebraicGeometry.SubalgebraStages.leg_snd AlgebraicGeometry.SubalgebraStages.diagram_map AlgebraicGeometry.SubalgebraStages.specTrans_refl AlgebraicGeometry.SubalgebraStages.trans_snd AlgebraicGeometry.SubalgebraStages.specTrans_specHom AlgebraicGeometry.SubalgebraStages.specCone_pt AlgebraicGeometry.SubalgebraStages.cone_π_app AlgebraicGeometry.SubalgebraStages.specDiagram_map AlgebraicGeometry.SubalgebraStages.specDiagram_obj AlgebraicGeometry.SubalgebraStages.leg_fst AlgebraicGeometry.SubalgebraStages.leg_trans CategoryTheory.Functor.OverTotal.ofFibre_fst CategoryTheory.Functor.overTotal_map_fst"

set_option autoImplicit false
open MvPolynomial CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.HilbertFunctor NeronModelInfra GoodReductionJacobian
p2m_open "CategoryTheory.MonoidalCategory"
attribute [local instance] MvPolynomial.gradedAlgebra

noncomputable section

namespace HilbP

abbrev PPn (A : Type) [CommRing A] (n : ℕ) : Scheme.{0} := Proj (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) A)

section Emb

variable {S : Type} [CommRing S] {X : Scheme.{0}} {f : X ⟶ Spec (CommRingCat.of S)} {𝓛X : X.Modules} {n : ℕ}
  (𝔓 : Scheme.Modules.ProjPresentation 𝓛X f n) (S' : Type) [CommRing S']
  (s : Spec (CommRingCat.of S') ⟶ Spec (CommRingCat.of S)) (ψ : S →+* S') (hs : s = Spec.map (CommRingCat.ofHom ψ))

include hs in
theorem comm_emb :
    letI : Algebra S S' := ψ.toAlgebra
    (pullback.fst f s ≫ 𝔓.toProj) ≫ ProjSpace.π S n =
      pullback.snd f s ≫ Spec.map (CommRingCat.ofHom (algebraMap S S')) := by
  rw [Category.assoc, 𝔓.toProj_π, pullback.condition, hs]

def emb : pullback f s ⟶ PPn S' n :=
  letI : Algebra S S' := ψ.toAlgebra
  (ProjSpace.isPullback_map S S' n).lift (pullback.fst f s ≫ 𝔓.toProj) (pullback.snd f s) (comm_emb 𝔓 S' s ψ hs)

theorem emb_π : emb 𝔓 S' s ψ hs ≫ ProjSpace.π S' n = pullback.snd f s := by
  letI : Algebra S S' := ψ.toAlgebra
  exact (ProjSpace.isPullback_map S S' n).lift_snd _ _ _

theorem emb_map :
    (letI : Algebra S S' := ψ.toAlgebra; emb 𝔓 S' s ψ hs ≫ ProjSpace.map S S' n) = pullback.fst f s ≫ 𝔓.toProj := by
  letI : Algebra S S' := ψ.toAlgebra
  exact (ProjSpace.isPullback_map S S' n).lift_fst _ _ _

theorem isPullback_emb :
    letI : Algebra S S' := ψ.toAlgebra
    IsPullback (pullback.fst f s) (emb 𝔓 S' s ψ hs) 𝔓.toProj (ProjSpace.map S S' n) := by
  letI : Algebra S S' := ψ.toAlgebra
  have e : Spec.map (CommRingCat.ofHom (algebraMap S S')) = s := hs.symm
  have sq : IsPullback (pullback.fst f s) (emb 𝔓 S' s ψ hs ≫ ProjSpace.π S' n)
      (𝔓.toProj ≫ ProjSpace.π S n) (Spec.map (CommRingCat.ofHom (algebraMap S S'))) := by
    rw [emb_π, 𝔓.toProj_π, e]
    exact IsPullback.of_hasPullback f s
  exact IsPullback.of_bot sq (emb_map 𝔓 S' s ψ hs).symm (ProjSpace.isPullback_map S S' n)

theorem isClosedImmersion_emb (hci : IsClosedImmersion 𝔓.toProj) : IsClosedImmersion (emb 𝔓 S' s ψ hs) :=
  MorphismProperty.of_isPullback (isPullback_emb 𝔓 S' s ψ hs) hci

theorem ker_emb_ideal (hci : IsClosedImmersion 𝔓.toProj)
    (I₀ : Ideal (MvPolynomial (Fin (n + 1)) S)) (hI₀ : ∀ p ∈ I₀, ∀ d : ℕ, homogeneousComponent d p ∈ I₀)
    (hker : ∀ i : Fin (n + 1),
        (Scheme.Hom.ker 𝔓.toProj).ideal ⟨Proj.basicOpen (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) S) (MvPolynomial.X i),
          Proj.isAffineOpen_basicOpen (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) S) (MvPolynomial.X i) (ProjSpace.X_mem_one S n i) one_pos⟩ =
        Ideal.span { s | ∃ (d : ℕ) (F : MvPolynomial (Fin (n + 1)) S) (hF : F.IsHomogeneous d),
          F ∈ I₀ ∧
          s = (Proj.awayToSection (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) S) (MvPolynomial.X i))
              (HomogeneousLocalization.mk
                { deg := d
                  num := ⟨F, (MvPolynomial.mem_homogeneousSubmodule d F).mpr hF⟩
                  den := ⟨MvPolynomial.X i ^ d, (MvPolynomial.mem_homogeneousSubmodule d _).mpr (MvPolynomial.isHomogeneous_X_pow i d)⟩
                  den_mem := ⟨d, rfl⟩ }) })
    (i : Fin (n + 1)) :
    (Scheme.Hom.ker (emb 𝔓 S' s ψ hs)).ideal ⟨Proj.basicOpen (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) S') (MvPolynomial.X i),
          Proj.isAffineOpen_basicOpen (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) S') (MvPolynomial.X i) (ProjSpace.X_mem_one S' n i) one_pos⟩ =
        Ideal.span { s | ∃ (d : ℕ) (F : MvPolynomial (Fin (n + 1)) S') (hF : F.IsHomogeneous d),
          F ∈ I₀.map (MvPolynomial.map ψ) ∧
          s = (Proj.awayToSection (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) S') (MvPolynomial.X i))
              (HomogeneousLocalization.mk
                { deg := d
                  num := ⟨F, (MvPolynomial.mem_homogeneousSubmodule d F).mpr hF⟩
                  den := ⟨MvPolynomial.X i ^ d, (MvPolynomial.mem_homogeneousSubmodule d _).mpr (MvPolynomial.isHomogeneous_X_pow i d)⟩
                  den_mem := ⟨d, rfl⟩ }) } := by
  letI : Algebra S S' := ψ.toAlgebra
  haveI : IsClosedImmersion 𝔓.toProj := hci
  obtain ⟨𝓙, h𝓙⟩ := AlgebraicGeometry.ProjSpace.exists_idealSheafData_ideal_basicOpen_eq_span n S'
    (I₀.map (MvPolynomial.map (algebraMap S S')))
  have h1 : 𝓙 = (Scheme.Hom.ker 𝔓.toProj).comap (ProjSpace.map S S' n) :=
    AlgebraicGeometry.ProjSpace.eq_comap_map_of_ideal_basicOpen_eq_span n S S' I₀ hI₀ _ hker 𝓙 h𝓙
  have h2 : Scheme.Hom.ker (emb 𝔓 S' s ψ hs) = (Scheme.Hom.ker 𝔓.toProj).comap (ProjSpace.map S S' n) := by
    have sq := (isPullback_emb 𝔓 S' s ψ hs).flip
    rw [← Scheme.IdealSheafData.ker_fst_of_isClosedImmersion 𝔓.toProj (ProjSpace.map S S' n), ← sq.isoPullback_hom_fst,
      Scheme.Hom.ker_comp_of_isIso]
  rw [h2, ← h1]
  exact h𝓙 i

theorem app_emb_eq_zero (hci : IsClosedImmersion 𝔓.toProj)
    (I₀ : Ideal (MvPolynomial (Fin (n + 1)) S)) (hI₀ : ∀ p ∈ I₀, ∀ d : ℕ, homogeneousComponent d p ∈ I₀)
    (hker : ∀ i : Fin (n + 1),
        (Scheme.Hom.ker 𝔓.toProj).ideal ⟨Proj.basicOpen (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) S) (MvPolynomial.X i),
          Proj.isAffineOpen_basicOpen (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) S) (MvPolynomial.X i) (ProjSpace.X_mem_one S n i) one_pos⟩ =
        Ideal.span { s | ∃ (d : ℕ) (F : MvPolynomial (Fin (n + 1)) S) (hF : F.IsHomogeneous d),
          F ∈ I₀ ∧
          s = (Proj.awayToSection (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) S) (MvPolynomial.X i))
              (HomogeneousLocalization.mk
                { deg := d
                  num := ⟨F, (MvPolynomial.mem_homogeneousSubmodule d F).mpr hF⟩
                  den := ⟨MvPolynomial.X i ^ d, (MvPolynomial.mem_homogeneousSubmodule d _).mpr (MvPolynomial.isHomogeneous_X_pow i d)⟩
                  den_mem := ⟨d, rfl⟩ }) })
    (d : ℕ) (F : MvPolynomial (Fin (n + 1)) S') (hF : F.IsHomogeneous d) (hFI : F ∈ I₀.map (MvPolynomial.map ψ))
    (i : Fin (n + 1)) :
    (emb 𝔓 S' s ψ hs).app (Proj.basicOpen (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) S') (MvPolynomial.X i))
      ((Proj.awayToSection (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) S') (MvPolynomial.X i))
        (HomogeneousLocalization.mk
          { deg := d
            num := ⟨F, (MvPolynomial.mem_homogeneousSubmodule d F).mpr hF⟩
            den := ⟨MvPolynomial.X i ^ d, (MvPolynomial.mem_homogeneousSubmodule d _).mpr (MvPolynomial.isHomogeneous_X_pow i d)⟩
            den_mem := ⟨d, rfl⟩ })) = 0 := by
  haveI : IsClosedImmersion (emb 𝔓 S' s ψ hs) := isClosedImmersion_emb 𝔓 S' s ψ hs hci
  have hk := Scheme.Hom.ker_apply (emb 𝔓 S' s ψ hs)
    ⟨Proj.basicOpen (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) S') (MvPolynomial.X i),
      Proj.isAffineOpen_basicOpen (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) S') (MvPolynomial.X i) (ProjSpace.X_mem_one S' n i) one_pos⟩
  rw [ker_emb_ideal 𝔓 S' s ψ hs hci I₀ hI₀ hker i] at hk
  have hmem : (Proj.awayToSection (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) S') (MvPolynomial.X i))
        (HomogeneousLocalization.mk
          { deg := d
            num := ⟨F, (MvPolynomial.mem_homogeneousSubmodule d F).mpr hF⟩
            den := ⟨MvPolynomial.X i ^ d, (MvPolynomial.mem_homogeneousSubmodule d _).mpr (MvPolynomial.isHomogeneous_X_pow i d)⟩
            den_mem := ⟨d, rfl⟩ }) ∈
      Ideal.span { s | ∃ (d : ℕ) (F : MvPolynomial (Fin (n + 1)) S') (hF : F.IsHomogeneous d),
          F ∈ I₀.map (MvPolynomial.map ψ) ∧
          s = (Proj.awayToSection (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) S') (MvPolynomial.X i))
              (HomogeneousLocalization.mk
                { deg := d
                  num := ⟨F, (MvPolynomial.mem_homogeneousSubmodule d F).mpr hF⟩
                  den := ⟨MvPolynomial.X i ^ d, (MvPolynomial.mem_homogeneousSubmodule d _).mpr (MvPolynomial.isHomogeneous_X_pow i d)⟩
                  den_mem := ⟨d, rfl⟩ }) } :=
    Ideal.subset_span ⟨d, F, hF, hFI, rfl⟩
  rw [hk] at hmem
  exact RingHom.mem_ker.mp hmem

end Emb

section HS

variable {n : ℕ} {h : ℕ → ℕ} (H : Scheme.{0}) (pH : H ⟶ Spec (CommRingCat.of ℤ))
  (ptH : ∀ (A : Type) [CommRing A], Point A n h ≃ (Spec (CommRingCat.of A) ⟶ H))
  (hoverH : ∀ (A : Type) [CommRing A] (x : Point A n h), ptH A x ≫ pH = Spec.map (CommRingCat.ofHom (algebraMap ℤ A)))
  (S : Type) [CommRing S]

abbrev HS : Scheme.{0} := pullback pH (Spec.map (CommRingCat.ofHom (algebraMap ℤ S)))

abbrev πHS : HS H pH S ⟶ Spec (CommRingCat.of S) := pullback.snd _ _

theorem int_comp {A : Type} [CommRing A] (ψ : S →+* A) :
    Spec.map (CommRingCat.ofHom ψ) ≫ Spec.map (CommRingCat.ofHom (algebraMap ℤ S)) =
      Spec.map (CommRingCat.ofHom (algebraMap ℤ A)) := by
  rw [← Spec.map_comp, ← CommRingCat.ofHom_comp, RingHom.ext_int (ψ.comp (algebraMap ℤ S)) (algebraMap ℤ A)]

def ptHS (A : Type) [CommRing A] (ψ : S →+* A) :
    Point A n h ≃ SchemeHomOver (Spec.map (CommRingCat.ofHom ψ)) (πHS H pH S) where
  toFun p := ⟨pullback.lift (ptH A p) (Spec.map (CommRingCat.ofHom ψ)) (by rw [hoverH, int_comp]),
    pullback.lift_snd _ _ _⟩
  invFun v := (ptH A).symm (v.1 ≫ pullback.fst _ _)
  left_inv p := by
    change (ptH A).symm (pullback.lift _ _ _ ≫ pullback.fst _ _) = p
    rw [pullback.lift_fst]
    exact Equiv.symm_apply_apply _ _
  right_inv v := by
    apply Subtype.ext
    apply pullback.hom_ext
    · change pullback.lift _ _ _ ≫ pullback.fst _ _ = v.1 ≫ pullback.fst _ _
      rw [pullback.lift_fst]
      exact Equiv.apply_symm_apply _ _
    · change pullback.lift _ _ _ ≫ pullback.snd _ _ = v.1 ≫ pullback.snd _ _
      rw [pullback.lift_snd]
      exact v.2.symm

theorem ptHS_fst (A : Type) [CommRing A] (ψ : S →+* A) (p : Point A n h) :
    (ptHS H pH ptH hoverH S A ψ p).1 ≫ pullback.fst _ _ = ptH A p :=
  pullback.lift_fst _ _ _

theorem ptHS_symm_apply (A : Type) [CommRing A] (ψ : S →+* A)
    (v : SchemeHomOver (Spec.map (CommRingCat.ofHom ψ)) (πHS H pH S)) :
    (ptHS H pH ptH hoverH S A ψ).symm v = (ptH A).symm (v.1 ≫ pullback.fst _ _) := rfl

include hoverH in
theorem hnatHS
    (hnatH : ∀ (A B : Type) [CommRing A] [CommRing B] (φ : A →+* B) (x : Point A n h) (y : Point B n h),
      y.I = Ideal.map (MvPolynomial.map φ) x.I ↔ ptH B y = Spec.map (CommRingCat.ofHom φ) ≫ ptH A x)
    (A B : Type) [CommRing A] [CommRing B] (ψ : S →+* A) (φ : A →+* B) (P : Point A n h) (Q : Point B n h)
    (hQ : Q.I = Ideal.map (MvPolynomial.map φ) P.I) :
    (ptHS H pH ptH hoverH S B (φ.comp ψ) Q).1 = Spec.map (CommRingCat.ofHom φ) ≫ (ptHS H pH ptH hoverH S A ψ P).1 := by
  apply pullback.hom_ext
  · rw [Category.assoc, ptHS_fst, ptHS_fst]
    exact (hnatH A B φ P Q).mp hQ
  · rw [Category.assoc]
    change pullback.lift _ _ _ ≫ pullback.snd _ _ = _ ≫ pullback.lift _ _ _ ≫ pullback.snd _ _
    rw [pullback.lift_snd, pullback.lift_snd, ← Spec.map_comp, ← CommRingCat.ofHom_comp]

end HS

section Poly

theorem cast_hilbertFunctionOf (n : ℕ) (P : Polynomial ℚ) {K : Type} [Field K] (I : Ideal (MvPolynomial (Fin (n + 1)) K))
    (d₁ : ℕ) (hd₁ : ∀ d : ℕ, d₁ ≤ d → (Module.finrank K (piece I d) : ℚ) = P.eval (d : ℚ))
    (m e : ℕ) (hm : m ≤ e) (h1 : d₁ ≤ e) :
    ((hilbertFunctionOf n P m e : ℕ) : ℚ) = P.eval (e : ℚ) := by
  have hPe := hd₁ e h1
  simp only [hilbertFunctionOf, if_neg (not_lt.mpr hm)]
  rw [← hPe, Int.floor_natCast, Int.toNat_natCast]

theorem poly_eq_of_eval_eq (P Q : Polynomial ℚ) (N : ℕ)
    (h : ∀ d : ℕ, N ≤ d → P.eval (d : ℚ) = Q.eval (d : ℚ)) : P = Q := by
  apply Polynomial.eq_of_infinite_eval_eq
  refine Set.infinite_of_injective_forall_mem (f := fun k : ℕ => ((N + k : ℕ) : ℚ)) ?_ ?_
  · intro a b hab
    have hab' : ((N + a : ℕ) : ℚ) = ((N + b : ℕ) : ℚ) := hab
    have : N + a = N + b := by exact_mod_cast hab'
    omega
  · intro k
    exact h (N + k) (Nat.le_add_right N k)

theorem HilbR_ringHom_eq_of_specMap_eq {R A : Type} [CommRing R] [CommRing A] {ψ ψ' : R →+* A}
    (h : Spec.map (CommRingCat.ofHom ψ) = Spec.map (CommRingCat.ofHom ψ')) : ψ = ψ' := by
  have := Spec.map_inj.mp h
  exact congrArg CommRingCat.Hom.hom this

theorem exists_isUnit_of_span_eq_top {A : Type} [CommRing A] {J : Type} (r : J → A)
    (hr : Ideal.span (Set.range r) = ⊤) (k : Type) [Field k] [Algebra A k] :
    ∃ j, IsUnit (algebraMap A k (r j)) := by
  by_contra hall
  simp only [not_exists] at hall
  have h0 : ∀ j, algebraMap A k (r j) = 0 := fun j => by
    by_contra hne
    exact hall j (isUnit_iff_ne_zero.mpr hne)
  have hmap : Ideal.map (algebraMap A k) (Ideal.span (Set.range r)) = ⊥ := by
    rw [Ideal.map_span, Ideal.span_eq_bot]
    rintro _ ⟨_, ⟨j, rfl⟩, rfl⟩
    exact h0 j
  rw [hr, Ideal.map_top] at hmap
  exact top_ne_bot hmap

end Poly

section MapComp

theorem projMap_congr {A C : Type} [CommRing A] [CommRing C] {n : ℕ}
    (φ ψ : MvPolynomial.homogeneousSubmodule (Fin (n + 1)) A →+*ᵍ MvPolynomial.homogeneousSubmodule (Fin (n + 1)) C)
    (hφ : HomogeneousIdeal.irrelevant (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) C) ≤
      (HomogeneousIdeal.irrelevant (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) A)).map φ)
    (hψ : HomogeneousIdeal.irrelevant (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) C) ≤
      (HomogeneousIdeal.irrelevant (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) A)).map ψ) (h : φ = ψ) :
    Proj.map φ hφ = Proj.map ψ hψ := by
  subst h; rfl

theorem mvMapGraded_comp (A B C : Type) [CommRing A] [CommRing B] [CommRing C]
    [Algebra A B] [Algebra B C] [Algebra A C] [IsScalarTower A B C] (n : ℕ) :
    (ProjSpace.mvMapGraded B C n).comp (ProjSpace.mvMapGraded A B n) = ProjSpace.mvMapGraded A C n := by
  ext p : 1
  change MvPolynomial.map (algebraMap B C) (MvPolynomial.map (algebraMap A B) p) = MvPolynomial.map (algebraMap A C) p
  rw [MvPolynomial.map_map, ← IsScalarTower.algebraMap_eq]

theorem map_comp_map (A B C : Type) [CommRing A] [CommRing B] [CommRing C]
    [Algebra A B] [Algebra B C] [Algebra A C] [IsScalarTower A B C] (n : ℕ) :
    ProjSpace.map B C n ≫ ProjSpace.map A B n = ProjSpace.map A C n := by
  rw [ProjSpace.map_eq, ProjSpace.map_eq, ProjSpace.map_eq, ← Proj.map_comp]
  exact projMap_congr _ _ _ _ (mvMapGraded_comp A B C n)

end MapComp

section Main

theorem preimage_spec {S S' : Type} [CommRing S] [CommRing S'] (s : Spec (CommRingCat.of S') ⟶ Spec (CommRingCat.of S)) :
    s = Spec.map (CommRingCat.ofHom (Spec.preimage s).hom) := by
  rw [CommRingCat.ofHom_hom, Spec.map_preimage]

set_option maxHeartbeats 6400000 in
theorem main
    (S : Type) [CommRing S] {X : Scheme.{0}} (f : X ⟶ Spec (CommRingCat.of S))
    [Flat f] [LocallyOfFinitePresentation f]
    (𝓛X : X.Modules) (hX₁ : Scheme.Modules.IsInvertible 𝓛X) (hX₂ : Scheme.Modules.ClosedImmersionBySections 𝓛X f)
    (P : Polynomial ℚ) :
    ∃ (C : Scheme.{0}) (πC : C ⟶ Spec (CommRingCat.of S))
      (pt : ∀ (S' : Type) [CommRing S'] (s : Spec (CommRingCat.of S') ⟶ Spec (CommRingCat.of S))
        (Z : Scheme.{0}) (ι : Z ⟶ pullback f s), IsClosedImmersion ι → Flat (ι ≫ pullback.snd f s) →
          LocallyOfFinitePresentation (ι ≫ pullback.snd f s) →
          (∀ (k : Type) [Field k] [IsAlgClosed k] (sk : S' →+* k), ∃ d₀ : ℕ, ∀ d : ℕ, d₀ ≤ d →
            ((Scheme.Modules.geomFibreH0Finrank (ι ≫ pullback.snd f s)
              (Nat.rec (motive := fun _ => Z.Modules) (𝟙_ Z.Modules)
                (fun _ M => M ⊗ (Scheme.Modules.pullback (ι ≫ pullback.fst f s)).obj 𝓛X) d) k sk : ℕ) : ℚ) =
              P.eval (d : ℚ)) →
          SchemeHomOver s πC),
      (∀ (S' S'' : Type) [CommRing S'] [CommRing S''] (ψ : S' →+* S'')
          (s : Spec (CommRingCat.of S') ⟶ Spec (CommRingCat.of S)) (s'' : Spec (CommRingCat.of S'') ⟶ Spec (CommRingCat.of S))
          (hs : Spec.map (CommRingCat.ofHom ψ) ≫ s = s'')
          (Z : Scheme.{0}) (ι : Z ⟶ pullback f s) (hι : IsClosedImmersion ι) (hfl : Flat (ι ≫ pullback.snd f s))
          (hfp : LocallyOfFinitePresentation (ι ≫ pullback.snd f s))
          (hHP : (∀ (k : Type) [Field k] [IsAlgClosed k] (sk : S' →+* k), ∃ d₀ : ℕ, ∀ d : ℕ, d₀ ≤ d →
            ((Scheme.Modules.geomFibreH0Finrank (ι ≫ pullback.snd f s)
              (Nat.rec (motive := fun _ => Z.Modules) (𝟙_ Z.Modules)
                (fun _ M => M ⊗ (Scheme.Modules.pullback (ι ≫ pullback.fst f s)).obj 𝓛X) d) k sk : ℕ) : ℚ) =
              P.eval (d : ℚ)))
          (Z'' : Scheme.{0}) (ι'' : Z'' ⟶ pullback f s'') (hι'' : IsClosedImmersion ι'') (hfl'' : Flat (ι'' ≫ pullback.snd f s''))
          (hfp'' : LocallyOfFinitePresentation (ι'' ≫ pullback.snd f s''))
          (hHP'' : (∀ (k : Type) [Field k] [IsAlgClosed k] (sk : S'' →+* k), ∃ d₀ : ℕ, ∀ d : ℕ, d₀ ≤ d →
            ((Scheme.Modules.geomFibreH0Finrank (ι'' ≫ pullback.snd f s'')
              (Nat.rec (motive := fun _ => Z''.Modules) (𝟙_ Z''.Modules)
                (fun _ M => M ⊗ (Scheme.Modules.pullback (ι'' ≫ pullback.fst f s'')).obj 𝓛X) d) k sk : ℕ) : ℚ) =
              P.eval (d : ℚ)))
          (e : Z'' ⟶ Z),
          IsPullback e (ι'' ≫ pullback.snd f s'') (ι ≫ pullback.snd f s) (Spec.map (CommRingCat.ofHom ψ)) →
          ι'' ≫ pullback.map f s'' f s (𝟙 X) (Spec.map (CommRingCat.ofHom ψ)) (𝟙 _)
              (by rw [Category.id_comp, Category.comp_id]) (by rw [Category.comp_id, hs]) = e ≫ ι →
          (pt S'' s'' Z'' ι'' hι'' hfl'' hfp'' hHP'').1 = Spec.map (CommRingCat.ofHom ψ) ≫ (pt S' s Z ι hι hfl hfp hHP).1) ∧
      (∀ (S' : Type) [CommRing S'] (s : Spec (CommRingCat.of S') ⟶ Spec (CommRingCat.of S)) (x : SchemeHomOver s πC),
        ∃ (Z : Scheme.{0}) (ι : Z ⟶ pullback f s) (hι : IsClosedImmersion ι) (hfl : Flat (ι ≫ pullback.snd f s))
          (hfp : LocallyOfFinitePresentation (ι ≫ pullback.snd f s))
          (hHP : (∀ (k : Type) [Field k] [IsAlgClosed k] (sk : S' →+* k), ∃ d₀ : ℕ, ∀ d : ℕ, d₀ ≤ d →
            ((Scheme.Modules.geomFibreH0Finrank (ι ≫ pullback.snd f s)
              (Nat.rec (motive := fun _ => Z.Modules) (𝟙_ Z.Modules)
                (fun _ M => M ⊗ (Scheme.Modules.pullback (ι ≫ pullback.fst f s)).obj 𝓛X) d) k sk : ℕ) : ℚ) =
              P.eval (d : ℚ))),
          pt S' s Z ι hι hfl hfp hHP = x) ∧
      (∀ (S' : Type) [CommRing S'] (s : Spec (CommRingCat.of S') ⟶ Spec (CommRingCat.of S))
          (Z Z' : Scheme.{0}) (ι : Z ⟶ pullback f s) (ι' : Z' ⟶ pullback f s)
          (hι : IsClosedImmersion ι) (hι' : IsClosedImmersion ι')
          (hfl : Flat (ι ≫ pullback.snd f s)) (hfl' : Flat (ι' ≫ pullback.snd f s))
          (hfp : LocallyOfFinitePresentation (ι ≫ pullback.snd f s)) (hfp' : LocallyOfFinitePresentation (ι' ≫ pullback.snd f s))
          (hHP : (∀ (k : Type) [Field k] [IsAlgClosed k] (sk : S' →+* k), ∃ d₀ : ℕ, ∀ d : ℕ, d₀ ≤ d →
            ((Scheme.Modules.geomFibreH0Finrank (ι ≫ pullback.snd f s)
              (Nat.rec (motive := fun _ => Z.Modules) (𝟙_ Z.Modules)
                (fun _ M => M ⊗ (Scheme.Modules.pullback (ι ≫ pullback.fst f s)).obj 𝓛X) d) k sk : ℕ) : ℚ) =
              P.eval (d : ℚ)))
          (hHP' : (∀ (k : Type) [Field k] [IsAlgClosed k] (sk : S' →+* k), ∃ d₀ : ℕ, ∀ d : ℕ, d₀ ≤ d →
            ((Scheme.Modules.geomFibreH0Finrank (ι' ≫ pullback.snd f s)
              (Nat.rec (motive := fun _ => Z'.Modules) (𝟙_ Z'.Modules)
                (fun _ M => M ⊗ (Scheme.Modules.pullback (ι' ≫ pullback.fst f s)).obj 𝓛X) d) k sk : ℕ) : ℚ) =
              P.eval (d : ℚ))),
        pt S' s Z ι hι hfl hfp hHP = pt S' s Z' ι' hι' hfl' hfp' hHP' → ∃ e : Z ≅ Z', e.hom ≫ ι' = ι) ∧
      IsProper πC ∧ LocallyOfFinitePresentation πC := by
  classical
  obtain ⟨n, 𝔓, hci⟩ := hX₂
  haveI := hci

  obtain ⟨D4, hD4⟩ :=
    AlgebraicGeometry.HilbertFunctor.exists_uniform_cover_forall_geomFibre_ideal_eq_point_of_isClosedImmersion_of_flat_of_locallyOfFinitePresentation n
  by_cases hPn : ∃ (K : Type) (_ : Field K) (I : Ideal (MvPolynomial (Fin (n + 1)) K)),
      (∀ p ∈ I, ∀ d : ℕ, homogeneousComponent d p ∈ I) ∧
      ∃ d₁ : ℕ, ∀ d : ℕ, d₁ ≤ d → (Module.finrank K (piece I d) : ℚ) = P.eval (d : ℚ)
  ·
    obtain ⟨D1, hD1⟩ :=
      AlgebraicGeometry.HilbertFunctor.exists_scheme_represents_isProper_locallyOfFinitePresentation_hilbertFunctionOf n P hPn
    obtain ⟨D2, hD2⟩ :=
      AlgebraicGeometry.HilbertFunctor.exists_closedImmersion_flat_lfp_forall_mem_iff_ker_ideal_eq_of_point_hilbertFunctionOf n P hPn
    obtain ⟨D3, hD3⟩ :=
      AlgebraicGeometry.HilbertFunctor.exists_point_I_eq_span_of_isClosedImmersion_of_flat_of_locallyOfFinitePresentation n P hPn
    obtain ⟨K₀, _, I₁, hI₁, d₁, hd₁⟩ := hPn
    obtain ⟨m, hm1, hm2, hm3, hm4, hm5⟩ : ∃ m : ℕ, D1 ≤ m ∧ D2 ≤ m ∧ D3 ≤ m ∧ D4 P ≤ m ∧ d₁ ≤ m :=
      ⟨D1 + D2 + D3 + D4 P + d₁, by omega, by omega, by omega, by omega, by omega⟩
    obtain ⟨H, pH, ptH, hbcH, hnatH, hoverH, hpropH, hlfpH, -, -⟩ := hD1 m hm1
    obtain ⟨Φ, hΦ1, hΦ2, hΦ3, hΦ4, hΦ5, hΦ6⟩ := hD2 m hm2
    have hK4 := hD3 m hm3

    haveI : LocallyOfFinitePresentation (𝔓.toProj ≫ ProjSpace.π S n) := by rw [𝔓.toProj_π]; infer_instance
    obtain ⟨I₀, hfg, hI₀, hker⟩ :=
      AlgebraicGeometry.ProjSpace.exists_ideal_fg_forall_ker_ideal_basicOpen_eq_span_of_isClosedImmersion S n X 𝔓.toProj

    obtain ⟨C, ιC, hCci, hClfp, hC⟩ :=
      AlgebraicGeometry.HilbertFunctor.exists_isClosedImmersion_locallyOfFinitePresentation_forall_factors_iff_forall_mem_of_isHomogeneous_of_le_of_fg
        S n (hilbertFunctionOf n P m) hbcH (HS H pH S) (πHS H pH S) (ptHS H pH ptH hoverH S)
        (hnatHS H pH ptH hoverH S hnatH) I₀ hI₀ hfg m
    haveI := hCci
    haveI := hClfp
    haveI : IsProper pH := hpropH
    haveI : LocallyOfFinitePresentation pH := hlfpH

    have KEY : ∀ (S' : Type) [CommRing S'] (s : Spec (CommRingCat.of S') ⟶ Spec (CommRingCat.of S))
        (Z : Scheme.{0}) (ι : Z ⟶ pullback f s), IsClosedImmersion ι → Flat (ι ≫ pullback.snd f s) →
        LocallyOfFinitePresentation (ι ≫ pullback.snd f s) →
        (∀ (k : Type) [Field k] [IsAlgClosed k] (sk : S' →+* k), ∃ d₀ : ℕ, ∀ d : ℕ, d₀ ≤ d →
            ((Scheme.Modules.geomFibreH0Finrank (ι ≫ pullback.snd f s)
              (Nat.rec (motive := fun _ => Z.Modules) (𝟙_ Z.Modules)
                (fun _ M => M ⊗ (Scheme.Modules.pullback (ι ≫ pullback.fst f s)).obj 𝓛X) d) k sk : ℕ) : ℚ) =
              P.eval (d : ℚ)) →
        ∃ p : Point S' n (hilbertFunctionOf n P m),
          (∃ c : Spec (CommRingCat.of S') ⟶ C, c ≫ ιC = (ptHS H pH ptH hoverH S S' (Spec.preimage s).hom p).1) ∧
          (∃ φ : (Φ S' p).1 ≅ Z, φ.hom ≫ ι ≫ emb 𝔓 S' s (Spec.preimage s).hom (preimage_spec s) = (Φ S' p).2) := by
      intro S' _ s Z ι hι hfl hfp hHP
      have hs := preimage_spec s
      letI algS' : Algebra S S' := (Spec.preimage s).hom.toAlgebra
      haveI hj : IsClosedImmersion (emb 𝔓 S' s (Spec.preimage s).hom hs) :=
        isClosedImmersion_emb 𝔓 S' s (Spec.preimage s).hom hs hci
      haveI hιZ : IsClosedImmersion (ι ≫ emb 𝔓 S' s (Spec.preimage s).hom hs) := inferInstance
      have hπ : (ι ≫ emb 𝔓 S' s (Spec.preimage s).hom hs) ≫ ProjSpace.π S' n = ι ≫ pullback.snd f s := by
        rw [Category.assoc, emb_π]
      have hflZ : Flat ((ι ≫ emb 𝔓 S' s (Spec.preimage s).hom hs) ≫ ProjSpace.π S' n) := by rw [hπ]; exact hfl
      have hfpZ : LocallyOfFinitePresentation ((ι ≫ emb 𝔓 S' s (Spec.preimage s).hom hs) ≫ ProjSpace.π S' n) := by
        rw [hπ]; exact hfp

      obtain ⟨J, _, r, hr, hJ⟩ := hD4 S' Z (ι ≫ emb 𝔓 S' s (Spec.preimage s).hom hs) hιZ hflZ hfpZ

      have fib : ∀ (k : Type) [Field k] [IsAlgClosed k] [Algebra S' k]
          (Zk : Scheme.{0}) (ιk : Zk ⟶ Proj (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) k)) (e : Zk ⟶ Z),
          IsClosedImmersion ιk →
          IsPullback e (ιk ≫ ProjSpace.π k n) ((ι ≫ emb 𝔓 S' s (Spec.preimage s).hom hs) ≫ ProjSpace.π S' n)
            (Spec.map (CommRingCat.ofHom (algebraMap S' k))) →
          e ≫ (ι ≫ emb 𝔓 S' s (Spec.preimage s).hom hs) = ιk ≫ ProjSpace.map S' k n →
          ∃ q : Point k n (hilbertFunctionOf n P m), ∀ (d : ℕ), m ≤ d →
            ∀ (F : MvPolynomial (Fin (n + 1)) k) (hF : F.IsHomogeneous d),
              (F ∈ q.I ↔ ∀ i : Fin (n + 1),
              (ιk.app (Proj.basicOpen (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) k) (MvPolynomial.X i)))
                ((Proj.awayToSection (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) k) (MvPolynomial.X i))
                  (HomogeneousLocalization.mk
                    { deg := d
                      num := ⟨F, (MvPolynomial.mem_homogeneousSubmodule d F).mpr hF⟩
                      den := ⟨MvPolynomial.X i ^ d, (MvPolynomial.mem_homogeneousSubmodule d _).mpr (MvPolynomial.isHomogeneous_X_pow i d)⟩
                      den_mem := ⟨d, rfl⟩ })) = 0) := by
        intro k _ _ _ Zk ιk e hιk hpb hcomm
        obtain ⟨j₀, hj₀⟩ := exists_isUnit_of_span_eq_top r hr k
        obtain ⟨Pj, hPjreal, hPj⟩ := hJ j₀

        obtain ⟨q₁, Zk₁, ιk₁, e₁, hιk₁, hpb₁, hcomm₁, hZk₁⟩ := hPj (D4 Pj) le_rfl k hj₀
        have hpb₁' : IsPullback e₁ (ιk₁ ≫ ProjSpace.π k n) (ι ≫ pullback.snd f s)
            (Spec.map (CommRingCat.ofHom (algebraMap S' k))) := by rw [← hπ]; exact hpb₁
        obtain ⟨d₀, hd₀⟩ :=
          AlgebraicGeometry.exists_forall_geomFibreH0Finrank_tensorPow_eq_hilbertFunctionOf_of_point_geomFibre_of_hom
            S f 𝓛X hX₁ 𝔓 S' s (Spec.preimage s).hom hs Z ι (emb 𝔓 S' s (Spec.preimage s).hom hs)
            (emb_π 𝔓 S' s _ hs) (emb_map 𝔓 S' s _ hs) k (algebraMap S' k) Pj (D4 Pj) q₁ Zk₁ ιk₁ hιk₁ e₁ hpb₁'
            hcomm₁.symm hZk₁
        obtain ⟨d₀', hd₀'⟩ := hHP k (algebraMap S' k)
        obtain ⟨Kj, _, Ij, hIj, dj, hdj⟩ := hPjreal
        have hPeq : Pj = P := by
          refine poly_eq_of_eval_eq Pj P (d₀ + d₀' + D4 Pj + dj) fun d hd => ?_
          have a := hd₀ d (by omega)
          have b := hd₀' d (by omega)
          have c := cast_hilbertFunctionOf n Pj Ij dj hdj (D4 Pj) d (by omega) (by omega)
          rw [← c, ← a]
          exact b
        subst hPeq

        obtain ⟨q, Zk₂, ιk₂, e₂, hιk₂, hpb₂, hcomm₂, hZk₂⟩ := hPj m hm4 k hj₀
        obtain ⟨φ, hφ₁, -⟩ :=
          AlgebraicGeometry.ProjSpace.exists_iso_hom_comp_eq_of_isPullback_of_comp_eq_map n S' k Z
            (ι ≫ emb 𝔓 S' s (Spec.preimage s).hom hs) Zk₂ ιk₂ e₂ hpb₂ hcomm₂ Zk ιk e hpb hcomm
        refine ⟨q, fun d hd F hF => ?_⟩
        rw [hZk₂ d hd F hF]
        refine forall_congr' fun i => ?_
        rw [← hφ₁, Scheme.Hom.comp_app]
        change φ.hom.app _ (ιk.app _ _) = 0 ↔ _
        constructor
        · intro h0
          apply (ConcreteCategory.bijective_of_isIso
            (φ.hom.app (ιk ⁻¹ᵁ Proj.basicOpen (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) k) (MvPolynomial.X i)))).1
          rw [h0, map_zero]
        · intro h0
          rw [h0, map_zero]
      obtain ⟨p, hp⟩ := hK4 S' Z (ι ≫ emb 𝔓 S' s (Spec.preimage s).hom hs) hιZ hflZ hfpZ fib

      haveI := (hΦ1 S' p).1
      have hK5 : Scheme.Hom.ker (Φ S' p).2 = Scheme.Hom.ker (ι ≫ emb 𝔓 S' s (Spec.preimage s).hom hs) :=
        AlgebraicGeometry.ProjSpace.eq_ker_of_ideal_basicOpen_eq_span_of_isClosedImmersion n S' Z _ hιZ m _
          (fun i => by rw [hΦ6 S' p i, hp])
      haveI := IsClosedImmersion.isIso_lift (ι ≫ emb 𝔓 S' s (Spec.preimage s).hom hs) (Φ S' p).2 hK5.symm
      refine ⟨p, ?_, ⟨asIso (IsClosedImmersion.lift (ι ≫ emb 𝔓 S' s (Spec.preimage s).hom hs) (Φ S' p).2 hK5.symm.le), ?_⟩⟩
      ·
        refine (hC S' (Spec.preimage s).hom p).mpr ?_
        intro d hd F hFI hF
        rw [hp]
        refine Ideal.subset_span ⟨d, hF, hd, fun i => ?_⟩
        have h0 := app_emb_eq_zero 𝔓 S' s (Spec.preimage s).hom hs hci I₀ hI₀ hker d F hF hFI i
        rw [Scheme.Hom.comp_app]
        change ι.app _ ((emb 𝔓 S' s (Spec.preimage s).hom hs).app _ _) = 0
        rw [h0, map_zero]
      · exact IsClosedImmersion.lift_fac (ι ≫ emb 𝔓 S' s (Spec.preimage s).hom hs) (Φ S' p).2 hK5.symm.le

    let ptF : ∀ (S' : Type) [CommRing S'] (s : Spec (CommRingCat.of S') ⟶ Spec (CommRingCat.of S))
        (Z : Scheme.{0}) (ι : Z ⟶ pullback f s), IsClosedImmersion ι → Flat (ι ≫ pullback.snd f s) →
        LocallyOfFinitePresentation (ι ≫ pullback.snd f s) →
        (∀ (k : Type) [Field k] [IsAlgClosed k] (sk : S' →+* k), ∃ d₀ : ℕ, ∀ d : ℕ, d₀ ≤ d →
            ((Scheme.Modules.geomFibreH0Finrank (ι ≫ pullback.snd f s)
              (Nat.rec (motive := fun _ => Z.Modules) (𝟙_ Z.Modules)
                (fun _ M => M ⊗ (Scheme.Modules.pullback (ι ≫ pullback.fst f s)).obj 𝓛X) d) k sk : ℕ) : ℚ) =
              P.eval (d : ℚ)) →
        SchemeHomOver s (ιC ≫ πHS H pH S) :=
      fun S' _ s Z ι hι hfl hfp hHP =>
        ⟨(KEY S' s Z ι hι hfl hfp hHP).choose_spec.1.choose, by
          rw [← Category.assoc, (KEY S' s Z ι hι hfl hfp hHP).choose_spec.1.choose_spec]
          exact (ptHS H pH ptH hoverH S S' (Spec.preimage s).hom _).2.trans (preimage_spec s).symm⟩
    refine ⟨C, ιC ≫ πHS H pH S, ptF, ?_, ?_, ?_, inferInstance, inferInstance⟩
    ·
      intro S' S'' _ _ ψ' s s'' hs' Z ι hι hfl hfp hHP Z'' ι'' hι'' hfl'' hfp'' hHP'' e hpb hcomm
      have hs := preimage_spec s
      have hs'' := preimage_spec s''

      letI algS' : Algebra S S' := (Spec.preimage s).hom.toAlgebra
      letI alg'' : Algebra S' S'' := ψ'.toAlgebra
      letI algS'' : Algebra S S'' := (Spec.preimage s'').hom.toAlgebra
      have hψeq : (Spec.preimage s'').hom = ψ'.comp (Spec.preimage s).hom := by
        apply HilbR_ringHom_eq_of_specMap_eq
        rw [CommRingCat.ofHom_comp, Spec.map_comp, ← hs, hs']
        exact hs''.symm
      haveI : IsScalarTower S S' S'' := IsScalarTower.of_algebraMap_eq (fun x => by
        change (Spec.preimage s'').hom x = ψ' ((Spec.preimage s).hom x)
        rw [hψeq]; rfl)
      haveI hj : IsClosedImmersion (emb 𝔓 S' s (Spec.preimage s).hom hs) :=
        isClosedImmersion_emb 𝔓 S' s (Spec.preimage s).hom hs hci
      haveI hj'' : IsClosedImmersion (emb 𝔓 S'' s'' (Spec.preimage s'').hom hs'') :=
        isClosedImmersion_emb 𝔓 S'' s'' (Spec.preimage s'').hom hs'' hci

      have hembc : pullback.map f s'' f s (𝟙 X) (Spec.map (CommRingCat.ofHom ψ')) (𝟙 _)
            (by rw [Category.id_comp, Category.comp_id]) (by rw [Category.comp_id, hs']) ≫
          emb 𝔓 S' s (Spec.preimage s).hom hs =
          emb 𝔓 S'' s'' (Spec.preimage s'').hom hs'' ≫ ProjSpace.map S' S'' n := by
        apply (ProjSpace.isPullback_map S S' n).hom_ext
        · rw [Category.assoc, emb_map, Category.assoc, map_comp_map S S' S'' n, emb_map]
          delta pullback.map
          rw [← Category.assoc, pullback.lift_fst, Category.assoc, Category.id_comp]
        · rw [Category.assoc, emb_π, Category.assoc, (ProjSpace.isPullback_map S' S'' n).w, ← Category.assoc, emb_π]
          delta pullback.map
          rw [pullback.lift_snd]

      have hsp := (KEY S' s Z ι hι hfl hfp hHP).choose_spec
      have hsp'' := (KEY S'' s'' Z'' ι'' hι'' hfl'' hfp'' hHP'').choose_spec
      obtain ⟨φ, hφ⟩ := hsp.2
      obtain ⟨φ'', hφ''⟩ := hsp''.2
      haveI := (hΦ1 S' (KEY S' s Z ι hι hfl hfp hHP).choose).1
      obtain ⟨q, hq⟩ := hbcH S' S'' ψ' (KEY S' s Z ι hι hfl hfp hHP).choose
      obtain ⟨eq, hpbq, hcommq⟩ := hΦ3 S' S'' (KEY S' s Z ι hι hfl hfp hHP).choose q hq

      have t : IsPullback φ.hom ((Φ S' (KEY S' s Z ι hι hfl hfp hHP).choose).2 ≫ ProjSpace.π S' n)
          ((ι ≫ emb 𝔓 S' s (Spec.preimage s).hom hs) ≫ ProjSpace.π S' n) (𝟙 _) :=
        IsPullback.of_horiz_isIso ⟨by rw [Category.comp_id, ← Category.assoc, hφ]⟩
      have h₁ := hpbq.paste_horiz t
      rw [Category.comp_id] at h₁
      have h₂ : IsPullback e ((ι'' ≫ emb 𝔓 S'' s'' (Spec.preimage s'').hom hs'') ≫ ProjSpace.π S'' n)
          ((ι ≫ emb 𝔓 S' s (Spec.preimage s).hom hs) ≫ ProjSpace.π S' n)
          (Spec.map (CommRingCat.ofHom (algebraMap S' S''))) := by
        rw [Category.assoc, emb_π, Category.assoc, emb_π]
        exact hpb
      obtain ⟨E, hE₁, -⟩ :=
        AlgebraicGeometry.ProjSpace.exists_iso_hom_comp_eq_of_isPullback_of_comp_eq_map n S' S'' Z
          (ι ≫ emb 𝔓 S' s (Spec.preimage s).hom hs)
          (Φ S'' q).1 (Φ S'' q).2 (eq ≫ φ.hom) h₁ (by rw [Category.assoc, hφ, hcommq])
          Z'' (ι'' ≫ emb 𝔓 S'' s'' (Spec.preimage s'').hom hs'') e h₂
          (by rw [← Category.assoc, ← hcomm, Category.assoc, hembc, Category.assoc])
      have hpq : (KEY S'' s'' Z'' ι'' hι'' hfl'' hfp'' hHP'').choose = q := by
        refine hΦ2 S'' _ q ⟨φ'' ≪≫ E.symm, ?_⟩
        rw [Iso.trans_hom, Iso.symm_hom, Category.assoc, E.inv_comp_eq.mpr hE₁.symm, hφ'']

      change (KEY S'' s'' Z'' ι'' hι'' hfl'' hfp'' hHP'').choose_spec.1.choose =
        Spec.map (CommRingCat.ofHom ψ') ≫ (KEY S' s Z ι hι hfl hfp hHP).choose_spec.1.choose
      rw [← cancel_mono ιC, hsp''.1.choose_spec, Category.assoc, hsp.1.choose_spec, hpq,
        ← hnatHS H pH ptH hoverH S hnatH S' S'' (Spec.preimage s).hom ψ' _ q hq]
      apply pullback.hom_ext
      · rw [ptHS_fst, ptHS_fst]
      · rw [(ptHS H pH ptH hoverH S S'' (Spec.preimage s'').hom q).2,
          (ptHS H pH ptH hoverH S S'' (ψ'.comp (Spec.preimage s).hom) q).2, hψeq]
    ·
      intro S' _ s x
      have hs := preimage_spec s
      letI algS' : Algebra S S' := (Spec.preimage s).hom.toAlgebra

      let v : SchemeHomOver (Spec.map (CommRingCat.ofHom (Spec.preimage s).hom)) (πHS H pH S) :=
        ⟨x.1 ≫ ιC, by rw [Category.assoc]; exact x.2.trans hs⟩
      let p : Point S' n (hilbertFunctionOf n P m) := (ptHS H pH ptH hoverH S S' (Spec.preimage s).hom).symm v
      have hpv : (ptHS H pH ptH hoverH S S' (Spec.preimage s).hom p).1 = x.1 ≫ ιC := by
        change (ptHS H pH ptH hoverH S S' (Spec.preimage s).hom ((ptHS H pH ptH hoverH S S' _).symm v)).1 = _
        rw [Equiv.apply_symm_apply]
      have hcond := (hC S' (Spec.preimage s).hom p).mp ⟨x.1, hpv.symm⟩
      haveI := (hΦ1 S' p).1
      haveI hj : IsClosedImmersion (emb 𝔓 S' s (Spec.preimage s).hom hs) :=
        isClosedImmersion_emb 𝔓 S' s (Spec.preimage s).hom hs hci

      have hle : Scheme.Hom.ker (emb 𝔓 S' s (Spec.preimage s).hom hs) ≤ Scheme.Hom.ker (Φ S' p).2 := by
        refine Scheme.IdealSheafData.le_of_iSup_eq_top
          (fun i : Fin (n + 1) => (⟨Proj.basicOpen (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) S') (MvPolynomial.X i),
            Proj.isAffineOpen_basicOpen (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) S') (MvPolynomial.X i)
              (ProjSpace.X_mem_one S' n i) one_pos⟩ : (PPn S' n).affineOpens))
          (Proj.iSup_basicOpen_eq_top _ (fun i => MvPolynomial.X i) (ProjSpace.irrelevant_le_span_X S' n)) fun i => ?_
        rw [ker_emb_ideal 𝔓 S' s (Spec.preimage s).hom hs hci I₀ hI₀ hker i, hΦ6 S' p i]
        apply Ideal.span_mono
        rintro _ ⟨d, F, hF, hFI, rfl⟩
        by_cases hmd : m ≤ d
        · exact ⟨d, F, hF, hcond d hmd F hFI hF, rfl⟩
        ·
          have hdm : d ≤ m := le_of_lt (not_le.mp hmd)
          have hG : (MvPolynomial.X i ^ (m - d) * F).IsHomogeneous m := by
            have := (MvPolynomial.isHomogeneous_X_pow i (m - d)).mul hF
            rwa [Nat.sub_add_cancel hdm] at this
          refine ⟨m, MvPolynomial.X i ^ (m - d) * F, hG, hcond m le_rfl _ (Ideal.mul_mem_left _ _ hFI) hG, ?_⟩
          congr 1
          apply HomogeneousLocalization.val_injective
          simp only [HomogeneousLocalization.val_mk]
          rw [Localization.mk_eq_mk_iff, Localization.r_iff_exists]
          refine ⟨1, ?_⟩
          simp only [OneMemClass.coe_one, one_mul]
          rw [← mul_assoc, ← pow_add, Nat.add_sub_cancel' hdm]
      let ι : (Φ S' p).1 ⟶ pullback f s := IsClosedImmersion.lift (emb 𝔓 S' s (Spec.preimage s).hom hs) (Φ S' p).2 hle
      have hιfac : ι ≫ emb 𝔓 S' s (Spec.preimage s).hom hs = (Φ S' p).2 := IsClosedImmersion.lift_fac _ _ _
      have hιci : IsClosedImmersion ι := by
        haveI : IsClosedImmersion (ι ≫ emb 𝔓 S' s (Spec.preimage s).hom hs) := by rw [hιfac]; infer_instance
        exact IsClosedImmersion.of_comp ι (emb 𝔓 S' s (Spec.preimage s).hom hs)
      have hsnd : ι ≫ pullback.snd f s = (Φ S' p).2 ≫ ProjSpace.π S' n := by
        rw [← emb_π 𝔓 S' s (Spec.preimage s).hom hs, ← Category.assoc, hιfac]
      have hιfl : Flat (ι ≫ pullback.snd f s) := by rw [hsnd]; exact (hΦ1 S' p).2.1
      have hιfp : LocallyOfFinitePresentation (ι ≫ pullback.snd f s) := by rw [hsnd]; exact (hΦ1 S' p).2.2
      have hιHP : (∀ (k : Type) [Field k] [IsAlgClosed k] (sk : S' →+* k), ∃ d₀ : ℕ, ∀ d : ℕ, d₀ ≤ d →
            ((Scheme.Modules.geomFibreH0Finrank (ι ≫ pullback.snd f s)
              (Nat.rec (motive := fun _ => (Φ S' p).1.Modules) (𝟙_ (Φ S' p).1.Modules)
                (fun _ M => M ⊗ (Scheme.Modules.pullback (ι ≫ pullback.fst f s)).obj 𝓛X) d) k sk : ℕ) : ℚ) =
              P.eval (d : ℚ)) := by
        intro k _ _ sk
        letI : Algebra S' k := sk.toAlgebra
        obtain ⟨q, hq⟩ := hbcH S' k sk p
        obtain ⟨eq, hpbq, hcommq⟩ := hΦ3 S' k p q hq
        obtain ⟨d₀, hd₀⟩ :=
          AlgebraicGeometry.exists_forall_geomFibreH0Finrank_tensorPow_eq_hilbertFunctionOf_of_point_geomFibre_of_hom
            S f 𝓛X hX₁ 𝔓 S' s (Spec.preimage s).hom hs (Φ S' p).1 ι (emb 𝔓 S' s (Spec.preimage s).hom hs)
            (emb_π 𝔓 S' s _ hs) (emb_map 𝔓 S' s _ hs) k sk P m q (Φ k q).1 (Φ k q).2 (hΦ1 k q).1 eq
            (by rw [hsnd]; exact hpbq) (by rw [hιfac]; exact hcommq.symm) (hΦ5 k q)
        refine ⟨d₀ + m + d₁, fun d hd => ?_⟩
        rw [hd₀ d (by omega)]
        exact cast_hilbertFunctionOf n P I₁ d₁ hd₁ m d (by omega) (by omega)
      refine ⟨(Φ S' p).1, ι, hιci, hιfl, hιfp, hιHP, ?_⟩

      have hspec := (KEY S' s (Φ S' p).1 ι hιci hιfl hιfp hιHP).choose_spec
      obtain ⟨φZ, hφZ⟩ := hspec.2
      have hpZ : (KEY S' s (Φ S' p).1 ι hιci hιfl hιfp hιHP).choose = p := by
        refine hΦ2 S' _ p ⟨φZ, ?_⟩
        rw [← hιfac]
        exact hφZ
      apply Subtype.ext
      change (KEY S' s (Φ S' p).1 ι hιci hιfl hιfp hιHP).choose_spec.1.choose = x.1
      rw [← cancel_mono ιC, hspec.1.choose_spec, hpZ, hpv]
    ·
      intro S' _ s Z Z' ι ι' hι hι' hfl hfl' hfp hfp' hHP hHP' heq
      have hs := preimage_spec s
      haveI hj : IsClosedImmersion (emb 𝔓 S' s (Spec.preimage s).hom hs) :=
        isClosedImmersion_emb 𝔓 S' s (Spec.preimage s).hom hs hci
      have hsp := (KEY S' s Z ι hι hfl hfp hHP).choose_spec
      have hsp' := (KEY S' s Z' ι' hι' hfl' hfp' hHP').choose_spec
      obtain ⟨φ, hφ⟩ := hsp.2
      obtain ⟨φ', hφ'⟩ := hsp'.2
      have hcc : (KEY S' s Z ι hι hfl hfp hHP).choose_spec.1.choose =
          (KEY S' s Z' ι' hι' hfl' hfp' hHP').choose_spec.1.choose := congrArg Subtype.val heq
      have hpt : (ptHS H pH ptH hoverH S S' (Spec.preimage s).hom (KEY S' s Z ι hι hfl hfp hHP).choose).1 =
          (ptHS H pH ptH hoverH S S' (Spec.preimage s).hom (KEY S' s Z' ι' hι' hfl' hfp' hHP').choose).1 := by
        rw [← hsp.1.choose_spec, ← hsp'.1.choose_spec, hcc]
      have hpp : (KEY S' s Z ι hι hfl hfp hHP).choose = (KEY S' s Z' ι' hι' hfl' hfp' hHP').choose :=
        (ptHS H pH ptH hoverH S S' (Spec.preimage s).hom).injective (Subtype.ext hpt)
      have hk : Scheme.Hom.ker (ι ≫ emb 𝔓 S' s (Spec.preimage s).hom hs) =
          Scheme.Hom.ker (ι' ≫ emb 𝔓 S' s (Spec.preimage s).hom hs) := by
        have e1 : Scheme.Hom.ker (Φ S' (KEY S' s Z ι hι hfl hfp hHP).choose).2 =
            Scheme.Hom.ker (ι ≫ emb 𝔓 S' s (Spec.preimage s).hom hs) := by
          rw [← hφ, Scheme.Hom.ker_comp_of_isIso]
        have e2 : Scheme.Hom.ker (Φ S' (KEY S' s Z' ι' hι' hfl' hfp' hHP').choose).2 =
            Scheme.Hom.ker (ι' ≫ emb 𝔓 S' s (Spec.preimage s).hom hs) := by
          rw [← hφ', Scheme.Hom.ker_comp_of_isIso]
        rw [← e1, ← e2, hpp]
      haveI : IsClosedImmersion (ι ≫ emb 𝔓 S' s (Spec.preimage s).hom hs) := inferInstance
      haveI : IsClosedImmersion (ι' ≫ emb 𝔓 S' s (Spec.preimage s).hom hs) := inferInstance
      haveI := IsClosedImmersion.isIso_lift (ι' ≫ emb 𝔓 S' s (Spec.preimage s).hom hs)
        (ι ≫ emb 𝔓 S' s (Spec.preimage s).hom hs) hk.symm
      refine ⟨asIso (IsClosedImmersion.lift (ι' ≫ emb 𝔓 S' s (Spec.preimage s).hom hs)
        (ι ≫ emb 𝔓 S' s (Spec.preimage s).hom hs) hk.symm.le), ?_⟩
      have hfac := IsClosedImmersion.lift_fac (ι' ≫ emb 𝔓 S' s (Spec.preimage s).hom hs)
        (ι ≫ emb 𝔓 S' s (Spec.preimage s).hom hs) hk.symm.le
      rw [← Category.assoc] at hfac
      exact (cancel_mono (emb 𝔓 S' s (Spec.preimage s).hom hs)).mp hfac
  ·
    have hno : ∀ (S' : Type) [CommRing S'] (s : Spec (CommRingCat.of S') ⟶ Spec (CommRingCat.of S))
        (Z : Scheme.{0}) (ι : Z ⟶ pullback f s), IsClosedImmersion ι → Flat (ι ≫ pullback.snd f s) →
        LocallyOfFinitePresentation (ι ≫ pullback.snd f s) →
        (∀ (k : Type) [Field k] [IsAlgClosed k] (sk : S' →+* k), ∃ d₀ : ℕ, ∀ d : ℕ, d₀ ≤ d →
            ((Scheme.Modules.geomFibreH0Finrank (ι ≫ pullback.snd f s)
              (Nat.rec (motive := fun _ => Z.Modules) (𝟙_ Z.Modules)
                (fun _ M => M ⊗ (Scheme.Modules.pullback (ι ≫ pullback.fst f s)).obj 𝓛X) d) k sk : ℕ) : ℚ) =
              P.eval (d : ℚ)) →
        IsEmpty ↥(Spec (CommRingCat.of S')) := by
      intro S' _ s Z ι hι hfl hfp hHP
      by_contra hne
      rw [not_isEmpty_iff] at hne
      obtain ⟨x⟩ := hne
      apply hPn

      let k : Type := AlgebraicClosure (FractionRing (S' ⧸ x.asIdeal))
      letI : Algebra S' k :=
        ((algebraMap (FractionRing (S' ⧸ x.asIdeal)) k).comp
          ((algebraMap (S' ⧸ x.asIdeal) (FractionRing (S' ⧸ x.asIdeal))).comp (Ideal.Quotient.mk x.asIdeal))).toAlgebra
      have hs := preimage_spec s
      letI algS' : Algebra S S' := (Spec.preimage s).hom.toAlgebra
      haveI hj : IsClosedImmersion (emb 𝔓 S' s (Spec.preimage s).hom hs) :=
        isClosedImmersion_emb 𝔓 S' s (Spec.preimage s).hom hs hci
      haveI hιZ : IsClosedImmersion (ι ≫ emb 𝔓 S' s (Spec.preimage s).hom hs) := inferInstance
      have hπ : (ι ≫ emb 𝔓 S' s (Spec.preimage s).hom hs) ≫ ProjSpace.π S' n = ι ≫ pullback.snd f s := by
        rw [Category.assoc, emb_π]
      have hflZ : Flat ((ι ≫ emb 𝔓 S' s (Spec.preimage s).hom hs) ≫ ProjSpace.π S' n) := by rw [hπ]; exact hfl
      have hfpZ : LocallyOfFinitePresentation ((ι ≫ emb 𝔓 S' s (Spec.preimage s).hom hs) ≫ ProjSpace.π S' n) := by
        rw [hπ]; exact hfp
      obtain ⟨J, _, r, hr, hJ⟩ := hD4 S' Z (ι ≫ emb 𝔓 S' s (Spec.preimage s).hom hs) hιZ hflZ hfpZ
      obtain ⟨j₀, hj₀⟩ := exists_isUnit_of_span_eq_top r hr k
      obtain ⟨Pj, hPjreal, hPj⟩ := hJ j₀
      obtain ⟨q₁, Zk₁, ιk₁, e₁, hιk₁, hpb₁, hcomm₁, hZk₁⟩ := hPj (D4 Pj) le_rfl k hj₀
      have hpb₁' : IsPullback e₁ (ιk₁ ≫ ProjSpace.π k n) (ι ≫ pullback.snd f s)
          (Spec.map (CommRingCat.ofHom (algebraMap S' k))) := by rw [← hπ]; exact hpb₁
      obtain ⟨d₀, hd₀⟩ :=
        AlgebraicGeometry.exists_forall_geomFibreH0Finrank_tensorPow_eq_hilbertFunctionOf_of_point_geomFibre_of_hom
          S f 𝓛X hX₁ 𝔓 S' s (Spec.preimage s).hom hs Z ι (emb 𝔓 S' s (Spec.preimage s).hom hs)
          (emb_π 𝔓 S' s _ hs) (emb_map 𝔓 S' s _ hs) k (algebraMap S' k) Pj (D4 Pj) q₁ Zk₁ ιk₁ hιk₁ e₁ hpb₁'
          hcomm₁.symm hZk₁
      obtain ⟨d₀', hd₀'⟩ := hHP k (algebraMap S' k)
      obtain ⟨Kj, hKj, Ij, hIj, dj, hdj⟩ := hPjreal
      have hPeq : Pj = P := by
        refine poly_eq_of_eval_eq Pj P (d₀ + d₀' + D4 Pj + dj) fun d hd => ?_
        have a := hd₀ d (by omega)
        have b := hd₀' d (by omega)
        have c := cast_hilbertFunctionOf n Pj Ij dj hdj (D4 Pj) d (by omega) (by omega)
        rw [← c, ← a]
        exact b
      subst hPeq
      exact ⟨Kj, hKj, Ij, hIj, dj, hdj⟩
    refine ⟨∅, Scheme.emptyTo _, fun S' _ s Z ι hι hfl hfp hHP =>
        haveI := hno S' s Z ι hι hfl hfp hHP
        ⟨(isInitialOfIsEmpty (X := Spec (CommRingCat.of S'))).to ∅, isInitialOfIsEmpty.hom_ext _ _⟩,
      ?_, ?_, ?_, inferInstance, inferInstance⟩
    · intro S' S'' _ _ ψ' s s'' hs' Z ι hι hfl hfp hHP Z'' ι'' hι'' hfl'' hfp'' hHP'' e hpb hcomm
      haveI := hno S'' s'' Z'' ι'' hι'' hfl'' hfp'' hHP''
      exact isInitialOfIsEmpty.hom_ext _ _
    · intro S' _ s x
      haveI hE : IsEmpty ↥(Spec (CommRingCat.of S')) := x.1.base.hom.1.isEmpty
      haveI : IsEmpty ↥(pullback f s) := (pullback.snd f s).base.hom.1.isEmpty
      refine ⟨pullback f s, 𝟙 _, inferInstance, ?_, ?_, ?_, ?_⟩
      · rw [Category.id_comp]; infer_instance
      · rw [Category.id_comp]; infer_instance
      · intro k _ _ sk
        exact (hE.false (⟨RingHom.ker sk, RingHom.ker_isPrime sk⟩ : ↥(Spec (CommRingCat.of S')))).elim
      · exact Subtype.ext (isInitialOfIsEmpty.hom_ext _ _)
    · intro S' _ s Z Z' ι ι' hι hι' hfl hfl' hfp hfp' hHP hHP' heq
      haveI := hno S' s Z ι hι hfl hfp hHP
      haveI : IsEmpty ↥Z := (ι ≫ pullback.snd f s).base.hom.1.isEmpty
      haveI : IsEmpty ↥Z' := (ι' ≫ pullback.snd f s).base.hom.1.isEmpty
      exact ⟨(isInitialOfIsEmpty (X := Z)).uniqueUpToIso (isInitialOfIsEmpty (X := Z')),
        isInitialOfIsEmpty.hom_ext _ _⟩

end Main

end HilbP

end

theorem solution
    (S : Type) [CommRing S] {X : Scheme.{0}} (f : X ⟶ Spec (CommRingCat.of S))
    [Flat f] [LocallyOfFinitePresentation f]
    (𝓛X : X.Modules) (hX₁ : Scheme.Modules.IsInvertible 𝓛X) (hX₂ : Scheme.Modules.ClosedImmersionBySections 𝓛X f)
    (P : Polynomial ℚ) :
    ∃ (C : Scheme.{0}) (πC : C ⟶ Spec (CommRingCat.of S))
      (pt : ∀ (S' : Type) [CommRing S'] (s : Spec (CommRingCat.of S') ⟶ Spec (CommRingCat.of S))
        (Z : Scheme.{0}) (ι : Z ⟶ pullback f s), IsClosedImmersion ι → Flat (ι ≫ pullback.snd f s) →
          LocallyOfFinitePresentation (ι ≫ pullback.snd f s) →
          (∀ (k : Type) [Field k] [IsAlgClosed k] (sk : S' →+* k), ∃ d₀ : ℕ, ∀ d : ℕ, d₀ ≤ d →
            ((Scheme.Modules.geomFibreH0Finrank (ι ≫ pullback.snd f s)
              (Nat.rec (motive := fun _ => Z.Modules) (𝟙_ Z.Modules)
                (fun _ M => M ⊗ (Scheme.Modules.pullback (ι ≫ pullback.fst f s)).obj 𝓛X) d) k sk : ℕ) : ℚ) =
              P.eval (d : ℚ)) →
          SchemeHomOver s πC),

      (∀ (S' S'' : Type) [CommRing S'] [CommRing S''] (ψ : S' →+* S'')
          (s : Spec (CommRingCat.of S') ⟶ Spec (CommRingCat.of S)) (s'' : Spec (CommRingCat.of S'') ⟶ Spec (CommRingCat.of S))
          (hs : Spec.map (CommRingCat.ofHom ψ) ≫ s = s'')
          (Z : Scheme.{0}) (ι : Z ⟶ pullback f s) (hι : IsClosedImmersion ι) (hfl : Flat (ι ≫ pullback.snd f s))
          (hfp : LocallyOfFinitePresentation (ι ≫ pullback.snd f s))
          (hHP : (∀ (k : Type) [Field k] [IsAlgClosed k] (sk : S' →+* k), ∃ d₀ : ℕ, ∀ d : ℕ, d₀ ≤ d →
            ((Scheme.Modules.geomFibreH0Finrank (ι ≫ pullback.snd f s)
              (Nat.rec (motive := fun _ => Z.Modules) (𝟙_ Z.Modules)
                (fun _ M => M ⊗ (Scheme.Modules.pullback (ι ≫ pullback.fst f s)).obj 𝓛X) d) k sk : ℕ) : ℚ) =
              P.eval (d : ℚ)))
          (Z'' : Scheme.{0}) (ι'' : Z'' ⟶ pullback f s'') (hι'' : IsClosedImmersion ι'') (hfl'' : Flat (ι'' ≫ pullback.snd f s''))
          (hfp'' : LocallyOfFinitePresentation (ι'' ≫ pullback.snd f s''))
          (hHP'' : (∀ (k : Type) [Field k] [IsAlgClosed k] (sk : S'' →+* k), ∃ d₀ : ℕ, ∀ d : ℕ, d₀ ≤ d →
            ((Scheme.Modules.geomFibreH0Finrank (ι'' ≫ pullback.snd f s'')
              (Nat.rec (motive := fun _ => Z''.Modules) (𝟙_ Z''.Modules)
                (fun _ M => M ⊗ (Scheme.Modules.pullback (ι'' ≫ pullback.fst f s'')).obj 𝓛X) d) k sk : ℕ) : ℚ) =
              P.eval (d : ℚ)))
          (e : Z'' ⟶ Z),
          IsPullback e (ι'' ≫ pullback.snd f s'') (ι ≫ pullback.snd f s) (Spec.map (CommRingCat.ofHom ψ)) →
          ι'' ≫ pullback.map f s'' f s (𝟙 X) (Spec.map (CommRingCat.ofHom ψ)) (𝟙 _)
              (by rw [Category.id_comp, Category.comp_id]) (by rw [Category.comp_id, hs]) = e ≫ ι →
          (pt S'' s'' Z'' ι'' hι'' hfl'' hfp'' hHP'').1 = Spec.map (CommRingCat.ofHom ψ) ≫ (pt S' s Z ι hι hfl hfp hHP).1) ∧

      (∀ (S' : Type) [CommRing S'] (s : Spec (CommRingCat.of S') ⟶ Spec (CommRingCat.of S)) (x : SchemeHomOver s πC),
        ∃ (Z : Scheme.{0}) (ι : Z ⟶ pullback f s) (hι : IsClosedImmersion ι) (hfl : Flat (ι ≫ pullback.snd f s))
          (hfp : LocallyOfFinitePresentation (ι ≫ pullback.snd f s))
          (hHP : (∀ (k : Type) [Field k] [IsAlgClosed k] (sk : S' →+* k), ∃ d₀ : ℕ, ∀ d : ℕ, d₀ ≤ d →
            ((Scheme.Modules.geomFibreH0Finrank (ι ≫ pullback.snd f s)
              (Nat.rec (motive := fun _ => Z.Modules) (𝟙_ Z.Modules)
                (fun _ M => M ⊗ (Scheme.Modules.pullback (ι ≫ pullback.fst f s)).obj 𝓛X) d) k sk : ℕ) : ℚ) =
              P.eval (d : ℚ))),
          pt S' s Z ι hι hfl hfp hHP = x) ∧

      (∀ (S' : Type) [CommRing S'] (s : Spec (CommRingCat.of S') ⟶ Spec (CommRingCat.of S))
          (Z Z' : Scheme.{0}) (ι : Z ⟶ pullback f s) (ι' : Z' ⟶ pullback f s)
          (hι : IsClosedImmersion ι) (hι' : IsClosedImmersion ι')
          (hfl : Flat (ι ≫ pullback.snd f s)) (hfl' : Flat (ι' ≫ pullback.snd f s))
          (hfp : LocallyOfFinitePresentation (ι ≫ pullback.snd f s)) (hfp' : LocallyOfFinitePresentation (ι' ≫ pullback.snd f s))
          (hHP : (∀ (k : Type) [Field k] [IsAlgClosed k] (sk : S' →+* k), ∃ d₀ : ℕ, ∀ d : ℕ, d₀ ≤ d →
            ((Scheme.Modules.geomFibreH0Finrank (ι ≫ pullback.snd f s)
              (Nat.rec (motive := fun _ => Z.Modules) (𝟙_ Z.Modules)
                (fun _ M => M ⊗ (Scheme.Modules.pullback (ι ≫ pullback.fst f s)).obj 𝓛X) d) k sk : ℕ) : ℚ) =
              P.eval (d : ℚ)))
          (hHP' : (∀ (k : Type) [Field k] [IsAlgClosed k] (sk : S' →+* k), ∃ d₀ : ℕ, ∀ d : ℕ, d₀ ≤ d →
            ((Scheme.Modules.geomFibreH0Finrank (ι' ≫ pullback.snd f s)
              (Nat.rec (motive := fun _ => Z'.Modules) (𝟙_ Z'.Modules)
                (fun _ M => M ⊗ (Scheme.Modules.pullback (ι' ≫ pullback.fst f s)).obj 𝓛X) d) k sk : ℕ) : ℚ) =
              P.eval (d : ℚ))),
        pt S' s Z ι hι hfl hfp hHP = pt S' s Z' ι' hι' hfl' hfp' hHP' → ∃ e : Z ≅ Z', e.hom ≫ ι' = ι) ∧
      IsProper πC ∧ LocallyOfFinitePresentation πC :=
  HilbP.main S f 𝓛X hX₁ hX₂ P

end S_AlgebraicGeometry_exists_scheme_represents_flat_lfp_closedSubscheme_hilbertPolynomial_eq_of_closedImmersionBySections
end P2MW
export P2MW.S_AlgebraicGeometry_exists_scheme_represents_flat_lfp_closedSubscheme_hilbertPolynomial_eq_of_closedImmersionBySections (solution)
