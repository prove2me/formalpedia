-- Prove2me | solution 1 for AlgebraicGeometry.HilbertFunctor.exists_closedImmersion_flat_lfp_forall_mem_iff_ker_ideal_eq_of_point_hilbertFunctionOf
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:02.935278+00:00
-- url     : https://prove2.me/submissions/1ca5bc12-3064-5c37-9695-be3e7a047c86

import Definitions.Def_AlgebraicGeometry_ProjSpace
import Definitions.Def_AlgebraicGeometry_HilbertFunctor
import Theorems.Thm_AlgebraicGeometry_ProjSpace_exists_idealSheafData_ideal_basicOpen_eq_span
import Theorems.Thm_AlgebraicGeometry_HilbertFunctor_Point_flat_comp_of_ideal_basicOpen_eq_span
import Theorems.Thm_AlgebraicGeometry_ProjSpace_locallyOfFinitePresentation_comp_of_fg_of_ideal_basicOpen_eq_span
import Theorems.Thm_AlgebraicGeometry_ProjSpace_eq_comap_map_of_ideal_basicOpen_eq_span
import Theorems.Thm_AlgebraicGeometry_HilbertFunctor_exists_forall_mem_of_forall_X_pow_mul_mem_hilbertFunctionOf
import Theorems.Thm_AlgebraicGeometry_ProjSpace_awayToSection_mk_mem_span_iff_exists_X_pow_mul_mem
import Theorems.Thm_AlgebraicGeometry_ProjSpace_eq_ker_of_ideal_basicOpen_eq_span_of_isClosedImmersion
import Theorems.Thm_AlgebraicGeometry_ProjSpace_exists_iso_hom_comp_eq_of_isPullback_of_comp_eq_map
import Theorems.Thm_AlgebraicGeometry_HilbertFunctor_exists_point_I_eq_span_of_isClosedImmersion_of_flat_of_locallyOfFinitePresentation
import Theorems.Thm_AlgebraicGeometry_ProjSpace_isPullback_map
import Theorems.Thm_AlgebraicGeometry_HilbertFunctor_Point_I_eq_span_of_forall_finrank_piece_succ_le
import Theorems.Thm_MvPolynomial_exists_forall_finrank_piece_succ_le_eval_and_exists_eq_eval
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_HilbertFunctor_exists_closedImmersion_flat_lfp_forall_mem_iff_ker_ideal_eq_of_point_hilbertFunctionOf
p2m_attr_erase "instance" "AlgebraicGeometry.OModulePresheaf.isScalarTower AlgebraicGeometry.Scheme.OrderedAffineCover.instLinearOrder AlgebraicGeometry.OModulePresheaf.module AlgebraicGeometry.Scheme.OrderedAffineCover.instFintype AlgebraicGeometry.Scheme.OrderedAffineCover.instFintypeIdx AlgebraicGeometry.OModulePresheaf.addCommGroup AlgebraicGeometry.Scheme.OrderedAffineCover.instDecidableEqIdx AlgebraicGeometry.OModulePresheaf.moduleSections TwoChartCech.Sections.M0_moduleA TwoChartCech.Sections.M1_module TwoChartCech.Cover.A01_algebra TwoChartCech.Cover.A0_algebra TwoChartCech.Cover.A1_commRing TwoChartCech.Cover.A1_algebra TwoChartCech.Sections.M01_module TwoChartCech.Sections.M0_addCommGroup TwoChartCech.Sections.M0_tower TwoChartCech.Sections.M01_addCommGroup TwoChartCech.Cover.A0_commRing TwoChartCech.Sections.M1_tower TwoChartCech.Sections.M01_moduleA TwoChartCech.Sections.M0_module TwoChartCech.Sections.M1_moduleA TwoChartCech.Sections.M1_addCommGroup TwoChartCech.Cover.A01_commRing TwoChartCech.Sections.M01_tower CoherentBaseChange.TwoTermComplex.C0_module CoherentBaseChange.TwoTermComplex.C0_addCommGroup CoherentBaseChange.TwoTermComplex.C1_module CoherentBaseChange.TwoTermComplex.C1_addCommGroup CoherentBaseChange.TwoTermComplex.C0_free CoherentBaseChange.TwoTermComplex.C1_finite CoherentBaseChange.TwoTermComplex.C0_finite CoherentBaseChange.TwoTermComplex.C1_free AlgebraicGeometry.ProjSpace.twistObj.addCommGroup AlgebraicGeometry.ProjSpace.twistFam.module AlgebraicGeometry.ProjSpace.twistObj.module AlgebraicGeometry.ProjSpace.twistObj.moduleSections AlgebraicGeometry.ProjSpace.twistFam.addCommGroup ProjSpaceCech.GradedModule.H.module"
p2m_attr_erase "instance" "ProjSpaceCech.GradedModule.H.addCommGroup ProjSpaceCech.GradedModule.sec.instAdd ProjSpaceCech.GradedModule.sec.instNeg ProjSpaceCech.GradedModule.acg ProjSpaceCech.GradedModule.Frac.setoid ProjSpaceCech.GradedModule.modR ProjSpaceCech.GradedModule.sec.instModule ProjSpaceCech.GradedModule.sec.instAddCommGroup ProjSpaceCech.GradedModule.sec.instZero ProjSpaceCech.GradedModule.Presentation.fJ ProjSpaceCech.GradedModule.sec.instSMul ProjSpaceCech.Twist.H.module ProjSpaceCech.Idx.instFintype ProjSpaceCech.Twist.H.addCommGroup ProjSpaceCech.Idx.instDecidableEq ProjSpaceCech.Twist.Mon.instDecidableEq ProjSpaceCech.Twist.cochain.instAddCommGroup ProjSpaceCech.Twist.cochain.instModule AlgebraicGeometry.OModulePresheaf.instSubsingletonObjZero PresheafOfModules.instMonoidalClosed PresheafOfModules.InternalHom.instModuleCarrierObjOppositeCommRingCatSubtypePiFamilyMemAddSubgroupNaturalFamilies PresheafOfModules.InternalHom.instModuleCarrierObjOppositeRingCatCompCommRingCatForget₂RingHomCarrierCarrierAbPresheaf PresheafOfModules.InternalHom.instSMulCarrierObjOppositeCommRingCatSubtypePiFamilyMemAddSubgroupNaturalFamilies AlgebraicGeometry.Scheme.PresheafOfModules.symmetricCategory SheafOfModules.instFaithfulRingSheafPModToPMod SheafOfModules.symmetricCategory AlgebraicGeometry.Scheme.PresheafOfModules.monoidalCategory AlgebraicGeometry.Scheme.PresheafOfModules.monoidalClosed SheafOfModules.instFullRingSheafPModToPMod SheafOfModules.monoidalCategory AlgebraicGeometry.Scheme.Modules.symmetricCategory SheafOfModules.monoidalClosed SheafOfModules.instIsLocalizationPModRingSheafSheafifyFunctorPresheafW SheafOfModules.sheafifyFunctor_monoidal AlgebraicGeometry.Scheme.Modules.monoidalClosed AlgebraicGeometry.instMonoidalPresheafOfModulesModulesSheafify AlgebraicGeometry.Scheme.Modules.monoidalCategory PresheafOfModules.PullbackMonoidal.pullback_monoidal PresheafOfModules.PullbackMonoidal.isIso_δ PresheafOfModules.pushforward_laxMonoidal"
p2m_attr_erase "instance" "PresheafOfModules.PullbackMonoidal.isIso_η PresheafOfModules.free_monoidal PresheafOfModules.restrictScalars_laxMonoidal PresheafOfModules.PullbackMonoidal.isIso_δ_gS PresheafOfModules.pullback_oplaxMonoidal PresheafOfModules.PullbackMonoidal.instPreservesColimitsOfSizeCompOppositeCommRingCatRingCatForget₂RingHomCarrierCarrierPb PresheafOfModules.pullback_monoidal' AlgebraicGeometry.Scheme.Modules.preservesBinaryProducts_opensMap AlgebraicGeometry.Scheme.Modules.pullback_monoidal AlgebraicGeometry.Scheme.Modules.sheafify_isLocalization' AlgebraicGeometry.Scheme.Modules.preservesTerminal_opensMap AlgebraicGeometry.Scheme.Modules.pullback₀_monoidal AlgebraicGeometry.Scheme.Modules.preservesFiniteProducts_opensMap AlgebraicGeometry.Scheme.Modules.instLiftingPresheafOfModulesSheafifyPresheafWOpensCarrierCarrierCommRingCatGrothendieckTopologyObjFunctorOppositeIsSheafSheafCompPullback₀Pullback AlgebraicGeometry.Scheme.Hom.opensMapFinal AlgebraicGeometry.RelPicard.RigidifiedLineBundle.setoid AlgebraicGeometry.RelPicard.RigidifiedLineBundle.instInhabited AlgebraicGeometry.OModulePresheaf.Leray.relAltC_scalarTower AlgebraicGeometry.OModulePresheaf.Leray.ker_relAltd_modΓ AlgebraicGeometry.OModulePresheaf.Leray.relAltC_modΓ AlgebraicGeometry.OModulePresheaf.Leray.biC_abGrp AlgebraicGeometry.OModulePresheaf.Leray.relAltH_modΓ AlgebraicGeometry.OModulePresheaf.Leray.ker_relAltd_smul AlgebraicGeometry.OModulePresheaf.Leray.relAltH_scalarTower AlgebraicGeometry.OModulePresheaf.Leray.relAltH_smul AlgebraicGeometry.OModulePresheaf.Leray.biC_module AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instDecidableEqIdx AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instFintype AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instLinearOrder AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instFintypeIdx DoubleComplex.instModuleE₂I DoubleComplex.Bounded.modR DoubleComplex.instModuleE₂II DoubleComplex.instAddCommGroupE₂II DoubleComplex.Bounded.abGrp DoubleComplex.instAddCommGroupE₂I AlgebraicGeometry.Scheme.Modules.GlueOfCocycle.instSMulCarrierObjOppositeOpensCarrierCarrierCommRingCatPresheafOpOpensSubtypeForallMinMemAddSubgroupFamilies AlgebraicGeometry.Scheme.Modules.GlueOfCocycle.instModulePreGlue AlgebraicGeometry.Scheme.Modules.GlueOfCocycle.instModuleCarrierObjOppositeOpensCarrierCarrierCommRingCatPresheafOpOpensSubtypeForallMinMemAddSubgroupFamilies IsDirectLimit.Module.instDirectLimitCoeLinearMapIdOfOfNonempty"
p2m_attr_erase "instance" "AlgebraicGeometry.SubalgebraStages.compactSpace_pullback AlgebraicGeometry.SubalgebraStages.quasiSeparatedSpace_pullback AlgebraicGeometry.SubalgebraStages.compactSpace_obj AlgebraicGeometry.SubalgebraStages.quasiSeparatedSpace_obj AlgebraicGeometry.SubalgebraStages.quasiCompact_snd AlgebraicGeometry.SubalgebraStages.isAffineHom_leg AlgebraicGeometry.SubalgebraStages.isAffineHom_trans AlgebraicGeometry.SubalgebraStages.isAffineHom_diagram_map AlgebraicGeometry.SubalgebraStages.quasiSeparated_snd AlgebraicGeometry.SubalgebraStages.isCofiltered_op"
p2m_attr_erase "simp" "AlgebraicGeometry.Scheme.OrderedAffineCover.mk.injEq AlgebraicGeometry.OModulePresheaf.mk.sizeOf_spec AlgebraicGeometry.Scheme.OrderedAffineCover.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.mk.injEq AlgebraicGeometry.Scheme.TwoAffineOpenCover.mk.injEq AlgebraicGeometry.Scheme.TwoAffineOpenCover.mk.sizeOf_spec AlgebraicGeometry.Scheme.TwoAffineOpenCover.pullback_U1 AlgebraicGeometry.Scheme.TwoAffineOpenCover.pullback_U0 TwoChartCech.Sections.mk.injEq TwoChartCech.Cover.mk.injEq TwoChartCech.GrothendieckComplex.mk.injEq TwoChartCech.Sections.mk.sizeOf_spec TwoChartCech.Cover.mk.sizeOf_spec TwoChartCech.Cover.lineBundle_r0_apply TwoChartCech.GrothendieckComplex.mk.sizeOf_spec TwoChartCech.Cover.lineBundle_r1_apply CoherentBaseChange.TwoTermComplex.mk.sizeOf_spec CoherentBaseChange.TwoTermComplex.mk.injEq AlgebraicGeometry.ProjSpace.twistObj.mk.injEq AlgebraicGeometry.ProjSpace.twistObj.zero_val AlgebraicGeometry.ProjSpace.twistObj.add_val AlgebraicGeometry.ProjSpace.twist_res_val AlgebraicGeometry.ProjSpace.twist_smul_val AlgebraicGeometry.ProjSpace.twistGradeToObj_val AlgebraicGeometry.ProjSpace.twistObj.smul_val AlgebraicGeometry.ProjSpace.twistGradeEquiv_apply_val AlgebraicGeometry.ProjSpace.twistObj.mk.sizeOf_spec ProjSpaceCech.GradedModule.mk.injEq ProjSpaceCech.GradedModule.mk.sizeOf_spec ProjSpaceCech.GradedModule.Frac.mk.sizeOf_spec ProjSpaceCech.GradedModule.Presentation.mk.injEq ProjSpaceCech.GradedModule.Frac.mk.injEq ProjSpaceCech.GradedModule.Presentation.mk.sizeOf_spec ProjSpaceCech.GradedModule.Hom.shift_toLinearMap ProjSpaceCech.GradedModule.Hom.mk.sizeOf_spec ProjSpaceCech.GradedModule.Hom.mk.injEq AlgebraicGeometry.OModulePresheaf.Hom.mk.injEq AlgebraicGeometry.OModulePresheaf.Hom.id_app AlgebraicGeometry.OModulePresheaf.AffHom.appSections_apply AlgebraicGeometry.OModulePresheaf.AffHom.comp_app"
p2m_attr_erase "simp" "AlgebraicGeometry.OModulePresheaf.AffSES.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.AffHom.kerMap_coe AlgebraicGeometry.OModulePresheaf.AffHom.id_app AlgebraicGeometry.OModulePresheaf.Hom.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.Hom.toAffHom_app AlgebraicGeometry.OModulePresheaf.SES.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.AffHom.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.Hom.comp_app AlgebraicGeometry.OModulePresheaf.SES.mk.injEq AlgebraicGeometry.OModulePresheaf.AffHom.mk.injEq AlgebraicGeometry.OModulePresheaf.Hom.appSections_apply AlgebraicGeometry.OModulePresheaf.AffSES.mk.injEq AlgebraicGeometry.OModulePresheaf.prod_obj AlgebraicGeometry.OModulePresheaf.restrOpen_obj AlgebraicGeometry.OModulePresheaf.DevissageStep.mk.injEq AlgebraicGeometry.OModulePresheaf.pushforward_obj AlgebraicGeometry.OModulePresheaf.im_obj AlgebraicGeometry.OModulePresheaf.pow_obj AlgebraicGeometry.OModulePresheaf.fstHom_app AlgebraicGeometry.OModulePresheaf.ker_obj AlgebraicGeometry.OModulePresheaf.coker_obj AlgebraicGeometry.OModulePresheaf.DevissageStep.mk.sizeOf_spec AlgebraicGeometry.Scheme.OrderedAffineCover.preimage_U AlgebraicGeometry.OModulePresheaf.sndHom_app AlgebraicGeometry.Scheme.Modules.ProjPresentation.mk.injEq AlgebraicGeometry.Scheme.Modules.ProjPresentation.mk.sizeOf_spec AlgebraicGeometry.Scheme.Modules.tensorPow_zero AlgebraicGeometry.Scheme.Modules.tensorPow_succ PresheafOfModules.InternalHom.presheaf_map_apply PresheafOfModules.InternalHom.curryFamily_app PresheafOfModules.InternalHom.add_app PresheafOfModules.InternalHom.smul_app PresheafOfModules.InternalHom.zero_app PresheafOfModules.ihomObj_map_val PresheafOfModules.ihomFunctor_map PresheafOfModules.InternalHom.restrict_app PresheafOfModules.InternalHom.postcomp_app PresheafOfModules.InternalHom.neg_app PresheafOfModules.curry'_app_val PresheafOfModules.InternalHom.presheaf_obj"
p2m_attr_erase "simp" "PresheafOfModules.ihomFunctor_obj PresheafOfModules.ihomObj_obj PresheafOfModules.InternalHom.sub_app PresheafOfModules.ihomMap_app_val SheafOfModules.tensorUnit_eq AlgebraicGeometry.Scheme.Modules.tensorUnit_eq PresheafOfModules.freeεIso_hom_app PresheafOfModules.freeμIso_hom_app AlgebraicGeometry.Scheme.Modules.tensorSections_zero_right AlgebraicGeometry.Scheme.Modules.map_unitSection AlgebraicGeometry.Scheme.Modules.tensorSectionsBilin_apply AlgebraicGeometry.Scheme.Modules.tensorPowSection_zero AlgebraicGeometry.Scheme.Modules.tensorSections_zero_left AlgebraicGeometry.RelPicard.RigidifiedLineBundle.mk.sizeOf_spec AlgebraicGeometry.RelPicard.RigidifiedLineBundle.mk.injEq NeronModelInfra.specGenericFibreInclusion_eq NeronModelInfra.genericFibreRestrict_coe_comp_snd NeronModelInfra.genericFibreRestrict_coe_comp_fst AlgebraicGeometry.OModulePresheaf.Leray.restrictToPreimage_U AlgebraicGeometry.Scheme.OrderedAffineCover.toCoverOf_U AlgebraicGeometry.Scheme.OrderedAffineCoverOf.mk.sizeOf_spec AlgebraicGeometry.Scheme.OrderedAffineCoverOf.mk.injEq AlgebraicGeometry.Scheme.OrderedAffineCover.restrict_U DoubleComplex.Bounded.mk.injEq DoubleComplex.Bounded.mk.sizeOf_spec DoubleComplex.Convergence.mk.injEq DoubleComplex.Convergence.mk.sizeOf_spec DoubleComplex.SubQuot.mk.sizeOf_spec DoubleComplex.SubQuot.mk.injEq AlgebraicGeometry.Scheme.Modules.glueComponent_glueMk AlgebraicGeometry.Scheme.Modules.UnitCocycle.mk.injEq AlgebraicGeometry.Scheme.Modules.UnitCocycle.mk.sizeOf_spec IsDirectLimit.Module.linearEquiv_symm_apply IsDirectLimit.linearEquiv_symm_apply IsDirectLimit.lift_of IsDirectLimit.Module.linearEquiv_apply IsDirectLimit.Module.lift_of IsDirectLimit.Equiv_apply AlgebraicGeometry.SubalgebraStages.specCone_π_app AlgebraicGeometry.SubalgebraStages.specLeg_specHom"
p2m_attr_erase "simp" "AlgebraicGeometry.SubalgebraStages.specLeg_specTrans AlgebraicGeometry.SubalgebraStages.cone_pt AlgebraicGeometry.SubalgebraStages.trans_fst AlgebraicGeometry.SubalgebraStages.diagram_obj AlgebraicGeometry.SubalgebraStages.leg_snd AlgebraicGeometry.SubalgebraStages.diagram_map AlgebraicGeometry.SubalgebraStages.specTrans_refl AlgebraicGeometry.SubalgebraStages.trans_snd AlgebraicGeometry.SubalgebraStages.specTrans_specHom AlgebraicGeometry.SubalgebraStages.specCone_pt AlgebraicGeometry.SubalgebraStages.cone_π_app AlgebraicGeometry.SubalgebraStages.specDiagram_map AlgebraicGeometry.SubalgebraStages.specDiagram_obj AlgebraicGeometry.SubalgebraStages.leg_fst AlgebraicGeometry.SubalgebraStages.leg_trans"

set_option autoImplicit false
set_option maxHeartbeats 1600000
open MvPolynomial CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.HilbertFunctor
attribute [local instance] MvPolynomial.gradedAlgebra

noncomputable section

namespace HilbComparisonAssembly

def sheafOf (n : ℕ) (A : Type) [CommRing A] (I : Ideal (MvPolynomial (Fin (n + 1)) A)) :
    (Proj (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) A)).IdealSheafData :=
  (AlgebraicGeometry.ProjSpace.exists_idealSheafData_ideal_basicOpen_eq_span n A I).choose

theorem sheafOf_spec (n : ℕ) (A : Type) [CommRing A] (I : Ideal (MvPolynomial (Fin (n + 1)) A)) :
    ∀ i : Fin (n + 1),
        (sheafOf n A I).ideal ⟨Proj.basicOpen (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) A) (X i),
          Proj.isAffineOpen_basicOpen (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) A) (X i) (ProjSpace.X_mem_one A n i) one_pos⟩ =
        Ideal.span { s | ∃ (d : ℕ) (F : MvPolynomial (Fin (n + 1)) A) (hF : F.IsHomogeneous d),
          F ∈ I ∧
          s = (Proj.awayToSection (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) A) (X i))
              (HomogeneousLocalization.mk
                { deg := d
                  num := ⟨F, (MvPolynomial.mem_homogeneousSubmodule d F).mpr hF⟩
                  den := ⟨X i ^ d, (MvPolynomial.mem_homogeneousSubmodule d _).mpr (MvPolynomial.isHomogeneous_X_pow i d)⟩
                  den_mem := ⟨d, rfl⟩ }) } :=
  (AlgebraicGeometry.ProjSpace.exists_idealSheafData_ideal_basicOpen_eq_span n A I).choose_spec

def Phi (n : ℕ) (h : ℕ → ℕ) (A : Type) [CommRing A] (p : Point A n h) :
    (Z : Scheme.{0}) × (Z ⟶ Proj (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) A)) :=
  ⟨(sheafOf n A p.I).subscheme, (sheafOf n A p.I).subschemeι⟩

scoped instance instClosed (n : ℕ) (h : ℕ → ℕ) (A : Type) [CommRing A] (p : Point A n h) :
    IsClosedImmersion (Phi n h A p).2 := by
  dsimp [Phi]; infer_instance

theorem degree_ge_of_mem_span {A : Type} [CommRing A] {n m : ℕ}
    (S : Set (MvPolynomial (Fin (n + 1)) A)) (hS : ∀ s ∈ S, s.IsHomogeneous m)
    (F : MvPolynomial (Fin (n + 1)) A) (hF : F ∈ Ideal.span S) :
    ∀ c ∈ F.support, m ≤ c.degree := by
  classical
  induction hF using Submodule.span_induction with
  | mem x hx =>
    intro c hc
    have := (hS x hx)  (mem_support_iff.mp hc)

    simp only [Finsupp.weight_apply, Pi.one_apply, smul_eq_mul, mul_one] at this
    rw [Finsupp.degree]
    exact le_of_eq this.symm
  | zero => intro c hc; simp at hc
  | add x y _ _ hx hy =>
    intro c hc
    rcases Finset.mem_union.mp (MvPolynomial.support_add hc) with h | h
    · exact hx c h
    · exact hy c h
  | smul a x _ hx =>
    intro c hc
    rw [smul_eq_mul] at hc
    obtain ⟨c₁, hc₁, c₂, hc₂, rfl⟩ := Finset.mem_add.mp (MvPolynomial.support_mul a x hc)
    rw [(map_add Finsupp.degree)]
    exact le_add_left (hx c₂ hc₂)

theorem eq_zero_of_mem_span_of_lt {A : Type} [CommRing A] {n m d : ℕ}
    (S : Set (MvPolynomial (Fin (n + 1)) A)) (hS : ∀ s ∈ S, s.IsHomogeneous m)
    (F : MvPolynomial (Fin (n + 1)) A) (hF : F ∈ Ideal.span S) (hFd : F.IsHomogeneous d) (hd : d < m) :
    F = 0 := by
  classical
  by_contra hne
  obtain ⟨c, hc⟩ := Finset.nonempty_iff_ne_empty.mpr (mt MvPolynomial.support_eq_empty.mp hne)
  have h1 := degree_ge_of_mem_span S hS F hF c hc
  have h2 : c.degree = d := by
    have := hFd (mem_support_iff.mp hc)
    simpa [Finsupp.weight_apply, Finsupp.degree, Finsupp.sum] using this
  omega

theorem le_of_forall_isHomogeneous {A : Type} [CommRing A] {n : ℕ}
    (I J : Ideal (MvPolynomial (Fin (n + 1)) A))
    (hI : ∀ p ∈ I, ∀ d : ℕ, homogeneousComponent d p ∈ I)
    (h : ∀ (d : ℕ) (F : MvPolynomial (Fin (n + 1)) A), F.IsHomogeneous d → F ∈ I → F ∈ J) :
    I ≤ J := by
  intro f hf
  rw [← sum_homogeneousComponent f]
  exact Ideal.sum_mem _ fun d _ => h d _ (homogeneousComponent_isHomogeneous d f) (hI f hf d)

end HilbComparisonAssembly
p2m_reactivate "P2MW.S_AlgebraicGeometry_HilbertFunctor_exists_closedImmersion_flat_lfp_forall_mem_iff_ker_ideal_eq_of_point_hilbertFunctionOf.HilbComparisonAssembly"

open HilbComparisonAssembly in
theorem solution
    (n : ℕ) (P : Polynomial ℚ)
    (hP : ∃ (K : Type) (_ : Field K) (I : Ideal (MvPolynomial (Fin (n + 1)) K)),
      (∀ p ∈ I, ∀ d : ℕ, homogeneousComponent d p ∈ I) ∧
      ∃ d₁ : ℕ, ∀ d : ℕ, d₁ ≤ d → (Module.finrank K (piece I d) : ℚ) = P.eval (d : ℚ)) :
    ∃ D₀ : ℕ, ∀ m : ℕ, D₀ ≤ m →
      ∃ Φ : ∀ (A : Type) [CommRing A], Point A n (hilbertFunctionOf n P m) →
          (Z : Scheme.{0}) × (Z ⟶ Proj (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) A)),

        (∀ (A : Type) [CommRing A] (p : Point A n (hilbertFunctionOf n P m)),
          IsClosedImmersion (Φ A p).2 ∧ Flat ((Φ A p).2 ≫ ProjSpace.π A n) ∧
            LocallyOfFinitePresentation ((Φ A p).2 ≫ ProjSpace.π A n)) ∧

        (∀ (A : Type) [CommRing A] (p q : Point A n (hilbertFunctionOf n P m)),
          (∃ e : (Φ A p).1 ≅ (Φ A q).1, e.hom ≫ (Φ A q).2 = (Φ A p).2) → p = q) ∧

        (∀ (A B : Type) [CommRing A] [CommRing B] [Algebra A B]
            (p : Point A n (hilbertFunctionOf n P m)) (q : Point B n (hilbertFunctionOf n P m)),
          q.I = Ideal.map (MvPolynomial.map (algebraMap A B)) p.I →
          ∃ e : (Φ B q).1 ⟶ (Φ A p).1,
            IsPullback e ((Φ B q).2 ≫ ProjSpace.π B n) ((Φ A p).2 ≫ ProjSpace.π A n)
              (Spec.map (CommRingCat.ofHom (algebraMap A B))) ∧
            e ≫ (Φ A p).2 = (Φ B q).2 ≫ ProjSpace.map A B n) ∧

        (∀ (A : Type) [CommRing A] (Z : Scheme.{0}) (ι : Z ⟶ Proj (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) A)),
          IsClosedImmersion ι → Flat (ι ≫ ProjSpace.π A n) → LocallyOfFinitePresentation (ι ≫ ProjSpace.π A n) →
          (∀ (k : Type) [Field k] [IsAlgClosed k] [Algebra A k],
            ∃ (q : Point k n (hilbertFunctionOf n P m)) (e : (Φ k q).1 ⟶ Z),
              IsPullback e ((Φ k q).2 ≫ ProjSpace.π k n) (ι ≫ ProjSpace.π A n)
                (Spec.map (CommRingCat.ofHom (algebraMap A k))) ∧
              e ≫ ι = (Φ k q).2 ≫ ProjSpace.map A k n) →
          ∃ (p : Point A n (hilbertFunctionOf n P m)) (e : (Φ A p).1 ≅ Z), e.hom ≫ ι = (Φ A p).2) ∧

        (∀ (A : Type) [CommRing A] (p : Point A n (hilbertFunctionOf n P m)) (d : ℕ), m ≤ d →
          ∀ (F : MvPolynomial (Fin (n + 1)) A) (hF : F.IsHomogeneous d),
            (F ∈ p.I ↔ ∀ i : Fin (n + 1),
              ((Φ A p).2.app (Proj.basicOpen (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) A) (X i)))
                ((Proj.awayToSection (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) A) (X i))
                  (HomogeneousLocalization.mk
                    { deg := d
                      num := ⟨F, (MvPolynomial.mem_homogeneousSubmodule d F).mpr hF⟩
                      den := ⟨X i ^ d, (MvPolynomial.mem_homogeneousSubmodule d _).mpr (MvPolynomial.isHomogeneous_X_pow i d)⟩
                      den_mem := ⟨d, rfl⟩ })) = 0)) ∧

        (∀ (A : Type) [CommRing A] (p : Point A n (hilbertFunctionOf n P m)) (i : Fin (n + 1)),
          (Scheme.Hom.ker (Φ A p).2).ideal ⟨Proj.basicOpen (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) A) (X i),
            Proj.isAffineOpen_basicOpen (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) A) (X i) (ProjSpace.X_mem_one A n i) one_pos⟩ =
          Ideal.span { s | ∃ (d : ℕ) (F : MvPolynomial (Fin (n + 1)) A) (hF : F.IsHomogeneous d),
            F ∈ p.I ∧
            s = (Proj.awayToSection (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) A) (X i))
                (HomogeneousLocalization.mk
                  { deg := d
                    num := ⟨F, (MvPolynomial.mem_homogeneousSubmodule d F).mpr hF⟩
                    den := ⟨X i ^ d, (MvPolynomial.mem_homogeneousSubmodule d _).mpr (MvPolynomial.isHomogeneous_X_pow i d)⟩
                    den_mem := ⟨d, rfl⟩ }) }) := by
  classical

  obtain ⟨D₃, hD₃⟩ := AlgebraicGeometry.HilbertFunctor.exists_forall_mem_of_forall_X_pow_mul_mem_hilbertFunctionOf n P hP
  obtain ⟨D₄, hD₄⟩ := AlgebraicGeometry.HilbertFunctor.exists_point_I_eq_span_of_isClosedImmersion_of_flat_of_locallyOfFinitePresentation n P hP
  obtain ⟨Dg, hDg⟩ := MvPolynomial.exists_forall_finrank_piece_succ_le_eval_and_exists_eq_eval n P hP
  obtain ⟨K₀, _, I₀, hI₀, d₁, hd₁⟩ := hP
  refine ⟨max (max D₃ D₄) (max Dg d₁), fun m hm => ?_⟩
  have hm₃ : D₃ ≤ m := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hm
  have hm₄ : D₄ ≤ m := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hm
  have hmg : Dg ≤ m := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hm
  have hm₁ : d₁ ≤ m := le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hm

  have hcast : ∀ e : ℕ, m ≤ e → ((hilbertFunctionOf n P m e : ℕ) : ℚ) = P.eval (e : ℚ) := by
    intro e he
    have hPe := hd₁ e (le_trans hm₁ he)
    simp only [hilbertFunctionOf, if_neg (not_lt.mpr he)]
    rw [← hPe, Int.floor_natCast, Int.toNat_natCast]

  have hgen : ∀ (A : Type) [CommRing A] (p : Point A n (hilbertFunctionOf n P m)),
      p.I = Ideal.span {f | f ∈ p.I ∧ f.IsHomogeneous m} := by
    intro A _ p
    refine AlgebraicGeometry.HilbertFunctor.Point.I_eq_span_of_forall_finrank_piece_succ_le n m (hilbertFunctionOf n P m) ?_ ?_ A p
    · intro d hd; simp [hilbertFunctionOf, hd]
    · intro e he K _ J hJ hJe
      have he1 : m ≤ e + 1 := Nat.le_succ_of_le he
      have h1 := (hDg e (le_trans hmg he)).1 K J hJ (by rw [hJe]; exact hcast e he)
      rw [show ((e : ℚ) + 1) = ((e + 1 : ℕ) : ℚ) by push_cast; ring, ← hcast (e + 1) he1] at h1
      exact_mod_cast h1

  have hchart : ∀ (A : Type) [CommRing A] (p : Point A n (hilbertFunctionOf n P m))
      (d : ℕ), m ≤ d → ∀ (F : MvPolynomial (Fin (n + 1)) A) (hF : F.IsHomogeneous d),
      (F ∈ p.I ↔ ∀ i : Fin (n + 1),
        (Proj.awayToSection (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) A) (X i))
              (HomogeneousLocalization.mk
                { deg := d
                  num := ⟨F, (MvPolynomial.mem_homogeneousSubmodule d F).mpr hF⟩
                  den := ⟨X i ^ d, (MvPolynomial.mem_homogeneousSubmodule d _).mpr (MvPolynomial.isHomogeneous_X_pow i d)⟩
                  den_mem := ⟨d, rfl⟩ }) ∈
          Ideal.span { s | ∃ (d : ℕ) (F : MvPolynomial (Fin (n + 1)) A) (hF : F.IsHomogeneous d),
          F ∈ p.I ∧
          s = (Proj.awayToSection (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) A) (X i))
              (HomogeneousLocalization.mk
                { deg := d
                  num := ⟨F, (MvPolynomial.mem_homogeneousSubmodule d F).mpr hF⟩
                  den := ⟨X i ^ d, (MvPolynomial.mem_homogeneousSubmodule d _).mpr (MvPolynomial.isHomogeneous_X_pow i d)⟩
                  den_mem := ⟨d, rfl⟩ }) }) := by
    intro A _ p d hd F hF
    constructor
    · intro hFI i
      exact (AlgebraicGeometry.ProjSpace.awayToSection_mk_mem_span_iff_exists_X_pow_mul_mem n A p.I i d F hF).mpr ⟨0, by simpa using hFI⟩
    · intro hall
      exact hD₃ m hm₃ A p d hd F hF fun i => (AlgebraicGeometry.ProjSpace.awayToSection_mk_mem_span_iff_exists_X_pow_mul_mem n A p.I i d F hF).mp (hall i)
  refine ⟨fun A _ p => Phi n _ A p, ?_, ?_, ?_, ?_, ?_, ?_⟩
  ·
    intro A _ p
    refine ⟨inferInstance, ?_, ?_⟩
    · exact AlgebraicGeometry.HilbertFunctor.Point.flat_comp_of_ideal_basicOpen_eq_span n A _ p (sheafOf n A p.I) (sheafOf_spec n A p.I)
    · refine AlgebraicGeometry.ProjSpace.locallyOfFinitePresentation_comp_of_fg_of_ideal_basicOpen_eq_span n A p.I p.homogeneous ?_ (sheafOf n A p.I) (sheafOf_spec n A p.I)

      set Sm : Submodule A (MvPolynomial (Fin (n + 1)) A) := MvPolynomial.homogeneousSubmodule (Fin (n + 1)) A m with hSm
      set Km : Submodule A Sm := Submodule.comap Sm.subtype (p.I.restrictScalars A) with hKm

      have hSmfg : Sm.FG := by
        have h1 : (MvPolynomial.restrictTotalDegree (Fin (n + 1)) A m).FG :=
          Submodule.fg_top _ |>.mp Module.Finite.fg_top
        have h2 : Sm = Submodule.map (homogeneousComponent m) (MvPolynomial.restrictTotalDegree (Fin (n + 1)) A m) := by
          apply le_antisymm
          · intro f hf
            refine Submodule.mem_map.mpr ⟨f, ?_, ?_⟩
            · rw [MvPolynomial.mem_restrictTotalDegree]
              exact ((MvPolynomial.mem_homogeneousSubmodule m f).mp (hSm ▸ hf)).totalDegree_le
            · rw [homogeneousComponent_of_mem (hSm ▸ hf), if_pos rfl]
          · rintro f ⟨g, -, rfl⟩
            rw [hSm]; exact homogeneousComponent_mem m g
        rw [h2]; exact h1.map _
      haveI : Module.Finite A Sm := Module.Finite.iff_fg.mpr hSmfg
      haveI : Module.Projective A (Sm ⧸ Km) := by rw [hKm, hSm]; exact p.projective_piece m

      have hKmfg : Km.FG := by
        obtain ⟨s, hs⟩ := Module.projective_lifting_property Km.mkQ LinearMap.id (Submodule.mkQ_surjective Km)
        have hKr : Km = LinearMap.range (LinearMap.id - s ∘ₗ Km.mkQ) := by
          apply le_antisymm
          · intro x hx
            refine ⟨x, ?_⟩
            simp [(Submodule.Quotient.mk_eq_zero Km).mpr hx]
          · rintro x ⟨y, rfl⟩
            have := LinearMap.congr_fun hs (Km.mkQ y)
            simp only [LinearMap.coe_comp, Function.comp_apply, LinearMap.id_coe, id_eq,
              Submodule.mkQ_apply] at this
            refine (Submodule.Quotient.mk_eq_zero Km).mp ?_
            simp only [LinearMap.sub_apply, LinearMap.id_coe, id_eq, LinearMap.coe_comp, Function.comp_apply,
              Submodule.mkQ_apply, Submodule.Quotient.mk_sub]
            rw [sub_eq_zero]
            exact this.symm
        rw [hKr, LinearMap.range_eq_map]
        exact Module.Finite.fg_top.map _
      obtain ⟨T, hT⟩ := hKmfg
      refine ⟨(T.image (fun x : ↥Sm => (↑x : MvPolynomial (Fin (n + 1)) A))), ?_⟩
      rw [hgen A p]
      apply le_antisymm
      · rw [Ideal.span_le]
        rintro f hf
        obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp (Finset.mem_coe.mp hf)
        have hxK : x ∈ Km := hT ▸ Submodule.subset_span hx
        refine Ideal.subset_span ⟨?_, ?_⟩
        · rw [hKm] at hxK; exact hxK
        · exact (MvPolynomial.mem_homogeneousSubmodule m _).mp (hSm ▸ x.2)
      · rw [Ideal.span_le]
        rintro f ⟨hfI, hfm⟩
        have hfS : f ∈ Sm := hSm ▸ (MvPolynomial.mem_homogeneousSubmodule m f).mpr hfm
        have hfK : (⟨f, hfS⟩ : Sm) ∈ Km := by rw [hKm]; exact hfI
        rw [← hT] at hfK

        have : f ∈ Submodule.span A ((fun x : ↥Sm => (↑x : MvPolynomial (Fin (n + 1)) A)) '' (T : Set ↥Sm)) := by
          have := Submodule.apply_mem_span_image_of_mem_span (Sm.subtype) hfK
          simpa using this
        refine (Submodule.span_le_restrictScalars A _ _) (by simpa [Finset.coe_image] using this)
  ·
    intro A _ p q ⟨e, he⟩
    have hker : sheafOf n A p.I = sheafOf n A q.I := by
      have h1 := (sheafOf n A p.I).ker_subschemeι
      have h2 := (sheafOf n A q.I).ker_subschemeι
      change (Phi n _ A p).2.ker = _ at h1
      change (Phi n _ A q).2.ker = _ at h2
      rw [← h1, ← h2, ← he, Scheme.Hom.ker_comp_of_isIso]
    have key : ∀ (p q : Point A n (hilbertFunctionOf n P m)), sheafOf n A p.I = sheafOf n A q.I →
        ∀ (d : ℕ) (F : MvPolynomial (Fin (n + 1)) A), F.IsHomogeneous d → F ∈ p.I → F ∈ q.I := by
      intro p q hpq d F hF hFp
      rcases lt_or_ge d m with hd | hd
      · have : F = 0 := by
          refine eq_zero_of_mem_span_of_lt {f | f ∈ p.I ∧ f.IsHomogeneous m} (fun s hs => hs.2) F ?_ hF hd
          rw [← hgen A p]; exact hFp
        rw [this]; exact Submodule.zero_mem _
      · rw [hchart A q d hd F hF]
        intro i
        rw [← sheafOf_spec n A q.I i, ← hpq, sheafOf_spec n A p.I i]
        exact ((hchart A p d hd F hF).mp hFp) i
    apply Point.ext
    exact le_antisymm (le_of_forall_isHomogeneous p.I q.I p.homogeneous (key p q hker))
      (le_of_forall_isHomogeneous q.I p.I q.homogeneous (key q p hker.symm))
  ·
    intro A B _ _ _ p q hq
    have hc : sheafOf n B q.I = (sheafOf n A p.I).comap (ProjSpace.map A B n) := by
      refine AlgebraicGeometry.ProjSpace.eq_comap_map_of_ideal_basicOpen_eq_span n A B p.I p.homogeneous (sheafOf n A p.I) (sheafOf_spec n A p.I) (sheafOf n B q.I) ?_
      rw [← hq]; exact sheafOf_spec n B q.I
    have hPB := AlgebraicGeometry.ProjSpace.isPullback_map A B n
    have H : (Phi n _ A p).2.ker ≤ ((Phi n _ B q).2 ≫ ProjSpace.map A B n).ker := by
      rw [← Scheme.IdealSheafData.map_ker]
      dsimp [Phi]
      rw [Scheme.IdealSheafData.ker_subschemeι, Scheme.IdealSheafData.ker_subschemeι, hc]
      exact Scheme.IdealSheafData.le_map_comap _ _
    let e : (Phi n _ B q).1 ⟶ (Phi n _ A p).1 :=
      IsClosedImmersion.lift (Phi n _ A p).2 ((Phi n _ B q).2 ≫ ProjSpace.map A B n) H
    have he : e ≫ (Phi n _ A p).2 = (Phi n _ B q).2 ≫ ProjSpace.map A B n :=
      IsClosedImmersion.lift_fac _ _ _
    refine ⟨e, ?_, he⟩
    have sq := AlgebraicGeometry.isPullback_of_isClosedImmersion (Phi n _ B q).2 (Phi n _ A p).2 e
      (ProjSpace.map A B n) he.symm (by
        dsimp [Phi]
        rw [Scheme.IdealSheafData.ker_subschemeι, Scheme.IdealSheafData.ker_subschemeι, hc])
    exact sq.flip.paste_vert hPB
  ·
    intro A _ Z ι hι hfl hfp hfib
    obtain ⟨p, hp⟩ := hD₄ m hm₄ A Z ι hι hfl hfp (by
      intro k _ _ _ Zk ιk e hιk hsq hcomm
      obtain ⟨q, e₀, hsq₀, hcomm₀⟩ := hfib k
      obtain ⟨φ, hφ₁, hφ₂⟩ := AlgebraicGeometry.ProjSpace.exists_iso_hom_comp_eq_of_isPullback_of_comp_eq_map n A k Z ι (Phi n _ k q).1 (Phi n _ k q).2 e₀ hsq₀ hcomm₀ Zk ιk e hsq hcomm
      refine ⟨q, fun d hd F hF => ?_⟩
      rw [hchart k q d hd F hF]
      refine forall_congr' fun i => ?_
      rw [← sheafOf_spec n k q.I i]
      have hk : (sheafOf n k q.I).ideal ⟨Proj.basicOpen (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) k) (X i),
          Proj.isAffineOpen_basicOpen (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) k) (X i) (ProjSpace.X_mem_one k n i) one_pos⟩ =
          RingHom.ker ((sheafOf n k q.I).subschemeι.app (Proj.basicOpen (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) k) (X i))).hom := by
        have := Scheme.Hom.ker_apply (sheafOf n k q.I).subschemeι
          ⟨Proj.basicOpen (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) k) (X i),
            Proj.isAffineOpen_basicOpen (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) k) (X i) (ProjSpace.X_mem_one k n i) one_pos⟩
        rw [Scheme.IdealSheafData.ker_subschemeι] at this
        exact this
      have hφ₁' : φ.hom ≫ ιk = (sheafOf n k q.I).subschemeι := hφ₁
      rw [hk, RingHom.mem_ker, ← hφ₁', Scheme.Hom.comp_app]
      change (ConcreteCategory.hom (ιk.app _ ≫ φ.hom.app _)) _ = 0 ↔ _
      rw [CategoryTheory.comp_apply]
      constructor
      · intro h0
        have hinj := (ConcreteCategory.bijective_of_isIso
          (φ.hom.app (ιk ⁻¹ᵁ Proj.basicOpen (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) k) (X i)))).1
        apply hinj
        rw [h0, map_zero]
      · intro h0
        rw [h0, map_zero])
    haveI : IsClosedImmersion ι := hι
    have h𝓘 := sheafOf_spec n A p.I
    have hK5 : sheafOf n A p.I = ι.ker := by
      refine AlgebraicGeometry.ProjSpace.eq_ker_of_ideal_basicOpen_eq_span_of_isClosedImmersion n A Z ι hι m (sheafOf n A p.I) ?_
      intro i
      rw [h𝓘 i, hp]
    have hle : ι.ker ≤ (Phi n _ A p).2.ker := by
      dsimp [Phi]; rw [Scheme.IdealSheafData.ker_subschemeι, hK5]
    haveI : IsIso (IsClosedImmersion.lift ι (Phi n _ A p).2 hle) :=
      IsClosedImmersion.isIso_lift ι (Phi n _ A p).2 (by dsimp [Phi]; rw [Scheme.IdealSheafData.ker_subschemeι, hK5])
    exact ⟨p, asIso (IsClosedImmersion.lift ι (Phi n _ A p).2 hle), IsClosedImmersion.lift_fac _ _ _⟩
  ·
    intro A _ p d hd F hF
    rw [hchart A p d hd F hF]
    refine forall_congr' fun i => ?_
    rw [← sheafOf_spec n A p.I i]
    have hk : (sheafOf n A p.I).ideal ⟨Proj.basicOpen (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) A) (X i),
        Proj.isAffineOpen_basicOpen (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) A) (X i) (ProjSpace.X_mem_one A n i) one_pos⟩ =
        RingHom.ker ((sheafOf n A p.I).subschemeι.app (Proj.basicOpen (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) A) (X i))).hom := by
      have := Scheme.Hom.ker_apply (sheafOf n A p.I).subschemeι
        ⟨Proj.basicOpen (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) A) (X i),
          Proj.isAffineOpen_basicOpen (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) A) (X i) (ProjSpace.X_mem_one A n i) one_pos⟩
      rw [Scheme.IdealSheafData.ker_subschemeι] at this
      exact this
    rw [hk, RingHom.mem_ker]
    rfl
  ·
    intro A _ p i
    dsimp only [Phi]
    rw [Scheme.IdealSheafData.ker_subschemeι]
    exact sheafOf_spec n A p.I i

end
end S_AlgebraicGeometry_HilbertFunctor_exists_closedImmersion_flat_lfp_forall_mem_iff_ker_ideal_eq_of_point_hilbertFunctionOf
end P2MW
export P2MW.S_AlgebraicGeometry_HilbertFunctor_exists_closedImmersion_flat_lfp_forall_mem_iff_ker_ideal_eq_of_point_hilbertFunctionOf (solution)
