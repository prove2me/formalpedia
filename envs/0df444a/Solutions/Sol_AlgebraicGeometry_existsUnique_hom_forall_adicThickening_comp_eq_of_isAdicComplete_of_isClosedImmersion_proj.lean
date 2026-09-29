-- Prove2me | solution 1 for AlgebraicGeometry.existsUnique_hom_forall_adicThickening_comp_eq_of_isAdicComplete_of_isClosedImmersion_proj
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.122355+00:00
-- url     : https://prove2.me/submissions/df3089ae-26f0-5ad3-ba0d-d79f77c7bbb0

import Mathlib
import Definitions.Def_AlgebraicGeometry_AdicThickening
import Definitions.Def_AlgebraicGeometry_ProjSpace
import Theorems.Thm_AlgebraicGeometry_exists_isClosedImmersion_projSpace_pullback_of_isClosedImmersion
import Theorems.Thm_AlgebraicGeometry_exists_idealSheafData_forall_comap_adicThickening_eq_of_isAdicComplete_of_isClosedImmersion_proj
import Theorems.Thm_AlgebraicGeometry_isIso_of_forall_isIso_adicThickening_of_isAdicComplete_of_isClosedImmersion_proj
import Theorems.Thm_AlgebraicGeometry_eq_of_forall_adicThickening_comp_eq_of_isAdicComplete_of_isClosedImmersion_proj
import Theorems.Thm_AlgebraicGeometry_isIso_and_adicThickening_comp_eq_of_comap_eq_ker_of_comp_eq
import Theorems.Thm_AlgebraicGeometry_isClosedImmersion_and_comap_ker_eq_ker_of_adicThickening_graph
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_existsUnique_hom_forall_adicThickening_comp_eq_of_isAdicComplete_of_isClosedImmersion_proj
p2m_attr_erase "instance" "AlgebraicGeometry.OModulePresheaf.instSubsingletonObjZero AlgebraicGeometry.OModulePresheaf.isScalarTower AlgebraicGeometry.Scheme.OrderedAffineCover.instLinearOrder AlgebraicGeometry.OModulePresheaf.module AlgebraicGeometry.Scheme.OrderedAffineCover.instFintype AlgebraicGeometry.Scheme.OrderedAffineCover.instFintypeIdx AlgebraicGeometry.OModulePresheaf.addCommGroup AlgebraicGeometry.Scheme.OrderedAffineCover.instDecidableEqIdx AlgebraicGeometry.OModulePresheaf.moduleSections TwoChartCech.Sections.M0_moduleA TwoChartCech.Sections.M1_module TwoChartCech.Cover.A01_algebra TwoChartCech.Cover.A0_algebra TwoChartCech.Cover.A1_commRing TwoChartCech.Cover.A1_algebra TwoChartCech.Sections.M01_module TwoChartCech.Sections.M0_addCommGroup TwoChartCech.Sections.M0_tower TwoChartCech.Sections.M01_addCommGroup TwoChartCech.Cover.A0_commRing TwoChartCech.Sections.M1_tower TwoChartCech.Sections.M01_moduleA TwoChartCech.Sections.M0_module TwoChartCech.Sections.M1_moduleA TwoChartCech.Sections.M1_addCommGroup TwoChartCech.Cover.A01_commRing TwoChartCech.Sections.M01_tower CoherentBaseChange.TwoTermComplex.C0_module CoherentBaseChange.TwoTermComplex.C0_addCommGroup CoherentBaseChange.TwoTermComplex.C1_module CoherentBaseChange.TwoTermComplex.C1_addCommGroup CoherentBaseChange.TwoTermComplex.C0_free CoherentBaseChange.TwoTermComplex.C1_finite CoherentBaseChange.TwoTermComplex.C0_finite CoherentBaseChange.TwoTermComplex.C1_free AlgebraicGeometry.OModulePresheaf.moduleSectionsHomSub AlgebraicGeometry.OModulePresheaf.smulSections AlgebraicGeometry.OModulePresheaf.Leray.relAltC_scalarTower AlgebraicGeometry.OModulePresheaf.Leray.ker_relAltd_modΓ AlgebraicGeometry.OModulePresheaf.Leray.relAltC_modΓ"
p2m_attr_erase "instance" "AlgebraicGeometry.OModulePresheaf.Leray.biC_abGrp AlgebraicGeometry.OModulePresheaf.Leray.relAltH_modΓ AlgebraicGeometry.OModulePresheaf.Leray.ker_relAltd_smul AlgebraicGeometry.OModulePresheaf.Leray.relAltH_scalarTower AlgebraicGeometry.OModulePresheaf.Leray.relAltH_smul AlgebraicGeometry.OModulePresheaf.Leray.biC_module AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instDecidableEqIdx AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instFintype AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instLinearOrder AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instFintypeIdx DoubleComplex.instModuleE₂I DoubleComplex.Bounded.modR DoubleComplex.instModuleE₂II DoubleComplex.instAddCommGroupE₂II DoubleComplex.Bounded.abGrp DoubleComplex.instAddCommGroupE₂I ProjSpaceCech.GradedModule.H.module ProjSpaceCech.GradedModule.H.addCommGroup ProjSpaceCech.GradedModule.sec.instAdd ProjSpaceCech.GradedModule.sec.instNeg ProjSpaceCech.GradedModule.acg ProjSpaceCech.GradedModule.Frac.setoid ProjSpaceCech.GradedModule.modR ProjSpaceCech.GradedModule.sec.instModule ProjSpaceCech.GradedModule.sec.instAddCommGroup ProjSpaceCech.GradedModule.sec.instZero ProjSpaceCech.GradedModule.Presentation.fJ ProjSpaceCech.GradedModule.sec.instSMul ProjSpaceCech.Twist.H.module ProjSpaceCech.Idx.instFintype ProjSpaceCech.Twist.H.addCommGroup ProjSpaceCech.Idx.instDecidableEq ProjSpaceCech.Twist.Mon.instDecidableEq ProjSpaceCech.Twist.cochain.instAddCommGroup ProjSpaceCech.Twist.cochain.instModule AlgebraicGeometry.ProjSpace.twistObj.addCommGroup AlgebraicGeometry.ProjSpace.twistFam.module AlgebraicGeometry.ProjSpace.twistObj.module AlgebraicGeometry.ProjSpace.twistObj.moduleSections AlgebraicGeometry.ProjSpace.twistFam.addCommGroup"
p2m_attr_erase "instance" "AlgebraicGeometry.OModulePresheaf.familyFramesGradedModule.moduleBase AlgebraicGeometry.OModulePresheaf.FamilyFrames.module AlgebraicGeometry.OModulePresheaf.FamilyFrames.addCommGroup"
p2m_attr_erase "simp" "AlgebraicGeometry.OModulePresheaf.prod_obj AlgebraicGeometry.OModulePresheaf.restrOpen_obj AlgebraicGeometry.OModulePresheaf.DevissageStep.mk.injEq AlgebraicGeometry.OModulePresheaf.pushforward_obj AlgebraicGeometry.OModulePresheaf.im_obj AlgebraicGeometry.OModulePresheaf.pow_obj AlgebraicGeometry.OModulePresheaf.fstHom_app AlgebraicGeometry.OModulePresheaf.ker_obj AlgebraicGeometry.OModulePresheaf.coker_obj AlgebraicGeometry.OModulePresheaf.DevissageStep.mk.sizeOf_spec AlgebraicGeometry.Scheme.OrderedAffineCover.preimage_U AlgebraicGeometry.OModulePresheaf.sndHom_app AlgebraicGeometry.OModulePresheaf.Hom.mk.injEq AlgebraicGeometry.OModulePresheaf.Hom.id_app AlgebraicGeometry.OModulePresheaf.AffHom.appSections_apply AlgebraicGeometry.OModulePresheaf.AffHom.comp_app AlgebraicGeometry.OModulePresheaf.AffSES.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.AffHom.kerMap_coe AlgebraicGeometry.OModulePresheaf.AffHom.id_app AlgebraicGeometry.OModulePresheaf.Hom.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.Hom.toAffHom_app AlgebraicGeometry.OModulePresheaf.SES.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.AffHom.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.Hom.comp_app AlgebraicGeometry.OModulePresheaf.SES.mk.injEq AlgebraicGeometry.OModulePresheaf.AffHom.mk.injEq AlgebraicGeometry.OModulePresheaf.Hom.appSections_apply AlgebraicGeometry.OModulePresheaf.AffSES.mk.injEq AlgebraicGeometry.Scheme.OrderedAffineCover.mk.injEq AlgebraicGeometry.OModulePresheaf.mk.sizeOf_spec AlgebraicGeometry.Scheme.OrderedAffineCover.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.mk.injEq AlgebraicGeometry.Scheme.TwoAffineOpenCover.mk.injEq AlgebraicGeometry.Scheme.TwoAffineOpenCover.mk.sizeOf_spec AlgebraicGeometry.Scheme.TwoAffineOpenCover.pullback_U1 AlgebraicGeometry.Scheme.TwoAffineOpenCover.pullback_U0 TwoChartCech.Sections.mk.injEq TwoChartCech.Cover.mk.injEq TwoChartCech.GrothendieckComplex.mk.injEq TwoChartCech.Sections.mk.sizeOf_spec"
p2m_attr_erase "simp" "TwoChartCech.Cover.mk.sizeOf_spec TwoChartCech.Cover.lineBundle_r0_apply TwoChartCech.GrothendieckComplex.mk.sizeOf_spec TwoChartCech.Cover.lineBundle_r1_apply CoherentBaseChange.TwoTermComplex.mk.sizeOf_spec CoherentBaseChange.TwoTermComplex.mk.injEq AlgebraicGeometry.OModulePresheaf.internalHom.ofAffHom_apply AlgebraicGeometry.OModulePresheaf.internalHom.toAffHom_app AlgebraicGeometry.OModulePresheaf.Leray.restrictToPreimage_U AlgebraicGeometry.Scheme.OrderedAffineCover.toCoverOf_U AlgebraicGeometry.Scheme.OrderedAffineCoverOf.mk.sizeOf_spec AlgebraicGeometry.Scheme.OrderedAffineCoverOf.mk.injEq AlgebraicGeometry.Scheme.OrderedAffineCover.restrict_U DoubleComplex.Bounded.mk.injEq DoubleComplex.Bounded.mk.sizeOf_spec DoubleComplex.Convergence.mk.injEq DoubleComplex.Convergence.mk.sizeOf_spec DoubleComplex.SubQuot.mk.sizeOf_spec DoubleComplex.SubQuot.mk.injEq ProjSpaceCech.GradedModule.mk.injEq ProjSpaceCech.GradedModule.mk.sizeOf_spec ProjSpaceCech.GradedModule.Frac.mk.sizeOf_spec ProjSpaceCech.GradedModule.Presentation.mk.injEq ProjSpaceCech.GradedModule.Frac.mk.injEq ProjSpaceCech.GradedModule.Presentation.mk.sizeOf_spec ProjSpaceCech.GradedModule.Hom.shift_toLinearMap ProjSpaceCech.GradedModule.Hom.mk.sizeOf_spec ProjSpaceCech.GradedModule.Hom.mk.injEq AlgebraicGeometry.ProjSpace.twistObj.mk.injEq AlgebraicGeometry.ProjSpace.twistObj.zero_val AlgebraicGeometry.ProjSpace.twistObj.add_val AlgebraicGeometry.ProjSpace.twist_res_val AlgebraicGeometry.ProjSpace.twist_smul_val AlgebraicGeometry.ProjSpace.twistGradeToObj_val AlgebraicGeometry.ProjSpace.twistObj.smul_val AlgebraicGeometry.ProjSpace.twistGradeEquiv_apply_val AlgebraicGeometry.ProjSpace.twistObj.mk.sizeOf_spec"

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

attribute [local instance] MvPolynomial.gradedAlgebra

theorem solution
    {R : Type u} [CommRing R] [IsNoetherianRing R] (I : Ideal R) [IsAdicComplete I R]
    {X Y : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of R)) (g : Y ⟶ Spec (CommRingCat.of R))
    (N : ℕ) (ιX : X ⟶ Proj (MvPolynomial.homogeneousSubmodule (Fin (N + 1)) R)) (hιX : IsClosedImmersion ιX)
    (hιXf : ιX ≫ ProjSpace.π R N = f)
    (N' : ℕ) (ιY : Y ⟶ Proj (MvPolynomial.homogeneousSubmodule (Fin (N' + 1)) R)) (hιY : IsClosedImmersion ιY)
    (hιYg : ιY ≫ ProjSpace.π R N' = g)
    (φ : ∀ n : ℕ, adicThickening f I n ⟶ adicThickening g I n)
    (hφ : ∀ n : ℕ, φ n ≫ adicThickeningToBase g I n = adicThickeningToBase f I n)
    (hφt : ∀ n : ℕ, adicThickeningTransition f I n ≫ φ (n + 1) = φ n ≫ adicThickeningTransition g I n) :
    ∃! ψ : X ⟶ Y, ψ ≫ g = f ∧ ∀ n : ℕ, adicThickeningι f I n ≫ ψ = φ n ≫ adicThickeningι g I n := by
  haveI := hιX; haveI := hιY
  haveI : IsSeparated g := by rw [← hιYg]; infer_instance

  obtain ⟨K, ιP, -, hιP, hιPp⟩ :=
    AlgebraicGeometry.exists_isClosedImmersion_projSpace_pullback_of_isClosedImmersion f g N ιX hιX hιXf N' ιY hιY hιYg

  have hgr : ∀ n : ℕ, adicThickeningι f I n ≫ f = (φ n ≫ adicThickeningι g I n) ≫ g := by
    intro n
    rw [adicThickeningι_comp, Category.assoc, adicThickeningι_comp, ← Category.assoc, hφ n]
  have hgrp : ∀ n : ℕ, pullback.lift (adicThickeningι f I n) (φ n ≫ adicThickeningι g I n) (hgr n) ≫ (pullback.fst f g ≫ f) =
      adicThickeningToBase f I n ≫ adicThickeningBase I n := by
    intro n
    rw [← Category.assoc, pullback.lift_fst, adicThickeningι_comp]
  obtain ⟨γ, hγdef⟩ : ∃ γ : ∀ n : ℕ, adicThickening f I n ⟶ adicThickening (pullback.fst f g ≫ f) I n, ∀ n, γ n =
      pullback.lift (pullback.lift (adicThickeningι f I n) (φ n ≫ adicThickeningι g I n) (hgr n)) (adicThickeningToBase f I n) (hgrp n) :=
    ⟨_, fun n => rfl⟩
  have hγ0 : ∀ n : ℕ, γ n ≫ adicThickeningι (pullback.fst f g ≫ f) I n =
      pullback.lift (adicThickeningι f I n) (φ n ≫ adicThickeningι g I n) (hgr n) := fun n => by
    rw [hγdef]; exact pullback.lift_fst _ _ _
  have hγ₁ : ∀ n : ℕ, γ n ≫ adicThickeningι (pullback.fst f g ≫ f) I n ≫ pullback.fst f g = adicThickeningι f I n := by
    intro n
    rw [← Category.assoc, hγ0, pullback.lift_fst]
  have hγ₂ : ∀ n : ℕ, γ n ≫ adicThickeningι (pullback.fst f g ≫ f) I n ≫ pullback.snd f g = φ n ≫ adicThickeningι g I n := by
    intro n
    rw [← Category.assoc, hγ0, pullback.lift_snd]
  have hGK := AlgebraicGeometry.isClosedImmersion_and_comap_ker_eq_ker_of_adicThickening_graph I f g φ hφ hφt γ hγ₁ hγ₂

  obtain ⟨J, hJ⟩ := AlgebraicGeometry.exists_idealSheafData_forall_comap_adicThickening_eq_of_isAdicComplete_of_isClosedImmersion_proj I
    (pullback.fst f g ≫ f) K ιP hιP hιPp (fun n => (γ n).ker) (fun n => (hGK n).2)

  have hζw : ∀ n : ℕ, (adicThickeningι (J.subschemeι ≫ pullback.fst f g ≫ f) I n ≫ J.subschemeι ≫ pullback.fst f g) ≫ f =
      adicThickeningToBase (J.subschemeι ≫ pullback.fst f g ≫ f) I n ≫ adicThickeningBase I n := by
    intro n
    rw [Category.assoc, Category.assoc, adicThickeningι_comp]
  let ζ : ∀ n : ℕ, adicThickening (J.subschemeι ≫ pullback.fst f g ≫ f) I n ⟶ adicThickening f I n := fun n =>
    pullback.lift (adicThickeningι (J.subschemeι ≫ pullback.fst f g ≫ f) I n ≫ J.subschemeι ≫ pullback.fst f g)
      (adicThickeningToBase (J.subschemeι ≫ pullback.fst f g ≫ f) I n) (hζw n)
  have hζ : ∀ n : ℕ, ζ n ≫ adicThickeningι f I n =
      adicThickeningι (J.subschemeι ≫ pullback.fst f g ≫ f) I n ≫ J.subschemeι ≫ pullback.fst f g := fun n => by
    rw [adicThickeningι_def]; exact pullback.lift_fst _ _ _
  have hζ' : ∀ n : ℕ, ζ n ≫ adicThickeningToBase f I n = adicThickeningToBase (J.subschemeι ≫ pullback.fst f g ≫ f) I n := fun n => by
    rw [adicThickeningToBase_def]; exact pullback.lift_snd _ _ _
  have hGT := fun n : ℕ => AlgebraicGeometry.isIso_and_adicThickening_comp_eq_of_comap_eq_ker_of_comp_eq I f g J γ
    (fun n => (hGK n).1) hJ hγ₁ n (ζ n) (hζ n)

  have hzι : IsClosedImmersion (J.subschemeι ≫ ιP) := inferInstance
  have hiso : IsIso (J.subschemeι ≫ pullback.fst f g) :=
    AlgebraicGeometry.isIso_of_forall_isIso_adicThickening_of_isAdicComplete_of_isClosedImmersion_proj I
      (J.subschemeι ≫ pullback.fst f g ≫ f) f K (J.subschemeι ≫ ιP) hzι (by rw [Category.assoc, hιPp]) N ιX hιX hιXf
      (J.subschemeι ≫ pullback.fst f g) (Category.assoc _ _ _) ζ hζ hζ' (fun n => (hGT n).1)

  refine ⟨inv (J.subschemeι ≫ pullback.fst f g) ≫ J.subschemeι ≫ pullback.snd f g, ⟨?_, ?_⟩, ?_⟩
  · rw [Category.assoc, Category.assoc, ← pullback.condition, ← Category.assoc (J.subschemeι), IsIso.inv_hom_id_assoc]
  · intro n
    haveI := (hGT n).1
    have e1 : adicThickeningι f I n = inv (ζ n) ≫ adicThickeningι (J.subschemeι ≫ pullback.fst f g ≫ f) I n ≫
        (J.subschemeι ≫ pullback.fst f g) := by
      rw [IsIso.eq_inv_comp, hζ n]
    rw [e1, Category.assoc, Category.assoc, IsIso.hom_inv_id_assoc, ← Category.assoc (adicThickeningι _ I n), (hGT n).2,
      Category.assoc, Category.assoc, IsIso.inv_hom_id_assoc, hγ₂ n]
  · rintro ψ' ⟨hψ'g, hψ'n⟩
    apply AlgebraicGeometry.eq_of_forall_adicThickening_comp_eq_of_isAdicComplete_of_isClosedImmersion_proj I f g N ιX hιX hιXf N' ιY hιY hιYg ψ' _ hψ'g
    · rw [Category.assoc, Category.assoc, ← pullback.condition, ← Category.assoc (J.subschemeι), IsIso.inv_hom_id_assoc]
    · intro n
      haveI := (hGT n).1
      have e1 : adicThickeningι f I n = inv (ζ n) ≫ adicThickeningι (J.subschemeι ≫ pullback.fst f g ≫ f) I n ≫
          (J.subschemeι ≫ pullback.fst f g) := by
        rw [IsIso.eq_inv_comp, hζ n]
      rw [hψ'n n]
      conv_rhs => rw [e1, Category.assoc, Category.assoc, IsIso.hom_inv_id_assoc, ← Category.assoc (adicThickeningι _ I n), (hGT n).2,
        Category.assoc, Category.assoc, IsIso.inv_hom_id_assoc, hγ₂ n]

end S_AlgebraicGeometry_existsUnique_hom_forall_adicThickening_comp_eq_of_isAdicComplete_of_isClosedImmersion_proj
end P2MW
export P2MW.S_AlgebraicGeometry_existsUnique_hom_forall_adicThickening_comp_eq_of_isAdicComplete_of_isClosedImmersion_proj (solution)
