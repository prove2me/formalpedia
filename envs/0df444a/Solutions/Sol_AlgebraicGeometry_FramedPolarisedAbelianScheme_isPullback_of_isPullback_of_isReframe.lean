-- Prove2me | solution 1 for AlgebraicGeometry.FramedPolarisedAbelianScheme.isPullback_of_isPullback_of_isReframe
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:02.935278+00:00
-- url     : https://prove2.me/submissions/c345cdae-14c5-5fc3-a774-a3e7344e264f

import Definitions.Def_AlgebraicGeometry_ThetaReframe
import Definitions.Def_AlgebraicGeometry_ThetaLevelGroup
import Definitions.Def_AlgebraicGeometry_ProjSpace
import Definitions.Def_AlgebraicGeometry_ModulesPullbackLocalSection
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_ProjPresentation_exists_projPresentation_pullback_sigma_eq_toProj_eq
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_ProjPresentation_exists_of_iso
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_ProjPresentation_exists_sigma_eq_toProj_eq_comp_map_of_algebraMap
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_ProjPresentation_exists_unit_smul_eq_of_toProj_eq
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_ProjPresentation_toProj_eq_of_sigma_eq_smul
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_FramedPolarisedAbelianScheme_isPullback_of_isPullback_of_isReframe
p2m_attr_erase "instance" "AlgebraicGeometry.ProjSpace.twistObj.addCommGroup AlgebraicGeometry.ProjSpace.twistFam.module AlgebraicGeometry.ProjSpace.twistObj.module AlgebraicGeometry.ProjSpace.twistObj.moduleSections AlgebraicGeometry.ProjSpace.twistFam.addCommGroup AlgebraicGeometry.OModulePresheaf.isScalarTower AlgebraicGeometry.Scheme.OrderedAffineCover.instLinearOrder AlgebraicGeometry.OModulePresheaf.module AlgebraicGeometry.Scheme.OrderedAffineCover.instFintype AlgebraicGeometry.Scheme.OrderedAffineCover.instFintypeIdx AlgebraicGeometry.OModulePresheaf.addCommGroup AlgebraicGeometry.Scheme.OrderedAffineCover.instDecidableEqIdx AlgebraicGeometry.OModulePresheaf.moduleSections TwoChartCech.Sections.M0_moduleA TwoChartCech.Sections.M1_module TwoChartCech.Cover.A01_algebra TwoChartCech.Cover.A0_algebra TwoChartCech.Cover.A1_commRing TwoChartCech.Cover.A1_algebra TwoChartCech.Sections.M01_module TwoChartCech.Sections.M0_addCommGroup TwoChartCech.Sections.M0_tower TwoChartCech.Sections.M01_addCommGroup TwoChartCech.Cover.A0_commRing TwoChartCech.Sections.M1_tower TwoChartCech.Sections.M01_moduleA TwoChartCech.Sections.M0_module TwoChartCech.Sections.M1_moduleA TwoChartCech.Sections.M1_addCommGroup TwoChartCech.Cover.A01_commRing TwoChartCech.Sections.M01_tower CoherentBaseChange.TwoTermComplex.C0_module CoherentBaseChange.TwoTermComplex.C0_addCommGroup CoherentBaseChange.TwoTermComplex.C1_module CoherentBaseChange.TwoTermComplex.C1_addCommGroup CoherentBaseChange.TwoTermComplex.C0_free CoherentBaseChange.TwoTermComplex.C1_finite CoherentBaseChange.TwoTermComplex.C0_finite CoherentBaseChange.TwoTermComplex.C1_free ProjSpaceCech.GradedModule.H.module"
p2m_attr_erase "instance" "ProjSpaceCech.GradedModule.H.addCommGroup ProjSpaceCech.GradedModule.sec.instAdd ProjSpaceCech.GradedModule.sec.instNeg ProjSpaceCech.GradedModule.acg ProjSpaceCech.GradedModule.Frac.setoid ProjSpaceCech.GradedModule.modR ProjSpaceCech.GradedModule.sec.instModule ProjSpaceCech.GradedModule.sec.instAddCommGroup ProjSpaceCech.GradedModule.sec.instZero ProjSpaceCech.GradedModule.Presentation.fJ ProjSpaceCech.GradedModule.sec.instSMul ProjSpaceCech.Twist.H.module ProjSpaceCech.Idx.instFintype ProjSpaceCech.Twist.H.addCommGroup ProjSpaceCech.Idx.instDecidableEq ProjSpaceCech.Twist.Mon.instDecidableEq ProjSpaceCech.Twist.cochain.instAddCommGroup ProjSpaceCech.Twist.cochain.instModule"
p2m_attr_erase "simp" "AlgebraicGeometry.ProjSpace.twistObj.mk.injEq AlgebraicGeometry.ProjSpace.twistObj.zero_val AlgebraicGeometry.ProjSpace.twistObj.add_val AlgebraicGeometry.ProjSpace.twist_res_val AlgebraicGeometry.ProjSpace.twist_smul_val AlgebraicGeometry.ProjSpace.twistGradeToObj_val AlgebraicGeometry.ProjSpace.twistObj.smul_val AlgebraicGeometry.ProjSpace.twistGradeEquiv_apply_val AlgebraicGeometry.ProjSpace.twistObj.mk.sizeOf_spec AlgebraicGeometry.Scheme.OrderedAffineCover.mk.injEq AlgebraicGeometry.OModulePresheaf.mk.sizeOf_spec AlgebraicGeometry.Scheme.OrderedAffineCover.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.mk.injEq AlgebraicGeometry.Scheme.TwoAffineOpenCover.mk.injEq AlgebraicGeometry.Scheme.TwoAffineOpenCover.mk.sizeOf_spec AlgebraicGeometry.Scheme.TwoAffineOpenCover.pullback_U1 AlgebraicGeometry.Scheme.TwoAffineOpenCover.pullback_U0 TwoChartCech.Sections.mk.injEq TwoChartCech.Cover.mk.injEq TwoChartCech.GrothendieckComplex.mk.injEq TwoChartCech.Sections.mk.sizeOf_spec TwoChartCech.Cover.mk.sizeOf_spec TwoChartCech.Cover.lineBundle_r0_apply TwoChartCech.GrothendieckComplex.mk.sizeOf_spec TwoChartCech.Cover.lineBundle_r1_apply CoherentBaseChange.TwoTermComplex.mk.sizeOf_spec CoherentBaseChange.TwoTermComplex.mk.injEq ProjSpaceCech.GradedModule.mk.injEq ProjSpaceCech.GradedModule.mk.sizeOf_spec ProjSpaceCech.GradedModule.Frac.mk.sizeOf_spec ProjSpaceCech.GradedModule.Presentation.mk.injEq ProjSpaceCech.GradedModule.Frac.mk.injEq ProjSpaceCech.GradedModule.Presentation.mk.sizeOf_spec ProjSpaceCech.GradedModule.Hom.shift_toLinearMap ProjSpaceCech.GradedModule.Hom.mk.sizeOf_spec ProjSpaceCech.GradedModule.Hom.mk.injEq AlgebraicGeometry.Scheme.Modules.tensorPow_zero AlgebraicGeometry.Scheme.Modules.tensorPow_succ AlgebraicGeometry.Scheme.Modules.tensorSections_zero_right AlgebraicGeometry.Scheme.Modules.map_unitSection"
p2m_attr_erase "simp" "AlgebraicGeometry.Scheme.Modules.tensorSectionsBilin_apply AlgebraicGeometry.Scheme.Modules.tensorPowSection_zero AlgebraicGeometry.Scheme.Modules.tensorSections_zero_left"

set_option autoImplicit false

attribute [local instance] MvPolynomial.gradedAlgebra

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian AlgebraicGeometry.Polarisation
open scoped BigOperators

namespace CL5_29

noncomputable def copyBase {R : Type} [CommRing R] {X : Scheme.{0}} {M : X.Modules} {f f' : X ⟶ Spec (.of R)} {N : ℕ}
    (h : f = f') (P : M.ProjPresentation f N) : M.ProjPresentation f' N :=
  ⟨P.σ, P.toProj, P.toProj_π.trans h, P.frame, P.app_ratio_smul⟩

@[scoped simp] theorem copyBase_σ {R : Type} [CommRing R] {X : Scheme.{0}} {M : X.Modules} {f f' : X ⟶ Spec (.of R)} {N : ℕ}
    (h : f = f') (P : M.ProjPresentation f N) (i : Fin (N + 1)) : (copyBase h P).σ i = P.σ i := rfl

@[scoped simp] theorem copyBase_toProj {R : Type} [CommRing R] {X : Scheme.{0}} {M : X.Modules} {f f' : X ⟶ Spec (.of R)} {N : ℕ}
    (h : f = f') (P : M.ProjPresentation f N) : (copyBase h P).toProj = P.toProj := rfl

end CL5_29
p2m_reactivate "P2MW.S_AlgebraicGeometry_FramedPolarisedAbelianScheme_isPullback_of_isPullback_of_isReframe.CL5_29"

open CL5_29 in
theorem solution
    {g N n : ℕ} {S S' : Type} [CommRing S] [CommRing S'] (φ : S →+* S') (U : Matrix (Fin (N + 1)) (Fin (N + 1)) S)
    (X X' : FramedPolarisedAbelianScheme g N n S) (Y Y' : FramedPolarisedAbelianScheme g N n S')
    (h : FramedPolarisedAbelianScheme.IsPullback φ X Y) (hX : X.IsReframe U X') (hY : Y.IsReframe (U.map φ) Y') :
    FramedPolarisedAbelianScheme.IsPullback φ X' Y' := by
  classical
  obtain ⟨P', hP'ci, hP'b, rfl, hσP⟩ := hX
  obtain ⟨Q', hQ'ci, hQ'b, rfl, hσQ⟩ := hY
  obtain ⟨gA, hg, hlaw, hPt, hpol, hfr⟩ := h
  refine ⟨gA, hg, hlaw, hPt, hpol, ?_⟩
  letI : Algebra S S' := φ.toAlgebra

  obtain ⟨PX, hPXσ, hPXt⟩ :=
    AlgebraicGeometry.Scheme.Modules.ProjPresentation.exists_projPresentation_pullback_sigma_eq_toProj_eq gA X.frame
  obtain ⟨PX', hPX'σ, hPX't⟩ :=
    AlgebraicGeometry.Scheme.Modules.ProjPresentation.exists_projPresentation_pullback_sigma_eq_toProj_eq gA P'

  obtain ⟨e⟩ := hpol
  obtain ⟨PY, hPYt, hPYσ⟩ := AlgebraicGeometry.Scheme.Modules.ProjPresentation.exists_of_iso PX e
  obtain ⟨PY', hPY't, hPY'σ⟩ := AlgebraicGeometry.Scheme.Modules.ProjPresentation.exists_of_iso PX' e

  obtain ⟨QY, hQYσ, hQYt⟩ :=
    AlgebraicGeometry.Scheme.Modules.ProjPresentation.exists_sigma_eq_toProj_eq_comp_map_of_algebraMap (R := S) (A := S') Y.frame
  obtain ⟨QY', hQY'σ, hQY't⟩ :=
    AlgebraicGeometry.Scheme.Modules.ProjPresentation.exists_sigma_eq_toProj_eq_comp_map_of_algebraMap (R := S) (A := S') Q'
  have hbase : gA ≫ X.f = Y.f ≫ Spec.map (CommRingCat.ofHom (algebraMap S S')) := hg.w

  have htp : QY.toProj = (copyBase hbase PY).toProj := by
    rw [copyBase_toProj, hPYt, hPXt, hQYt]; exact hfr
  obtain ⟨u, hu⟩ := AlgebraicGeometry.Scheme.Modules.ProjPresentation.exists_unit_smul_eq_of_toProj_eq QY (copyBase hbase PY) htp

  have hsc : ∀ i j : Fin (N + 1),
      gA.app ⊤ ((X.f.appLE ⊤ ⊤ le_top).hom ((Scheme.ΓSpecIso (CommRingCat.of S)).inv.hom (U i j))) =
        (Y.f.appLE ⊤ ⊤ le_top).hom ((Scheme.ΓSpecIso (CommRingCat.of S')).inv.hom ((U.map φ) i j)) := by
    intro i j
    have e1 : X.f.appLE ⊤ ⊤ le_top = X.f.appTop := (Scheme.Hom.app_eq_appLE X.f).symm
    have e2 : Y.f.appLE ⊤ ⊤ le_top = Y.f.appTop := (Scheme.Hom.app_eq_appLE Y.f).symm
    rw [e1, e2, Matrix.map_apply]
    have h1 : (X.f.appTop ≫ gA.appTop) = (Spec.map (CommRingCat.ofHom φ)).appTop ≫ Y.f.appTop := by
      rw [← Scheme.Hom.comp_appTop, ← Scheme.Hom.comp_appTop, hg.w]
    have h2 := congrArg (fun k => k.hom ((Scheme.ΓSpecIso (CommRingCat.of S)).inv.hom (U i j))) h1
    simp only [CommRingCat.hom_comp, RingHom.comp_apply] at h2
    have h3 := Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom φ)
    have h4 := congrArg (fun k => k.hom (U i j)) h3
    simp only [CommRingCat.hom_comp, RingHom.comp_apply, CommRingCat.hom_ofHom] at h4
    exact h2.trans (congrArg _ h4.symm)

  have hu' : ∀ i, (copyBase hbase PY').σ i = (u : Γ(Y.A, ⊤)) • QY'.σ i := by
    intro i
    have huj : ∀ j, (ConcreteCategory.hom (Scheme.Modules.Hom.app e.hom (gA ⁻¹ᵁ ⊤)))
        (Scheme.Modules.pullbackLocalSection gA (X.frame.σ j)) = (u : Γ(Y.A, ⊤)) • Y.frame.σ j := fun j => by
      have := hu j
      rw [copyBase_σ, hPYσ, hPXσ, hQYσ] at this
      exact this
    rw [copyBase_σ, hPY'σ, hPX'σ, hQY'σ, hσQ, hσP]
    show (ConcreteCategory.hom (Scheme.Modules.Hom.app e.hom (gA ⁻¹ᵁ ⊤)))
        (Scheme.Modules.pullbackLocalSection gA
          (∑ j, (X.f.appLE ⊤ ⊤ le_top).hom ((Scheme.ΓSpecIso (CommRingCat.of S)).inv.hom (U i j)) • X.frame.σ j)) = _
    rw [Scheme.Modules.pullbackLocalSection_sum, map_sum (ConcreteCategory.hom (Scheme.Modules.Hom.app e.hom (gA ⁻¹ᵁ ⊤))),
      Finset.smul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [Scheme.Modules.pullbackLocalSection_smul, Scheme.Modules.Hom.app_smul, huj j, ← hsc i j]
    set c : Γ(Y.A, ⊤) := (gA.app ⊤) ((X.f.appLE ⊤ ⊤ le_top).hom ((Scheme.ΓSpecIso (CommRingCat.of S)).inv.hom (U i j))) with hc
    show c • ((u : Γ(Y.A, ⊤)) • Y.frame.σ j) = (u : Γ(Y.A, ⊤)) • (c • Y.frame.σ j)
    rw [smul_smul, smul_smul, mul_comm]
  have key := AlgebraicGeometry.Scheme.Modules.ProjPresentation.toProj_eq_of_sigma_eq_smul QY' (copyBase hbase PY')
    (u : Γ(Y.A, ⊤)) u.isUnit hu'
  rw [copyBase_toProj, hPY't, hPX't, hQY't] at key
  exact key.symm

end S_AlgebraicGeometry_FramedPolarisedAbelianScheme_isPullback_of_isPullback_of_isReframe
end P2MW
export P2MW.S_AlgebraicGeometry_FramedPolarisedAbelianScheme_isPullback_of_isPullback_of_isReframe (solution)
