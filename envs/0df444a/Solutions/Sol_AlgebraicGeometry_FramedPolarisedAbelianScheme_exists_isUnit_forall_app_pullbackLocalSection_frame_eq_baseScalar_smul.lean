-- Prove2me | solution 1 for AlgebraicGeometry.FramedPolarisedAbelianScheme.exists_isUnit_forall_app_pullbackLocalSection_frame_eq_baseScalar_smul
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:02.935278+00:00
-- url     : https://prove2.me/submissions/8c3d0b9c-4c10-5b7c-bc78-e5968f7c05cd

import Definitions.Def_AlgebraicGeometry_ThetaAdaptedFrame
import Definitions.Def_AlgebraicGeometry_ProjSpace

import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_ProjPresentation_exists_baseChange_of_isPullback
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_ProjPresentation_exists_of_iso
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_ProjPresentation_exists_projPresentation_pullback_sigma_eq_toProj_eq
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_pullbackComp_hom_app_pullbackLocalSection
import Theorems.Thm_AlgebraicGeometry_ProjSpace_isPullback_map
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_ProjPresentation_exists_unit_appTop_smul_eq_of_toProj_eq_of_bijective
import Theorems.Thm_GoodReductionJacobian_AbelianSchemePropertyBundle_bijective_algebraMap_sections_pullback
import Definitions.Def_AlgebraicGeometry_TwoAffineOpenCover
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_FramedPolarisedAbelianScheme_exists_isUnit_forall_app_pullbackLocalSection_frame_eq_baseScalar_smul
p2m_attr_erase "instance" "AlgebraicGeometry.SubalgebraStages.compactSpace_pullback AlgebraicGeometry.SubalgebraStages.quasiSeparatedSpace_pullback AlgebraicGeometry.SubalgebraStages.compactSpace_obj AlgebraicGeometry.SubalgebraStages.quasiSeparatedSpace_obj AlgebraicGeometry.SubalgebraStages.quasiCompact_snd AlgebraicGeometry.SubalgebraStages.isAffineHom_leg AlgebraicGeometry.SubalgebraStages.isAffineHom_trans AlgebraicGeometry.SubalgebraStages.isAffineHom_diagram_map AlgebraicGeometry.SubalgebraStages.quasiSeparated_snd AlgebraicGeometry.SubalgebraStages.isCofiltered_op IsDirectLimit.Module.instDirectLimitCoeLinearMapIdOfOfNonempty AdicCompletion.instIsLocalRingMaximalIdeal"
p2m_attr_erase "simp" "AlgebraicGeometry.Scheme.Modules.tensorPow_zero AlgebraicGeometry.Scheme.Modules.tensorPow_succ AlgebraicGeometry.Scheme.Modules.tensorSections_zero_right AlgebraicGeometry.Scheme.Modules.map_unitSection AlgebraicGeometry.Scheme.Modules.tensorSectionsBilin_apply AlgebraicGeometry.Scheme.Modules.tensorPowSection_zero AlgebraicGeometry.Scheme.Modules.tensorSections_zero_left AlgebraicGeometry.SubalgebraStages.specCone_π_app AlgebraicGeometry.SubalgebraStages.specLeg_specHom AlgebraicGeometry.SubalgebraStages.specLeg_specTrans AlgebraicGeometry.SubalgebraStages.cone_pt AlgebraicGeometry.SubalgebraStages.trans_fst AlgebraicGeometry.SubalgebraStages.diagram_obj AlgebraicGeometry.SubalgebraStages.leg_snd AlgebraicGeometry.SubalgebraStages.diagram_map AlgebraicGeometry.SubalgebraStages.specTrans_refl AlgebraicGeometry.SubalgebraStages.trans_snd AlgebraicGeometry.SubalgebraStages.specTrans_specHom AlgebraicGeometry.SubalgebraStages.specCone_pt AlgebraicGeometry.SubalgebraStages.cone_π_app AlgebraicGeometry.SubalgebraStages.specDiagram_map AlgebraicGeometry.SubalgebraStages.specDiagram_obj AlgebraicGeometry.SubalgebraStages.leg_fst AlgebraicGeometry.SubalgebraStages.leg_trans IsDirectLimit.Module.linearEquiv_symm_apply IsDirectLimit.linearEquiv_symm_apply IsDirectLimit.lift_of IsDirectLimit.Module.linearEquiv_apply IsDirectLimit.Module.lift_of IsDirectLimit.Equiv_apply RegularLocalRingQuotientAscent.dualNumberFst_apply GoodReductionJacobian.RelativeGroupLaw.baseChangePointToBase_ofBase GoodReductionJacobian.RelativeGroupLaw.baseChangePointToBase_coe GoodReductionJacobian.RelativeGroupLaw.baseChangePointOfBase_coe GoodReductionJacobian.RelativeGroupLaw.baseChange_inv GoodReductionJacobian.RelativeGroupLaw.baseChangePointOfBase_toBase GoodReductionJacobian.RelativeGroupLaw.baseChange_mul GoodReductionJacobian.RelativeGroupLaw.baseChange_one NeronModelInfra.NeronModelPropertyBundle.endExtensionEquiv_symm_restrict NeronModelInfra.schemeHomOverComp_id_left"
p2m_attr_erase "simp" "NeronModelInfra.schemeHomOverComp_id_right NeronModelInfra.schemeHomOverId_coe NeronModelInfra.NeronModelPropertyBundle.endExtensionEquiv_apply NeronModelInfra.NeronModelPropertyBundle.restrict_endExtensionEquiv_symm NeronModelInfra.schemeHomOverComp_coe NeronSpecialFibreInfra.specialFibreRestrict_coe_comp_fst NeronSpecialFibreInfra.fibreRestrictAlong_coe_comp_snd NeronSpecialFibreInfra.fibreRestrictAlong_coe_comp_fst NeronSpecialFibreInfra.neronEndRestrictEquiv_apply NeronSpecialFibreInfra.fibreRestrictAlong_coe_comp_fst_assoc NeronSpecialFibreInfra.specialFibreRestrict_coe_comp_snd NeronSpecialFibreInfra.neronEndExtension_genericFibreRestrict NeronSpecialFibreInfra.specClosedFibreInclusion_eq NeronSpecialFibreInfra.specialFibreRestrict_coe_comp_fst_assoc NeronSpecialFibreInfra.specialFibreRestrict_coe_comp_snd_assoc NeronSpecialFibreInfra.genericFibreRestrict_neronEndExtension NeronSpecialFibreInfra.homOverId_coe NeronSpecialFibreInfra.homOverComp_coe NeronSpecialFibreInfra.fibreRestrictAlong_coe_comp_snd_assoc GoodReductionJacobian.RelativeGroupLaw.fibre_inv GoodReductionJacobian.RelativeGroupLaw.fibrePointToBase_coe GoodReductionJacobian.RelativeGroupLaw.fibrePointOfBase_toBase GoodReductionJacobian.RelativeGroupLaw.fibre_mul GoodReductionJacobian.RelativeGroupLaw.fibrePointToBase_ofBase GoodReductionJacobian.RelativeGroupLaw.fibre_one GoodReductionJacobian.RelativeGroupLaw.fibrePointOfBase_coe AlgebraicGeometry.schemeFibreEndo_snd AlgebraicGeometry.schemeFibreEndo_fst"

set_option autoImplicit false

attribute [local instance] MvPolynomial.gradedAlgebra

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian AlgebraicGeometry.Polarisation
open scoped BigOperators

theorem solution
    {g N n : ℕ} {S S' : Type} [CommRing S] [CommRing S'] (φ : S →+* S')
    (X : FramedPolarisedAbelianScheme g N n S) (X' : FramedPolarisedAbelianScheme g N n S')
    (gA : X'.A ⟶ X.A) (hg : CategoryTheory.IsPullback gA X'.f X.f (Spec.map (CommRingCat.ofHom φ)))
    (hproj : letI : Algebra S S' := φ.toAlgebra; X'.frame.toProj ≫ ProjSpace.map S S' N = gA ≫ X.frame.toProj)
    (b : pullback X'.f (𝟙 (Spec (CommRingCat.of S'))) ⟶ pullback X.f (𝟙 (Spec (CommRingCat.of S))))
    (hb₁ : b ≫ pullback.fst X.f (𝟙 _) = pullback.fst X'.f (𝟙 _) ≫ gA)
    (hb₂ : b ≫ pullback.snd X.f (𝟙 _) = pullback.snd X'.f (𝟙 _) ≫ Spec.map (CommRingCat.ofHom φ))
    (c : (Scheme.Modules.pullback b).obj ((Scheme.Modules.pullback (pullback.fst X.f (𝟙 _))).obj X.pol) ≅
      (Scheme.Modules.pullback (pullback.fst X'.f (𝟙 _))).obj X'.pol)

    (τ : Fin (N + 1) → Γ((Scheme.Modules.pullback (pullback.fst X.f (𝟙 (Spec (CommRingCat.of S))))).obj X.pol, ⊤))
    (hτ : ∀ i : Fin (N + 1), τ i =
      (Scheme.Modules.pullbackLocalSection (pullback.fst X.f (𝟙 (Spec (CommRingCat.of S)))) (X.frame.σ i) :
        Γ((Scheme.Modules.pullback (pullback.fst X.f (𝟙 (Spec (CommRingCat.of S))))).obj X.pol,
          (pullback.fst X.f (𝟙 (Spec (CommRingCat.of S)))) ⁻¹ᵁ ⊤)))
    (τ' : Fin (N + 1) → Γ((Scheme.Modules.pullback (pullback.fst X'.f (𝟙 (Spec (CommRingCat.of S'))))).obj X'.pol, ⊤))
    (hτ' : ∀ i : Fin (N + 1), τ' i =
      (Scheme.Modules.pullbackLocalSection (pullback.fst X'.f (𝟙 (Spec (CommRingCat.of S')))) (X'.frame.σ i) :
        Γ((Scheme.Modules.pullback (pullback.fst X'.f (𝟙 (Spec (CommRingCat.of S'))))).obj X'.pol,
          (pullback.fst X'.f (𝟙 (Spec (CommRingCat.of S')))) ⁻¹ᵁ ⊤))) :
    ∃ u : S', IsUnit u ∧ ∀ i : Fin (N + 1),
      c.hom.app ⊤ (Scheme.Modules.pullbackLocalSection b (τ i) :
          Γ((Scheme.Modules.pullback b).obj ((Scheme.Modules.pullback (pullback.fst X.f (𝟙 _))).obj X.pol), ⊤)) =
        Polarisation.baseScalar X'.f (𝟙 (Spec (CommRingCat.of S'))) u • τ' i := by
  classical
  letI algφ : Algebra S S' := φ.toAlgebra
  have hφ : (algebraMap S S' : S →+* S') = φ := rfl
  haveI : IsIso (pullback.fst X'.f (𝟙 (Spec (CommRingCat.of S')))) := inferInstance
  have hsnd' : (pullback.fst X'.f (𝟙 (Spec (CommRingCat.of S')))) ≫ X'.f = (pullback.snd X'.f (𝟙 (Spec (CommRingCat.of S')))) := by rw [pullback.condition, Category.comp_id]

  have sq : IsPullback (b ≫ (pullback.fst X.f (𝟙 (Spec (CommRingCat.of S))))) (pullback.snd X'.f (𝟙 (Spec (CommRingCat.of S')))) X.f (Spec.map (CommRingCat.ofHom (algebraMap S S'))) := by
    rw [hb₁, ← hsnd', hφ]
    exact IsPullback.of_iso hg (asIso (pullback.fst X'.f (𝟙 (Spec (CommRingCat.of S'))))).symm (Iso.refl _) (Iso.refl _) (Iso.refl _)
      (by simp) (by simp) (by simp) (by simp)

  obtain ⟨𝔅, h𝔅σ, h𝔅proj, -⟩ :=
    AlgebraicGeometry.Scheme.Modules.ProjPresentation.exists_baseChange_of_isPullback sq X.frame

  let κ : (Scheme.Modules.pullback (b ≫ (pullback.fst X.f (𝟙 (Spec (CommRingCat.of S)))))).obj X.pol ≅ (Scheme.Modules.pullback (pullback.fst X'.f (𝟙 (Spec (CommRingCat.of S'))))).obj X'.pol :=
    ((Scheme.Modules.pullbackComp b (pullback.fst X.f (𝟙 (Spec (CommRingCat.of S))))).app X.pol).symm ≪≫ c
  obtain ⟨𝔅', h𝔅'proj, h𝔅'σ⟩ := AlgebraicGeometry.Scheme.Modules.ProjPresentation.exists_of_iso 𝔅 κ
  have hσB : ∀ i, 𝔅'.σ i = c.hom.app ⊤ (Scheme.Modules.pullbackLocalSection b (τ i) :
      Γ((Scheme.Modules.pullback b).obj ((Scheme.Modules.pullback (pullback.fst X.f (𝟙 _))).obj X.pol), ⊤)) := by
    intro i
    rw [h𝔅'σ, h𝔅σ, hτ i]
    show c.hom.app ⊤ (((Scheme.Modules.pullbackComp b (pullback.fst X.f (𝟙 (Spec (CommRingCat.of S))))).app X.pol).inv.app ⊤
      (Scheme.Modules.pullbackLocalSection (b ≫ (pullback.fst X.f (𝟙 (Spec (CommRingCat.of S))))) (X.frame.σ i))) = _
    congr 1
    have h := AlgebraicGeometry.Scheme.Modules.pullbackComp_hom_app_pullbackLocalSection b (pullback.fst X.f (𝟙 (Spec (CommRingCat.of S)))) X.pol ⊤ (X.frame.σ i)
    rw [← h]
    change (((Scheme.Modules.pullbackComp b (pullback.fst X.f (𝟙 (Spec (CommRingCat.of S))))).hom.app X.pol) ≫
      ((Scheme.Modules.pullbackComp b (pullback.fst X.f (𝟙 (Spec (CommRingCat.of S))))).inv.app X.pol)).app ⊤ _ = _
    rw [Iso.hom_inv_id_app, Scheme.Modules.Hom.id_app]
    rfl

  obtain ⟨𝔄, h𝔄σ, h𝔄proj⟩ : ∃ 𝔄 : Scheme.Modules.ProjPresentation ((Scheme.Modules.pullback (pullback.fst X'.f (𝟙 (Spec (CommRingCat.of S'))))).obj X'.pol) (pullback.snd X'.f (𝟙 (Spec (CommRingCat.of S')))) N,
      (∀ i, 𝔄.σ i = (((Scheme.Modules.pullbackPushforwardAdjunction (pullback.fst X'.f (𝟙 (Spec (CommRingCat.of S'))))).unit.app X'.pol).app ⊤) (X'.frame.σ i)) ∧
      𝔄.toProj = (pullback.fst X'.f (𝟙 (Spec (CommRingCat.of S')))) ≫ X'.frame.toProj := by
    have key : ∀ (f₀ : pullback X'.f (𝟙 (Spec (CommRingCat.of S'))) ⟶ Spec (CommRingCat.of S')) (hf : (pullback.fst X'.f (𝟙 (Spec (CommRingCat.of S')))) ≫ X'.f = f₀),
        ∃ 𝔄 : Scheme.Modules.ProjPresentation ((Scheme.Modules.pullback (pullback.fst X'.f (𝟙 (Spec (CommRingCat.of S'))))).obj X'.pol) f₀ N,
          (∀ i, 𝔄.σ i = (((Scheme.Modules.pullbackPushforwardAdjunction (pullback.fst X'.f (𝟙 (Spec (CommRingCat.of S'))))).unit.app X'.pol).app ⊤) (X'.frame.σ i)) ∧
          𝔄.toProj = (pullback.fst X'.f (𝟙 (Spec (CommRingCat.of S')))) ≫ X'.frame.toProj := by
      intro f₀ hf
      subst hf
      exact AlgebraicGeometry.Scheme.Modules.ProjPresentation.exists_projPresentation_pullback_sigma_eq_toProj_eq _ _
    exact key _ hsnd'
  have hσA : ∀ i, 𝔄.σ i = τ' i := fun i => by rw [h𝔄σ, hτ' i]; rfl

  have hproj' : 𝔄.toProj = 𝔅'.toProj := by
    rw [h𝔅'proj, h𝔄proj]
    apply (AlgebraicGeometry.ProjSpace.isPullback_map S S' N).hom_ext
    · rw [Category.assoc, hproj, ← Category.assoc, ← hb₁, h𝔅proj, Category.assoc]
    · rw [Category.assoc, X'.frame.toProj_π, 𝔅.toProj_π, hsnd']

  have hΓ : Function.Bijective fun r : S' => (pullback.snd X'.f (𝟙 (Spec (CommRingCat.of S')))).appTop ((Scheme.ΓSpecIso (.of S')).inv r) := by
    have heq : Scheme.TwoAffineOpenCover.specMap S' S' = 𝟙 (Spec (CommRingCat.of S')) := by
      show Spec.map (CommRingCat.ofHom (RingHom.id S')) = 𝟙 _
      rw [CommRingCat.ofHom_id, Spec.map_id]
    have hQ := X'.bundle.bijective_algebraMap_sections_pullback S'
    let e : pullback X'.f (Scheme.TwoAffineOpenCover.specMap S' S') ≅ pullback X'.f (𝟙 (Spec (CommRingCat.of S'))) :=
      pullback.congrHom rfl heq
    have he : e.hom ≫ (pullback.snd X'.f (𝟙 (Spec (CommRingCat.of S')))) = pullback.snd X'.f (Scheme.TwoAffineOpenCover.specMap S' S') := by
      simp only [e, pullback.congrHom, pullback.map, Category.comp_id]
      exact pullback.lift_snd _ _ _

    have hfun : (fun r : S' => (pullback.snd X'.f (𝟙 (Spec (CommRingCat.of S')))).appTop ((Scheme.ΓSpecIso (.of S')).inv r)) =
        (fun y => e.inv.appTop y) ∘
          (fun r : S' => (pullback.snd X'.f (Scheme.TwoAffineOpenCover.specMap S' S')).appTop ((Scheme.ΓSpecIso (.of S')).inv r)) := by
      funext r
      show _ = e.inv.appTop ((pullback.snd X'.f (Scheme.TwoAffineOpenCover.specMap S' S')).appTop _)
      rw [← he, Scheme.Hom.comp_appTop]
      change _ = ((e.hom.appTop ≫ e.inv.appTop)) (((pullback.snd X'.f (𝟙 (Spec (CommRingCat.of S'))))).appTop _)
      rw [← Scheme.Hom.comp_appTop, Iso.inv_hom_id, Scheme.Hom.id_appTop]
      rfl
    have hbij_e : Function.Bijective (fun y => e.inv.appTop y) := by
      refine Function.bijective_iff_has_inverse.mpr ⟨fun z => e.hom.appTop z, fun y => ?_, fun z => ?_⟩
      · change (e.inv.appTop ≫ e.hom.appTop) y = y
        rw [← Scheme.Hom.comp_appTop, Iso.hom_inv_id, Scheme.Hom.id_appTop]; rfl
      · change (e.hom.appTop ≫ e.inv.appTop) z = z
        rw [← Scheme.Hom.comp_appTop, Iso.inv_hom_id, Scheme.Hom.id_appTop]; rfl
    have hQ' : Function.Bijective (fun r : S' =>
        (pullback.snd X'.f (Scheme.TwoAffineOpenCover.specMap S' S')).appTop ((Scheme.ΓSpecIso (.of S')).inv r)) := by
      convert hQ using 2 with r
      rw [Scheme.TwoAffineOpenCover.algebraMap_algebraOfHom]
      simp [Scheme.Hom.appLE, Scheme.Hom.appTop]
    rw [hfun]
    exact hbij_e.comp hQ'

  obtain ⟨u, hu⟩ := AlgebraicGeometry.Scheme.Modules.ProjPresentation.exists_unit_appTop_smul_eq_of_toProj_eq_of_bijective
    𝔄 𝔅' hproj' hΓ
  refine ⟨(u : S'), u.isUnit, fun i => ?_⟩
  rw [← hσB i, hu i, hσA i]
  rfl

end S_AlgebraicGeometry_FramedPolarisedAbelianScheme_exists_isUnit_forall_app_pullbackLocalSection_frame_eq_baseScalar_smul
end P2MW
export P2MW.S_AlgebraicGeometry_FramedPolarisedAbelianScheme_exists_isUnit_forall_app_pullbackLocalSection_frame_eq_baseScalar_smul (solution)
