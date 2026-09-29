-- Prove2me | solution 1 for AlgebraicGeometry.FramedPolarisedAbelianScheme.iso_of_iso_of_isPullback_of_isPullback
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:02.935278+00:00
-- url     : https://prove2.me/submissions/7816ee69-06cb-5c7d-8250-f08431f84bc9

import Definitions.Def_AlgebraicGeometry_ThetaAdaptedFrame
import Definitions.Def_AlgebraicGeometry_ProjSpace

import Theorems.Thm_AlgebraicGeometry_ProjSpace_isPullback_map
import Theorems.Thm_AlgebraicGeometry_FramedPolarisedAbelianScheme_iso_of_iso_comp_toProj_eq_of_one_comp_toProj_eq_of_forall_comp_toProj_eq
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_FramedPolarisedAbelianScheme_iso_of_iso_of_isPullback_of_isPullback
p2m_attr_erase "instance" "AlgebraicGeometry.SubalgebraStages.compactSpace_pullback AlgebraicGeometry.SubalgebraStages.quasiSeparatedSpace_pullback AlgebraicGeometry.SubalgebraStages.compactSpace_obj AlgebraicGeometry.SubalgebraStages.quasiSeparatedSpace_obj AlgebraicGeometry.SubalgebraStages.quasiCompact_snd AlgebraicGeometry.SubalgebraStages.isAffineHom_leg AlgebraicGeometry.SubalgebraStages.isAffineHom_trans AlgebraicGeometry.SubalgebraStages.isAffineHom_diagram_map AlgebraicGeometry.SubalgebraStages.quasiSeparated_snd AlgebraicGeometry.SubalgebraStages.isCofiltered_op IsDirectLimit.Module.instDirectLimitCoeLinearMapIdOfOfNonempty AdicCompletion.instIsLocalRingMaximalIdeal"
p2m_attr_erase "simp" "GoodReductionJacobian.prodInr_comp_prodFst GoodReductionJacobian.RelativeGroupLaw.prod_inv GoodReductionJacobian.prodInl_comp_prodSnd GoodReductionJacobian.prodInr_comp_prodSnd GoodReductionJacobian.prodInl_comp_prodFst GoodReductionJacobian.prodFstPt_prodPairPt GoodReductionJacobian.prodFst_coe GoodReductionJacobian.prodSndPt_prodPairPt GoodReductionJacobian.RelativeGroupLaw.prod_one GoodReductionJacobian.prodPairPt_coe GoodReductionJacobian.prodPairPt_prodFstPt_prodSndPt GoodReductionJacobian.prodFstPt_coe GoodReductionJacobian.RelativeGroupLaw.prod_mul GoodReductionJacobian.prodSndPt_coe GoodReductionJacobian.prodSnd_coe AlgebraicGeometry.SubalgebraStages.specCone_π_app AlgebraicGeometry.SubalgebraStages.specLeg_specHom AlgebraicGeometry.SubalgebraStages.specLeg_specTrans AlgebraicGeometry.SubalgebraStages.cone_pt AlgebraicGeometry.SubalgebraStages.trans_fst AlgebraicGeometry.SubalgebraStages.diagram_obj AlgebraicGeometry.SubalgebraStages.leg_snd AlgebraicGeometry.SubalgebraStages.diagram_map AlgebraicGeometry.SubalgebraStages.specTrans_refl AlgebraicGeometry.SubalgebraStages.trans_snd AlgebraicGeometry.SubalgebraStages.specTrans_specHom AlgebraicGeometry.SubalgebraStages.specCone_pt AlgebraicGeometry.SubalgebraStages.cone_π_app AlgebraicGeometry.SubalgebraStages.specDiagram_map AlgebraicGeometry.SubalgebraStages.specDiagram_obj AlgebraicGeometry.SubalgebraStages.leg_fst AlgebraicGeometry.SubalgebraStages.leg_trans IsDirectLimit.Module.linearEquiv_symm_apply IsDirectLimit.linearEquiv_symm_apply IsDirectLimit.lift_of IsDirectLimit.Module.linearEquiv_apply IsDirectLimit.Module.lift_of IsDirectLimit.Equiv_apply GoodReductionJacobian.RelativeGroupLaw.fibre_inv GoodReductionJacobian.RelativeGroupLaw.fibrePointToBase_coe"
p2m_attr_erase "simp" "GoodReductionJacobian.RelativeGroupLaw.fibrePointOfBase_toBase GoodReductionJacobian.RelativeGroupLaw.fibre_mul GoodReductionJacobian.RelativeGroupLaw.fibrePointToBase_ofBase GoodReductionJacobian.RelativeGroupLaw.fibre_one GoodReductionJacobian.RelativeGroupLaw.fibrePointOfBase_coe AlgebraicGeometry.schemeFibreEndo_snd AlgebraicGeometry.schemeFibreEndo_fst RegularLocalRingQuotientAscent.dualNumberFst_apply GoodReductionJacobian.RelativeGroupLaw.baseChangePointToBase_ofBase GoodReductionJacobian.RelativeGroupLaw.baseChangePointToBase_coe GoodReductionJacobian.RelativeGroupLaw.baseChangePointOfBase_coe GoodReductionJacobian.RelativeGroupLaw.baseChange_inv GoodReductionJacobian.RelativeGroupLaw.baseChangePointOfBase_toBase GoodReductionJacobian.RelativeGroupLaw.baseChange_mul GoodReductionJacobian.RelativeGroupLaw.baseChange_one NeronSpecialFibreInfra.specialFibreRestrict_coe_comp_fst NeronSpecialFibreInfra.fibreRestrictAlong_coe_comp_snd NeronSpecialFibreInfra.fibreRestrictAlong_coe_comp_fst NeronSpecialFibreInfra.neronEndRestrictEquiv_apply NeronSpecialFibreInfra.fibreRestrictAlong_coe_comp_fst_assoc NeronSpecialFibreInfra.specialFibreRestrict_coe_comp_snd NeronSpecialFibreInfra.neronEndExtension_genericFibreRestrict NeronSpecialFibreInfra.specClosedFibreInclusion_eq NeronSpecialFibreInfra.specialFibreRestrict_coe_comp_fst_assoc NeronSpecialFibreInfra.specialFibreRestrict_coe_comp_snd_assoc NeronSpecialFibreInfra.genericFibreRestrict_neronEndExtension NeronSpecialFibreInfra.homOverId_coe NeronSpecialFibreInfra.homOverComp_coe NeronSpecialFibreInfra.fibreRestrictAlong_coe_comp_snd_assoc AlgebraicGeometry.Scheme.Modules.tensorPow_zero AlgebraicGeometry.Scheme.Modules.tensorPow_succ AlgebraicGeometry.Scheme.Modules.tensorSections_zero_right AlgebraicGeometry.Scheme.Modules.map_unitSection AlgebraicGeometry.Scheme.Modules.tensorSectionsBilin_apply AlgebraicGeometry.Scheme.Modules.tensorPowSection_zero AlgebraicGeometry.Scheme.Modules.tensorSections_zero_left"

set_option autoImplicit false

attribute [local instance] MvPolynomial.gradedAlgebra

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian AlgebraicGeometry.Polarisation
open scoped BigOperators TensorProduct

theorem solution
    {g N n : ℕ} {S T : Type} [CommRing S] [CommRing T] (φ : S →+* T)
    (X X' : FramedPolarisedAbelianScheme g N n S) (Y Y' : FramedPolarisedAbelianScheme g N n T)
    (hXX' : FramedPolarisedAbelianScheme.Iso X X')
    (hY : FramedPolarisedAbelianScheme.IsPullback φ X Y) (hY' : FramedPolarisedAbelianScheme.IsPullback φ X' Y') :
    FramedPolarisedAbelianScheme.Iso Y Y' := by
  classical
  letI algφ : Algebra S T := φ.toAlgebra
  obtain ⟨e, he, heι, hehom, heP, -⟩ := hXX'
  obtain ⟨gA, hg, hhom, hPY, -, hιY⟩ := hY
  obtain ⟨gA', hg', hhom', hPY', -, hιY'⟩ := hY'
  have he' : e.inv ≫ X.f = X'.f := by rw [← he, Iso.inv_hom_id_assoc]

  have w₁ : (gA ≫ e.hom) ≫ X'.f = Y.f ≫ Spec.map (CommRingCat.ofHom φ) := by rw [Category.assoc, he, hg.w]
  have w₂ : (gA' ≫ e.inv) ≫ X.f = Y'.f ≫ Spec.map (CommRingCat.ofHom φ) := by rw [Category.assoc, he', hg'.w]
  let e₀h : Y.A ⟶ Y'.A := hg'.lift (gA ≫ e.hom) Y.f w₁
  let e₀i : Y'.A ⟶ Y.A := hg.lift (gA' ≫ e.inv) Y'.f w₂
  have h₁ : e₀h ≫ gA' = gA ≫ e.hom := hg'.lift_fst _ _ _
  have h₂ : e₀h ≫ Y'.f = Y.f := hg'.lift_snd _ _ _
  have h₃ : e₀i ≫ gA = gA' ≫ e.inv := hg.lift_fst _ _ _
  have h₄ : e₀i ≫ Y.f = Y'.f := hg.lift_snd _ _ _
  let e₀ : Y.A ≅ Y'.A :=
    { hom := e₀h, inv := e₀i,
      hom_inv_id := by
        apply hg.hom_ext
        · rw [Category.assoc, h₃, ← Category.assoc, h₁, Category.assoc, Iso.hom_inv_id, Category.comp_id, Category.id_comp]
        · rw [Category.assoc, h₄, h₂, Category.id_comp]
      inv_hom_id := by
        apply hg'.hom_ext
        · rw [Category.assoc, h₁, ← Category.assoc, h₃, Category.assoc, Iso.inv_hom_id, Category.comp_id, Category.id_comp]
        · rw [Category.assoc, h₂, h₄, Category.id_comp] }

  have hPB := AlgebraicGeometry.ProjSpace.isPullback_map S T N
  have he₀ι : e₀.hom ≫ Y'.frame.toProj = Y.frame.toProj := by
    apply hPB.hom_ext
    · rw [Category.assoc, hιY', ← Category.assoc, h₁, Category.assoc, heι, hιY]
    · rw [Category.assoc, Y'.frame.toProj_π, Y.frame.toProj_π]
      exact h₂

  have one_gA : ∀ {Z : FramedPolarisedAbelianScheme g N n T} {W : FramedPolarisedAbelianScheme g N n S} (γ : Z.A ⟶ W.A)
      (hγ : CategoryTheory.IsPullback γ Z.f W.f (Spec.map (CommRingCat.ofHom φ)))
      (hγhom : ∀ {T' : Scheme.{0}} (t' : T' ⟶ Spec (CommRingCat.of T)) (x y : SchemeHomOver t' Z.f),
        (Z.L.mul t' x y).1 ≫ γ =
          (W.L.mul (t' ≫ Spec.map (CommRingCat.ofHom φ))
            ⟨x.1 ≫ γ, by rw [Category.assoc, hγ.w, ← Category.assoc, x.2]⟩
            ⟨y.1 ≫ γ, by rw [Category.assoc, hγ.w, ← Category.assoc, y.2]⟩).1),
      (Z.L.one (𝟙 (Spec (CommRingCat.of T)))).1 ≫ γ = (W.L.one (𝟙 (Spec (CommRingCat.of T)) ≫ Spec.map (CommRingCat.ofHom φ))).1 := by
    intro Z W γ hγ hγhom
    letI : Group (SchemeHomOver (𝟙 (Spec (CommRingCat.of T)) ≫ Spec.map (CommRingCat.ofHom φ)) W.f) := W.L.pointGroup _
    have h11 := hγhom (𝟙 _) (Z.L.one _) (Z.L.one _)
    rw [Z.L.one_mul] at h11
    let a : SchemeHomOver (𝟙 (Spec (CommRingCat.of T)) ≫ Spec.map (CommRingCat.ofHom φ)) W.f :=
      ⟨(Z.L.one (𝟙 _)).1 ≫ γ, by rw [Category.assoc, hγ.w, ← Category.assoc, (Z.L.one (𝟙 _)).2]⟩
    have h11' : a * a = a * 1 := by rw [mul_one]; exact (Subtype.ext h11).symm
    exact congrArg Subtype.val (mul_left_cancel h11')
  have one_e : (X.L.one (𝟙 (Spec (CommRingCat.of T)) ≫ Spec.map (CommRingCat.ofHom φ))).1 ≫ e.hom =
      (X'.L.one (𝟙 (Spec (CommRingCat.of T)) ≫ Spec.map (CommRingCat.ofHom φ))).1 := by
    letI : Group (SchemeHomOver (𝟙 (Spec (CommRingCat.of T)) ≫ Spec.map (CommRingCat.ofHom φ)) X'.f) := X'.L.pointGroup _
    have h11 := hehom (𝟙 (Spec (CommRingCat.of T)) ≫ Spec.map (CommRingCat.ofHom φ)) (X.L.one _) (X.L.one _)
    rw [X.L.one_mul] at h11
    let a : SchemeHomOver (𝟙 (Spec (CommRingCat.of T)) ≫ Spec.map (CommRingCat.ofHom φ)) X'.f :=
      ⟨(X.L.one _).1 ≫ e.hom, by rw [Category.assoc, he]; exact (X.L.one _).2⟩
    have h11' : a * a = a * 1 := by rw [mul_one]; exact (Subtype.ext h11).symm
    exact congrArg Subtype.val (mul_left_cancel h11')
  have hone : (Y.L.one (𝟙 (Spec (CommRingCat.of T)))).1 ≫ Y.frame.toProj = (Y'.L.one (𝟙 (Spec (CommRingCat.of T)))).1 ≫ Y'.frame.toProj := by
    apply hPB.hom_ext
    · have eqL : ((Y.L.one (𝟙 (Spec (CommRingCat.of T)))).1 ≫ Y.frame.toProj) ≫ ProjSpace.map S T N =
          (X.L.one (𝟙 (Spec (CommRingCat.of T)) ≫ Spec.map (CommRingCat.ofHom φ))).1 ≫ X.frame.toProj := by
        rw [Category.assoc, hιY, ← Category.assoc, one_gA gA hg hhom]
      have eqR : ((Y'.L.one (𝟙 (Spec (CommRingCat.of T)))).1 ≫ Y'.frame.toProj) ≫ ProjSpace.map S T N =
          (X.L.one (𝟙 (Spec (CommRingCat.of T)) ≫ Spec.map (CommRingCat.ofHom φ))).1 ≫ X.frame.toProj := by
        rw [Category.assoc, hιY', ← Category.assoc, one_gA gA' hg' hhom', ← one_e, Category.assoc, heι]
      rw [eqL, eqR]
    · rw [Category.assoc, Y.frame.toProj_π, Category.assoc, Y'.frame.toProj_π, (Y.L.one _).2, (Y'.L.one _).2]
  have hPsec : ∀ i, (Y.P i).1 ≫ Y.frame.toProj = (Y'.P i).1 ≫ Y'.frame.toProj := by
    intro i
    apply hPB.hom_ext
    · have eqL : ((Y.P i).1 ≫ Y.frame.toProj) ≫ ProjSpace.map S T N =
          Spec.map (CommRingCat.ofHom φ) ≫ (X.P i).1 ≫ X.frame.toProj := by
        rw [Category.assoc, hιY, ← Category.assoc, hPY i, Category.assoc]
      have eqR : ((Y'.P i).1 ≫ Y'.frame.toProj) ≫ ProjSpace.map S T N =
          Spec.map (CommRingCat.ofHom φ) ≫ (X.P i).1 ≫ X.frame.toProj := by
        rw [Category.assoc, hιY', ← Category.assoc, hPY' i, Category.assoc, ← heP i, Category.assoc, heι]
      rw [eqL, eqR]
    · rw [Category.assoc, Y.frame.toProj_π, Category.assoc, Y'.frame.toProj_π, (Y.P i).2, (Y'.P i).2]
  exact AlgebraicGeometry.FramedPolarisedAbelianScheme.iso_of_iso_comp_toProj_eq_of_one_comp_toProj_eq_of_forall_comp_toProj_eq
    Y Y' e₀ h₂ he₀ι hone hPsec

end S_AlgebraicGeometry_FramedPolarisedAbelianScheme_iso_of_iso_of_isPullback_of_isPullback
end P2MW
export P2MW.S_AlgebraicGeometry_FramedPolarisedAbelianScheme_iso_of_iso_of_isPullback_of_isPullback (solution)
