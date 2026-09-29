-- Prove2me | solution 1 for AlgebraicGeometry.FramedPolarisedAbelianScheme.isThetaAdapted_of_isPullback
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:02.935278+00:00
-- url     : https://prove2.me/submissions/ddfc7944-98cb-5a47-97a7-4e62dc5b3598

import Definitions.Def_AlgebraicGeometry_ThetaAdaptedFrame
import Definitions.Def_AlgebraicGeometry_ProjSpace
import Definitions.Def_AlgebraicGeometry_ThetaGroupLaw
import Theorems.Thm_AlgebraicGeometry_FramedPolarisedAbelianScheme_bijective_sum_baseScalar_smul_of_eq_pullbackLocalSection_frame
import Theorems.Thm_AlgebraicGeometry_Polarisation_SchrodingerFrame_exists_sigma_eq_baseScalar_smul_of_isUnit
import Theorems.Thm_AlgebraicGeometry_Polarisation_ThetaPt_exists_monoidHom_pt_comp_eq_act_eq_of_isPullback
import Theorems.Thm_AlgebraicGeometry_FramedPolarisedAbelianScheme_exists_isUnit_forall_app_pullbackLocalSection_frame_eq_baseScalar_smul
import Theorems.Thm_AlgebraicGeometry_Polarisation_ThetaPt_exists_forall_act_eq_baseScalar_addChar_smul_of_forall_addMonoidHom
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_FramedPolarisedAbelianScheme_isThetaAdapted_of_isPullback
p2m_attr_erase "instance" "TwoChartCech.Sections.M0_moduleA TwoChartCech.Sections.M1_module TwoChartCech.Cover.A01_algebra TwoChartCech.Cover.A0_algebra TwoChartCech.Cover.A1_commRing TwoChartCech.Cover.A1_algebra TwoChartCech.Sections.M01_module TwoChartCech.Sections.M0_addCommGroup TwoChartCech.Sections.M0_tower TwoChartCech.Sections.M01_addCommGroup TwoChartCech.Cover.A0_commRing TwoChartCech.Sections.M1_tower TwoChartCech.Sections.M01_moduleA TwoChartCech.Sections.M0_module TwoChartCech.Sections.M1_moduleA TwoChartCech.Sections.M1_addCommGroup TwoChartCech.Cover.A01_commRing TwoChartCech.Sections.M01_tower CoherentBaseChange.TwoTermComplex.C0_module CoherentBaseChange.TwoTermComplex.C0_addCommGroup CoherentBaseChange.TwoTermComplex.C1_module CoherentBaseChange.TwoTermComplex.C1_addCommGroup CoherentBaseChange.TwoTermComplex.C0_free CoherentBaseChange.TwoTermComplex.C1_finite CoherentBaseChange.TwoTermComplex.C0_finite CoherentBaseChange.TwoTermComplex.C1_free AlgebraicGeometry.SubalgebraStages.compactSpace_pullback AlgebraicGeometry.SubalgebraStages.quasiSeparatedSpace_pullback AlgebraicGeometry.SubalgebraStages.compactSpace_obj AlgebraicGeometry.SubalgebraStages.quasiSeparatedSpace_obj AlgebraicGeometry.SubalgebraStages.quasiCompact_snd AlgebraicGeometry.SubalgebraStages.isAffineHom_leg AlgebraicGeometry.SubalgebraStages.isAffineHom_trans AlgebraicGeometry.SubalgebraStages.isAffineHom_diagram_map AlgebraicGeometry.SubalgebraStages.quasiSeparated_snd AlgebraicGeometry.SubalgebraStages.isCofiltered_op IsDirectLimit.Module.instDirectLimitCoeLinearMapIdOfOfNonempty AdicCompletion.instIsLocalRingMaximalIdeal"
p2m_attr_erase "simp" "AlgebraicGeometry.Scheme.Modules.tensorPow_zero AlgebraicGeometry.Scheme.Modules.tensorPow_succ AlgebraicGeometry.Scheme.Modules.tensorSections_zero_right AlgebraicGeometry.Scheme.Modules.map_unitSection AlgebraicGeometry.Scheme.Modules.tensorSectionsBilin_apply AlgebraicGeometry.Scheme.Modules.tensorPowSection_zero AlgebraicGeometry.Scheme.Modules.tensorSections_zero_left AlgebraicGeometry.Scheme.TwoAffineOpenCover.mk.injEq AlgebraicGeometry.Scheme.TwoAffineOpenCover.mk.sizeOf_spec AlgebraicGeometry.Scheme.TwoAffineOpenCover.pullback_U1 AlgebraicGeometry.Scheme.TwoAffineOpenCover.pullback_U0 TwoChartCech.Sections.mk.injEq TwoChartCech.Cover.mk.injEq TwoChartCech.GrothendieckComplex.mk.injEq TwoChartCech.Sections.mk.sizeOf_spec TwoChartCech.Cover.mk.sizeOf_spec TwoChartCech.Cover.lineBundle_r0_apply TwoChartCech.GrothendieckComplex.mk.sizeOf_spec TwoChartCech.Cover.lineBundle_r1_apply CoherentBaseChange.TwoTermComplex.mk.sizeOf_spec CoherentBaseChange.TwoTermComplex.mk.injEq AlgebraicGeometry.SubalgebraStages.specCone_π_app AlgebraicGeometry.SubalgebraStages.specLeg_specHom AlgebraicGeometry.SubalgebraStages.specLeg_specTrans AlgebraicGeometry.SubalgebraStages.cone_pt AlgebraicGeometry.SubalgebraStages.trans_fst AlgebraicGeometry.SubalgebraStages.diagram_obj AlgebraicGeometry.SubalgebraStages.leg_snd AlgebraicGeometry.SubalgebraStages.diagram_map AlgebraicGeometry.SubalgebraStages.specTrans_refl AlgebraicGeometry.SubalgebraStages.trans_snd AlgebraicGeometry.SubalgebraStages.specTrans_specHom AlgebraicGeometry.SubalgebraStages.specCone_pt AlgebraicGeometry.SubalgebraStages.cone_π_app AlgebraicGeometry.SubalgebraStages.specDiagram_map AlgebraicGeometry.SubalgebraStages.specDiagram_obj AlgebraicGeometry.SubalgebraStages.leg_fst AlgebraicGeometry.SubalgebraStages.leg_trans IsDirectLimit.Module.linearEquiv_symm_apply IsDirectLimit.linearEquiv_symm_apply"
p2m_attr_erase "simp" "IsDirectLimit.lift_of IsDirectLimit.Module.linearEquiv_apply IsDirectLimit.Module.lift_of IsDirectLimit.Equiv_apply RegularLocalRingQuotientAscent.dualNumberFst_apply GoodReductionJacobian.RelativeGroupLaw.baseChangePointToBase_ofBase GoodReductionJacobian.RelativeGroupLaw.baseChangePointToBase_coe GoodReductionJacobian.RelativeGroupLaw.baseChangePointOfBase_coe GoodReductionJacobian.RelativeGroupLaw.baseChange_inv GoodReductionJacobian.RelativeGroupLaw.baseChangePointOfBase_toBase GoodReductionJacobian.RelativeGroupLaw.baseChange_mul GoodReductionJacobian.RelativeGroupLaw.baseChange_one NeronSpecialFibreInfra.specialFibreRestrict_coe_comp_fst NeronSpecialFibreInfra.fibreRestrictAlong_coe_comp_snd NeronSpecialFibreInfra.fibreRestrictAlong_coe_comp_fst NeronSpecialFibreInfra.neronEndRestrictEquiv_apply NeronSpecialFibreInfra.fibreRestrictAlong_coe_comp_fst_assoc NeronSpecialFibreInfra.specialFibreRestrict_coe_comp_snd NeronSpecialFibreInfra.neronEndExtension_genericFibreRestrict NeronSpecialFibreInfra.specClosedFibreInclusion_eq NeronSpecialFibreInfra.specialFibreRestrict_coe_comp_fst_assoc NeronSpecialFibreInfra.specialFibreRestrict_coe_comp_snd_assoc NeronSpecialFibreInfra.genericFibreRestrict_neronEndExtension NeronSpecialFibreInfra.homOverId_coe NeronSpecialFibreInfra.homOverComp_coe NeronSpecialFibreInfra.fibreRestrictAlong_coe_comp_snd_assoc GoodReductionJacobian.RelativeGroupLaw.fibre_inv GoodReductionJacobian.RelativeGroupLaw.fibrePointToBase_coe GoodReductionJacobian.RelativeGroupLaw.fibrePointOfBase_toBase GoodReductionJacobian.RelativeGroupLaw.fibre_mul GoodReductionJacobian.RelativeGroupLaw.fibrePointToBase_ofBase GoodReductionJacobian.RelativeGroupLaw.fibre_one GoodReductionJacobian.RelativeGroupLaw.fibrePointOfBase_coe AlgebraicGeometry.schemeFibreEndo_snd AlgebraicGeometry.schemeFibreEndo_fst"

set_option autoImplicit false

attribute [local instance] MvPolynomial.gradedAlgebra

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian AlgebraicGeometry.Polarisation
open scoped BigOperators TensorProduct

theorem solution
    {g N n : ℕ} (δ : Fin g → ℕ) [hδ : ∀ i, NeZero (δ i)] (e : Fin (N + 1) ≃ ((i : Fin g) → ZMod (δ i)))
    {S S' : Type} [CommRing S] [CommRing S'] (φ : S →+* S')
    (ζ : S) (hζ : ζ ^ (N + 1) = 1) (hζu : ∀ j : ℕ, 0 < j → j < N + 1 → IsUnit (1 - ζ ^ j))
    (X : FramedPolarisedAbelianScheme g N n S) (X' : FramedPolarisedAbelianScheme g N n S')
    (h : FramedPolarisedAbelianScheme.IsPullback φ X X') (hX : X.IsThetaAdapted δ e) :
    X'.IsThetaAdapted δ e := by
  classical
  obtain ⟨F, hF⟩ := hX
  obtain ⟨gA, hg, hmul, hP, ⟨ιpol⟩, hproj⟩ := h

  set pr := pullback.fst X.f (𝟙 (Spec (CommRingCat.of S))) with hpr
  set pr' := pullback.fst X'.f (𝟙 (Spec (CommRingCat.of S'))) with hpr'
  have hcond : (pr' ≫ gA) ≫ X.f =
      (pullback.snd X'.f (𝟙 _) ≫ Spec.map (CommRingCat.ofHom φ)) ≫ 𝟙 (Spec (CommRingCat.of S)) := by
    rw [Category.assoc, hg.w, ← Category.assoc, Category.comp_id]
    simp only [hpr']
    rw [pullback.condition, Category.assoc, Category.id_comp]
  let b : pullback X'.f (𝟙 (Spec (CommRingCat.of S'))) ⟶ pullback X.f (𝟙 (Spec (CommRingCat.of S))) :=
    pullback.lift (pr' ≫ gA) (pullback.snd X'.f (𝟙 _) ≫ Spec.map (CommRingCat.ofHom φ)) hcond
  have hb₁ : b ≫ pullback.fst X.f (𝟙 _) = pullback.fst X'.f (𝟙 _) ≫ gA := pullback.lift_fst _ _ _
  have hb₂ : b ≫ pullback.snd X.f (𝟙 _) = pullback.snd X'.f (𝟙 _) ≫ Spec.map (CommRingCat.ofHom φ) := pullback.lift_snd _ _ _

  let c : (Scheme.Modules.pullback b).obj ((Scheme.Modules.pullback (pullback.fst X.f (𝟙 _))).obj X.pol) ≅
      (Scheme.Modules.pullback (pullback.fst X'.f (𝟙 _))).obj X'.pol :=
    (Scheme.Modules.pullbackComp b (pullback.fst X.f (𝟙 _))).app X.pol ≪≫
      (Scheme.Modules.pullbackCongr hb₁).app X.pol ≪≫
      ((Scheme.Modules.pullbackComp (pullback.fst X'.f (𝟙 _)) gA).app X.pol).symm ≪≫
      (Scheme.Modules.pullback (pullback.fst X'.f (𝟙 _))).mapIso ιpol

  have hr : Spec.map (CommRingCat.ofHom φ) ≫ 𝟙 (Spec (CommRingCat.of S)) =
      𝟙 (Spec (CommRingCat.of S')) ≫ Spec.map (CommRingCat.ofHom φ) := by simp
  obtain ⟨β, hβpt, hβact, hβsc, hβu⟩ :=
    AlgebraicGeometry.Polarisation.ThetaPt.exists_monoidHom_pt_comp_eq_act_eq_of_isPullback φ X.L X'.L gA hg hmul X.pol X'.pol (𝟙 _) (𝟙 _) φ hr b hb₁ hb₂ c

  let T : Γ((Scheme.Modules.pullback (pullback.fst X.f (𝟙 (Spec (CommRingCat.of S))))).obj X.pol, ⊤) →
      Γ((Scheme.Modules.pullback (pullback.fst X'.f (𝟙 (Spec (CommRingCat.of S'))))).obj X'.pol, ⊤) :=
    fun s => c.hom.app ⊤ (Scheme.Modules.pullbackLocalSection b s :
      Γ((Scheme.Modules.pullback b).obj ((Scheme.Modules.pullback (pullback.fst X.f (𝟙 _))).obj X.pol), ⊤))
  have hTact : ∀ (θ : ThetaPt X.f X.L X.pol (𝟙 _)) s, (β θ).act (T s) = T (θ.act s) := fun θ s => hβact θ s

  let σ' : ((i : Fin g) → ZMod (δ i)) →
      Γ((Scheme.Modules.pullback (pullback.fst X'.f (𝟙 (Spec (CommRingCat.of S'))))).obj X'.pol, ⊤) :=
    fun hh => (Scheme.Modules.pullbackLocalSection (pullback.fst X'.f (𝟙 (Spec (CommRingCat.of S')))) (X'.frame.σ (e.symm hh)) :
      Γ((Scheme.Modules.pullback (pullback.fst X'.f (𝟙 (Spec (CommRingCat.of S'))))).obj X'.pol,
        (pullback.fst X'.f (𝟙 (Spec (CommRingCat.of S')))) ⁻¹ᵁ ⊤))
  have hσ' : ∀ i : Fin (N + 1), σ' (e i) =
      (Scheme.Modules.pullbackLocalSection (pullback.fst X'.f (𝟙 (Spec (CommRingCat.of S')))) (X'.frame.σ i) :
        Γ((Scheme.Modules.pullback (pullback.fst X'.f (𝟙 (Spec (CommRingCat.of S'))))).obj X'.pol,
          (pullback.fst X'.f (𝟙 (Spec (CommRingCat.of S')))) ⁻¹ᵁ ⊤)) := by
    intro i; simp only [σ', Equiv.symm_apply_apply]
  obtain ⟨u, hu, hunit⟩ := AlgebraicGeometry.FramedPolarisedAbelianScheme.exists_isUnit_forall_app_pullbackLocalSection_frame_eq_baseScalar_smul φ X X' gA hg hproj b hb₁ hb₂ c (fun i => F.σ (e i)) hF (fun i => σ' (e i)) hσ'
  have hTσ : ∀ hh, T (F.σ hh) = Polarisation.baseScalar X'.f (𝟙 _) u • σ' hh := by
    intro hh; have := hunit (e.symm hh); simpa only [Equiv.apply_symm_apply] using this

  have hbapp : ∀ r : S, b.app ⊤ (Polarisation.baseScalar X.f (𝟙 (Spec (CommRingCat.of S))) r) =
      Polarisation.baseScalar X'.f (𝟙 (Spec (CommRingCat.of S'))) (φ r) := by
    intro r
    show (b.appTop).hom ((pullback.snd X.f (𝟙 _)).appTop.hom ((Scheme.ΓSpecIso (CommRingCat.of S)).inv.hom r)) =
      (pullback.snd X'.f (𝟙 _)).appTop.hom ((Scheme.ΓSpecIso (CommRingCat.of S')).inv.hom (φ r))
    rw [← CommRingCat.comp_apply, ← Scheme.Hom.comp_appTop, hb₂, Scheme.Hom.comp_appTop, CommRingCat.comp_apply]
    congr 1
    have := Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom φ)
    exact (congrArg (fun k => (CommRingCat.Hom.hom k) r) this).symm
  have hTsmul : ∀ (r : S) (s : Γ((Scheme.Modules.pullback (pullback.fst X.f (𝟙 (Spec (CommRingCat.of S))))).obj X.pol, ⊤)),
      T (Polarisation.baseScalar X.f (𝟙 _) r • s) = Polarisation.baseScalar X'.f (𝟙 _) (φ r) • T s := by
    intro r s
    simp only [T]
    rw [Scheme.Modules.pullbackLocalSection_smul]
    refine (Scheme.Modules.Hom.app_smul c.hom _ _).trans ?_
    exact congrArg (fun x => x • T s) (hbapp r)

  have hφζ : (φ ζ) ^ (N + 1) = 1 := by rw [← map_pow, hζ, map_one]
  have hφζu : ∀ j : ℕ, 0 < j → j < N + 1 → IsUnit (1 - (φ ζ) ^ j) := by
    intro j hj hj'; have := (hζu j hj hj').map φ; simpa using this
  have hpowmod : ∀ m : ℕ, ζ ^ m = ζ ^ (m % (N + 1)) := by
    intro m; conv_lhs => rw [← Nat.mod_add_div m (N + 1), pow_add, pow_mul, hζ, one_pow, mul_one]
  let χS : (((i : Fin g) → ZMod (δ i)) →+ ZMod (N + 1)) → AddChar ((i : Fin g) → ZMod (δ i)) S := fun cc =>
    { toFun := fun hh => ζ ^ (cc hh).val
      map_zero_eq_one' := by simp
      map_add_eq_mul' := by
        intro a a'
        simp only [map_add]
        rw [ZMod.val_add, ← hpowmod, pow_add] }
  have hχS : ∀ cc hh, χS cc hh = ζ ^ (cc hh).val := fun _ _ => rfl

  have hbs_mul : ∀ a a' : S', Polarisation.baseScalar X'.f (𝟙 (Spec (CommRingCat.of S'))) (a * a') =
      Polarisation.baseScalar X'.f (𝟙 _) a * Polarisation.baseScalar X'.f (𝟙 _) a' := by
    intro a a'; rw [← Polarisation.baseScalarHom_apply, map_mul]; rfl
  have hGbasis : Function.Bijective fun cc : ((i : Fin g) → ZMod (δ i)) → S' =>
      ∑ hh, Polarisation.baseScalar X'.f (𝟙 (Spec (CommRingCat.of S'))) (cc hh) • T (F.σ hh) := by
    have hFB := AlgebraicGeometry.FramedPolarisedAbelianScheme.bijective_sum_baseScalar_smul_of_eq_pullbackLocalSection_frame
      δ e X' σ' hσ'
    have hmulu : Function.Bijective fun cc : ((i : Fin g) → ZMod (δ i)) → S' => fun hh => cc hh * u := by
      obtain ⟨v, hv⟩ := hu
      refine Function.bijective_iff_has_inverse.mpr ⟨fun cc => fun hh => cc hh * ↑v⁻¹, ?_, ?_⟩
      · intro cc; funext hh; simp [← hv, mul_assoc]
      · intro cc; funext hh; simp [← hv, mul_assoc]
    have : (fun cc : ((i : Fin g) → ZMod (δ i)) → S' =>
        ∑ hh, Polarisation.baseScalar X'.f (𝟙 (Spec (CommRingCat.of S'))) (cc hh) • T (F.σ hh)) =
        (fun cc : ((i : Fin g) → ZMod (δ i)) → S' =>
          ∑ hh, Polarisation.baseScalar X'.f (𝟙 (Spec (CommRingCat.of S'))) (cc hh) • σ' hh) ∘
        (fun cc => fun hh => cc hh * u) := by
      funext cc
      simp only [Function.comp_apply, hTσ, smul_smul, hbs_mul]
    rw [this]
    exact hFB.comp hmulu
  have hDLA := fun χ' : AddChar ((i : Fin g) → ZMod (δ i)) S' =>
    AlgebraicGeometry.Polarisation.ThetaPt.exists_forall_act_eq_baseScalar_addChar_smul_of_forall_addMonoidHom X'.f X'.L X'.pol (𝟙 _) N (φ ζ) hφζ hφζu δ e (fun hh => T (F.σ hh))
      (fun cc => β (F.dualLift (χS cc)))
      (by
        intro cc hh
        rw [hTact, F.dualLift_act, hTsmul, hχS, map_pow])
      χ'
  let G : Polarisation.SchrodingerFrame X'.f X'.L X'.pol (𝟙 (Spec (CommRingCat.of S'))) δ :=
    { σ := fun hh => T (F.σ hh)
      basis := hGbasis
      lift := fun hh => β (F.lift hh)
      dualLift := fun χ' => (hDLA χ').choose
      lift_act := by intro hh hh'; rw [hTact, F.lift_act]
      dualLift_act := by intro χ' hh; exact (hDLA χ').choose_spec hh }

  obtain ⟨F', hF'σ, -, -⟩ :=
    AlgebraicGeometry.Polarisation.SchrodingerFrame.exists_sigma_eq_baseScalar_smul_of_isUnit G (↑hu.unit⁻¹ : S') (Units.isUnit _)
  refine ⟨F', fun i => ?_⟩
  rw [hF'σ, ← hσ' i]
  show Polarisation.baseScalar X'.f (𝟙 _) (↑hu.unit⁻¹ : S') • T (F.σ (e i)) = σ' (e i)
  rw [hTσ, smul_smul, ← hbs_mul, Units.inv_mul_of_eq hu.unit_spec, ← Polarisation.baseScalarHom_apply, map_one, one_smul]

end S_AlgebraicGeometry_FramedPolarisedAbelianScheme_isThetaAdapted_of_isPullback
end P2MW
export P2MW.S_AlgebraicGeometry_FramedPolarisedAbelianScheme_isThetaAdapted_of_isPullback (solution)
