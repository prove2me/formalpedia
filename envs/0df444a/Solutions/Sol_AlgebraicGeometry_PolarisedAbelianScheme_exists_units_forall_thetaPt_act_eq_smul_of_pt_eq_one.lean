-- Prove2me | solution 1 for AlgebraicGeometry.PolarisedAbelianScheme.exists_units_forall_thetaPt_act_eq_smul_of_pt_eq_one
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:02.935278+00:00
-- url     : https://prove2.me/submissions/9f8260b0-4f3a-5000-8ce1-05b1802458b0

import Definitions.Def_AlgebraicGeometry_ThetaGroupLaw
import Definitions.Def_AlgebraicGeometry_ThetaLevelGroup
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_IsInvertible_exists_forall_app_eq_smul
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_IsInvertible_eq_one_of_forall_smul_eq
import Theorems.Thm_GoodReductionJacobian_AbelianSchemePropertyBundle_bijective_specIso_inv_comp_appTop_of_isPullback
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_PolarisedAbelianScheme_exists_units_forall_thetaPt_act_eq_smul_of_pt_eq_one
p2m_attr_erase "instance" "TwoChartCech.Sections.M0_moduleA TwoChartCech.Sections.M1_module TwoChartCech.Cover.A01_algebra TwoChartCech.Cover.A0_algebra TwoChartCech.Cover.A1_commRing TwoChartCech.Cover.A1_algebra TwoChartCech.Sections.M01_module TwoChartCech.Sections.M0_addCommGroup TwoChartCech.Sections.M0_tower TwoChartCech.Sections.M01_addCommGroup TwoChartCech.Cover.A0_commRing TwoChartCech.Sections.M1_tower TwoChartCech.Sections.M01_moduleA TwoChartCech.Sections.M0_module TwoChartCech.Sections.M1_moduleA TwoChartCech.Sections.M1_addCommGroup TwoChartCech.Cover.A01_commRing TwoChartCech.Sections.M01_tower CoherentBaseChange.TwoTermComplex.C0_module CoherentBaseChange.TwoTermComplex.C0_addCommGroup CoherentBaseChange.TwoTermComplex.C1_module CoherentBaseChange.TwoTermComplex.C1_addCommGroup CoherentBaseChange.TwoTermComplex.C0_free CoherentBaseChange.TwoTermComplex.C1_finite CoherentBaseChange.TwoTermComplex.C0_finite CoherentBaseChange.TwoTermComplex.C1_free AlgebraicGeometry.SubalgebraStages.compactSpace_pullback AlgebraicGeometry.SubalgebraStages.quasiSeparatedSpace_pullback AlgebraicGeometry.SubalgebraStages.compactSpace_obj AlgebraicGeometry.SubalgebraStages.quasiSeparatedSpace_obj AlgebraicGeometry.SubalgebraStages.quasiCompact_snd AlgebraicGeometry.SubalgebraStages.isAffineHom_leg AlgebraicGeometry.SubalgebraStages.isAffineHom_trans AlgebraicGeometry.SubalgebraStages.isAffineHom_diagram_map AlgebraicGeometry.SubalgebraStages.quasiSeparated_snd AlgebraicGeometry.SubalgebraStages.isCofiltered_op IsDirectLimit.Module.instDirectLimitCoeLinearMapIdOfOfNonempty AdicCompletion.instIsLocalRingMaximalIdeal"
p2m_attr_erase "simp" "AlgebraicGeometry.Scheme.Modules.toUnitSection_ofUnitSection AlgebraicGeometry.Scheme.Modules.pullbackSection_def AlgebraicGeometry.Scheme.Modules.ofUnitSection_toUnitSection AlgebraicGeometry.RelEffCartierDiv.toRelEffDivisor_ofRelEffDivisor AlgebraicGeometry.RelEffCartierDiv.toRelEffDivisor_I AlgebraicGeometry.mapOnProdOver_fst_assoc AlgebraicGeometry.RelEffCartierDiv.mk.sizeOf_spec AlgebraicGeometry.RelEffCartierDiv.mk.injEq AlgebraicGeometry.mapOnProdOver_snd AlgebraicGeometry.mapOnProdOver_fst AlgebraicGeometry.mapOnProdOver_snd_assoc AlgebraicGeometry.mapOnProdOver_id AlgebraicCurve.RelEffDivisor.mk.sizeOf_spec AlgebraicCurve.mapOnProd_fst AlgebraicCurve.mapOnProd_fst_assoc AlgebraicCurve.mapOnProd_snd AlgebraicCurve.UnivDivisorPack.mk.injEq AlgebraicCurve.RelEffDivisor.mk.injEq AlgebraicCurve.UnivDivisorPack.mk.sizeOf_spec AlgebraicCurve.mapOnProd_snd_assoc AlgebraicGeometry.Scheme.TwoAffineOpenCover.mk.injEq AlgebraicGeometry.Scheme.TwoAffineOpenCover.mk.sizeOf_spec AlgebraicGeometry.Scheme.TwoAffineOpenCover.pullback_U1 AlgebraicGeometry.Scheme.TwoAffineOpenCover.pullback_U0 TwoChartCech.Sections.mk.injEq TwoChartCech.Cover.mk.injEq TwoChartCech.GrothendieckComplex.mk.injEq TwoChartCech.Sections.mk.sizeOf_spec TwoChartCech.Cover.mk.sizeOf_spec TwoChartCech.Cover.lineBundle_r0_apply TwoChartCech.GrothendieckComplex.mk.sizeOf_spec TwoChartCech.Cover.lineBundle_r1_apply CoherentBaseChange.TwoTermComplex.mk.sizeOf_spec CoherentBaseChange.TwoTermComplex.mk.injEq AlgebraicGeometry.SubalgebraStages.specCone_π_app AlgebraicGeometry.SubalgebraStages.specLeg_specHom AlgebraicGeometry.SubalgebraStages.specLeg_specTrans AlgebraicGeometry.SubalgebraStages.cone_pt AlgebraicGeometry.SubalgebraStages.trans_fst AlgebraicGeometry.SubalgebraStages.diagram_obj"
p2m_attr_erase "simp" "AlgebraicGeometry.SubalgebraStages.leg_snd AlgebraicGeometry.SubalgebraStages.diagram_map AlgebraicGeometry.SubalgebraStages.specTrans_refl AlgebraicGeometry.SubalgebraStages.trans_snd AlgebraicGeometry.SubalgebraStages.specTrans_specHom AlgebraicGeometry.SubalgebraStages.specCone_pt AlgebraicGeometry.SubalgebraStages.cone_π_app AlgebraicGeometry.SubalgebraStages.specDiagram_map AlgebraicGeometry.SubalgebraStages.specDiagram_obj AlgebraicGeometry.SubalgebraStages.leg_fst AlgebraicGeometry.SubalgebraStages.leg_trans IsDirectLimit.Module.linearEquiv_symm_apply IsDirectLimit.linearEquiv_symm_apply IsDirectLimit.lift_of IsDirectLimit.Module.linearEquiv_apply IsDirectLimit.Module.lift_of IsDirectLimit.Equiv_apply RegularLocalRingQuotientAscent.dualNumberFst_apply GoodReductionJacobian.RelativeGroupLaw.baseChangePointToBase_ofBase GoodReductionJacobian.RelativeGroupLaw.baseChangePointToBase_coe GoodReductionJacobian.RelativeGroupLaw.baseChangePointOfBase_coe GoodReductionJacobian.RelativeGroupLaw.baseChange_inv GoodReductionJacobian.RelativeGroupLaw.baseChangePointOfBase_toBase GoodReductionJacobian.RelativeGroupLaw.baseChange_mul GoodReductionJacobian.RelativeGroupLaw.baseChange_one NeronSpecialFibreInfra.specialFibreRestrict_coe_comp_fst NeronSpecialFibreInfra.fibreRestrictAlong_coe_comp_snd NeronSpecialFibreInfra.fibreRestrictAlong_coe_comp_fst NeronSpecialFibreInfra.neronEndRestrictEquiv_apply NeronSpecialFibreInfra.fibreRestrictAlong_coe_comp_fst_assoc NeronSpecialFibreInfra.specialFibreRestrict_coe_comp_snd NeronSpecialFibreInfra.neronEndExtension_genericFibreRestrict NeronSpecialFibreInfra.specClosedFibreInclusion_eq NeronSpecialFibreInfra.specialFibreRestrict_coe_comp_fst_assoc NeronSpecialFibreInfra.specialFibreRestrict_coe_comp_snd_assoc NeronSpecialFibreInfra.genericFibreRestrict_neronEndExtension NeronSpecialFibreInfra.homOverId_coe NeronSpecialFibreInfra.homOverComp_coe NeronSpecialFibreInfra.fibreRestrictAlong_coe_comp_snd_assoc GoodReductionJacobian.RelativeGroupLaw.fibre_inv"
p2m_attr_erase "simp" "GoodReductionJacobian.RelativeGroupLaw.fibrePointToBase_coe GoodReductionJacobian.RelativeGroupLaw.fibrePointOfBase_toBase GoodReductionJacobian.RelativeGroupLaw.fibre_mul GoodReductionJacobian.RelativeGroupLaw.fibrePointToBase_ofBase GoodReductionJacobian.RelativeGroupLaw.fibre_one GoodReductionJacobian.RelativeGroupLaw.fibrePointOfBase_coe AlgebraicGeometry.schemeFibreEndo_snd AlgebraicGeometry.schemeFibreEndo_fst"

set_option autoImplicit false

noncomputable section

p2m_open "CategoryTheory CategoryTheory.Limits AlgebraicGeometry P2MW.S_AlgebraicGeometry_PolarisedAbelianScheme_exists_units_forall_thetaPt_act_eq_smul_of_pt_eq_one.AlgebraicGeometry NeronModelInfra GoodReductionJacobian TopologicalSpace Opposite AlgebraicGeometry.Polarisation P2MW.S_AlgebraicGeometry_PolarisedAbelianScheme_exists_units_forall_thetaPt_act_eq_smul_of_pt_eq_one.AlgebraicGeometry.Polarisation"

open scoped BigOperators

namespace AlgebraicGeometry
p2m_export "AlgebraicGeometry" "Spec.map_preimage Scheme.Modules.pullback Scheme.Modules.Hom.comp_app Scheme.Modules.Hom Spec Spec.map Scheme Scheme.Modules.Hom.id_app Spec.preimage Scheme.Modules Scheme.ΓSpecIso Polarisation.ThetaPt PolarisedAbelianScheme Scheme.Modules.IsInvertible"
namespace Scheme
p2m_export "AlgebraicGeometry.Scheme" "Modules.pullback Hom.id_app Hom Γ Modules.Hom.comp_app empty Modules.Hom Modules.Hom.id_app Hom.comp_app Modules Opens ΓSpecIso Modules.IsInvertible"
namespace Modules
p2m_export "AlgebraicGeometry.Scheme.Modules" "pushforward pullback Hom.comp_app pushforwardId pushforwardId_inv_app_app Hom pushforward_map_app Hom.id_app pullbackPushforwardAdjunction pullbackId conjugateEquiv_pullbackId_hom topRes topRes_top IsInvertible IsInvertible.pullback pullbackLocalSection pullbackLocalSection_def IsInvertible.exists_forall_app_eq_smul IsInvertible.eq_one_of_forall_smul_eq"
namespace C8a
p2m_open "AlgebraicGeometry.Scheme.Modules AlgebraicGeometry.Scheme AlgebraicGeometry"

theorem comp_app_apply {X : Scheme.{0}} {M N K : X.Modules} (φ : M ⟶ N) (ψ : N ⟶ K) (U : X.Opens)
    (x : Γ(M, U)) : (φ ≫ ψ).app U x = ψ.app U (φ.app U x) := rfl

theorem pullbackId_hom_app_app_pullbackLocalSection {X : Scheme.{0}} (M : X.Modules) (U : X.Opens) (s : Γ(M, U)) :
    ((pullbackId X).hom.app M).app ((𝟙 X) ⁻¹ᵁ U) (pullbackLocalSection (𝟙 X) s) = s := by
  have h := unit_conjugateEquiv (CategoryTheory.Adjunction.id (C := X.Modules)) (pullbackPushforwardAdjunction (𝟙 X))
    (pullbackId X).hom M
  rw [conjugateEquiv_pullbackId_hom] at h
  have h2 : (CategoryTheory.Adjunction.id.unit.app M ≫ (pushforwardId X).inv.app ((𝟭 X.Modules).obj M)).app U s =
      ((pullbackPushforwardAdjunction (𝟙 X)).unit.app M ≫ (pushforward (𝟙 X)).map ((pullbackId X).hom.app M)).app U s := by
    rw [h]
  rw [Scheme.Modules.Hom.comp_app, Scheme.Modules.Hom.comp_app] at h2
  change ((pushforwardId X).inv.app ((𝟭 X.Modules).obj M)).app U ((CategoryTheory.Adjunction.id.unit.app M).app U s) =
    ((pushforward (𝟙 X)).map ((pullbackId X).hom.app M)).app U
      (((pullbackPushforwardAdjunction (𝟙 X)).unit.app M).app U s) at h2
  rw [pushforward_map_app, pushforwardId_inv_app_app, ← pullbackLocalSection_def] at h2
  exact h2.symm

theorem pullbackLocalSection_id_top_eq {X : Scheme.{0}} (M : X.Modules) (s : Γ(M, ⊤)) :
    (pullbackLocalSection (𝟙 X) s : Γ((Scheme.Modules.pullback (𝟙 X)).obj M, ⊤)) =
      ((pullbackId X).inv.app M).app ⊤ s := by
  have hiso : ((pullbackId X).hom.app M).app ⊤ ≫ ((pullbackId X).inv.app M).app ⊤ = 𝟙 _ := by
    rw [← Scheme.Modules.Hom.comp_app, Iso.hom_inv_id_app, Scheme.Modules.Hom.id_app]
  have h2 : ((pullbackId X).inv.app M).app ⊤ (((pullbackId X).hom.app M).app ⊤
      (pullbackLocalSection (𝟙 X) s : Γ((Scheme.Modules.pullback (𝟙 X)).obj M, ⊤))) =
      (pullbackLocalSection (𝟙 X) s : Γ((Scheme.Modules.pullback (𝟙 X)).obj M, ⊤)) :=
    ConcreteCategory.congr_hom hiso _
  have h3 : ((pullbackId X).hom.app M).app ⊤
      (pullbackLocalSection (𝟙 X) s : Γ((Scheme.Modules.pullback (𝟙 X)).obj M, ⊤)) = s :=
    pullbackId_hom_app_app_pullbackLocalSection M ⊤ s
  rw [h3] at h2
  exact h2.symm

def actOf {X : Scheme.{0}} (M : X.Modules) (a : X ⟶ X) (φ : (Scheme.Modules.pullback a).obj M ≅ M) (s : Γ(M, ⊤)) :
    Γ(M, ⊤) :=
  (φ.hom.app (a ⁻¹ᵁ ⊤) (pullbackLocalSection a s) : Γ(M, a ⁻¹ᵁ ⊤))

theorem actOf_eq {X : Scheme.{0}} (M : X.Modules) (a : X ⟶ X) (φ : (Scheme.Modules.pullback a).obj M ≅ M) (s : Γ(M, ⊤)) :
    actOf M a φ s = φ.hom.app ⊤ (pullbackLocalSection a s : Γ((Scheme.Modules.pullback a).obj M, ⊤)) := rfl

theorem exists_units_forall_actOf_eq_smul {X : Scheme.{0}} (M : X.Modules) (hM : Scheme.Modules.IsInvertible M)
    {a : X ⟶ X} (ha : a = 𝟙 X) (φ : (Scheme.Modules.pullback a).obj M ≅ M) :
    ∃ v : Γ(X, ⊤)ˣ, ∀ s : Γ(M, ⊤), actOf M a φ s = (v : Γ(X, ⊤)) • s := by
  subst ha

  let γ : M ≅ M := ((pullbackId X).app M).symm ≪≫ φ
  obtain ⟨w, hw⟩ := hM.exists_forall_app_eq_smul γ.hom
  obtain ⟨w', hw'⟩ := hM.exists_forall_app_eq_smul γ.inv
  have h1 : w' * w = 1 := by
    apply hM.eq_one_of_forall_smul_eq
    intro U s
    rw [map_mul, mul_smul, ← hw U s, ← hw' U (γ.hom.app U s), ← comp_app_apply, Iso.hom_inv_id,
      Scheme.Modules.Hom.id_app]
    rfl
  refine ⟨⟨w, w', by rw [mul_comm]; exact h1, h1⟩, fun s => ?_⟩
  rw [actOf_eq, pullbackLocalSection_id_top_eq]
  have h2 : φ.hom.app ⊤ (((pullbackId X).inv.app M).app ⊤ s) = γ.hom.app ⊤ s := by
    rw [← comp_app_apply]
    rfl
  rw [h2, hw ⊤ s]
  change topRes w ⊤ • s = _
  rw [topRes_top]

end AlgebraicGeometry.Scheme.Modules.C8a

namespace AlgebraicGeometry
p2m_export "AlgebraicGeometry" "Spec.map_preimage Scheme.Modules.pullback Scheme.Modules.Hom.comp_app Scheme.Modules.Hom Spec Spec.map Scheme Scheme.Modules.Hom.id_app Spec.preimage Scheme.Modules Scheme.ΓSpecIso Polarisation.ThetaPt PolarisedAbelianScheme Scheme.Modules.IsInvertible"
namespace PolarisedAbelianScheme
p2m_export "AlgebraicGeometry.PolarisedAbelianScheme" "Iso IsPullback pol_isInvertible bundle L A f pol"
namespace C8a
p2m_open "AlgebraicGeometry.PolarisedAbelianScheme AlgebraicGeometry"

theorem exists_units_baseScalar_eq {g d n : ℕ} {S : Type} [CommRing S] (u : PolarisedAbelianScheme g d n S)
    {R : Type} [CommRing R] (t : Spec (CommRingCat.of R) ⟶ Spec (CommRingCat.of S)) (v : Γ(pullback u.f t, ⊤)ˣ) :
    ∃ c : Rˣ, baseScalar u.f t (c : R) = (v : Γ(pullback u.f t, ⊤)) := by
  have hP : CategoryTheory.IsPullback (pullback.fst u.f t) (pullback.snd u.f t) u.f
      (Spec.map (CommRingCat.ofHom (Spec.preimage t).hom)) := by
    rw [CommRingCat.ofHom_hom, Spec.map_preimage]
    exact CategoryTheory.IsPullback.of_hasPullback u.f t
  have bij := u.bundle.bijective_specIso_inv_comp_appTop_of_isPullback (Spec.preimage t).hom
    (pullback.snd u.f t) (pullback.fst u.f t) hP
  set E := ((Scheme.ΓSpecIso (CommRingCat.of R)).inv ≫ (pullback.snd u.f t).appTop).hom with hE
  have hbase : ∀ r : R, baseScalar u.f t r = E r := fun r => rfl
  obtain ⟨c, hc⟩ := bij.2 (v : Γ(pullback u.f t, ⊤))
  obtain ⟨c', hc'⟩ := bij.2 ((v⁻¹ : Γ(pullback u.f t, ⊤)ˣ) : Γ(pullback u.f t, ⊤))
  have hcc' : c * c' = 1 := bij.1 (by rw [map_mul, map_one, hc, hc', Units.mul_inv])
  have hc'c : c' * c = 1 := by rw [mul_comm]; exact hcc'
  exact ⟨⟨c, c', hcc', hc'c⟩, by rw [hbase]; exact hc⟩

end AlgebraicGeometry.PolarisedAbelianScheme.C8a

namespace AlgebraicGeometry
p2m_export "AlgebraicGeometry" "Spec.map_preimage Scheme.Modules.pullback Scheme.Modules.Hom.comp_app Scheme.Modules.Hom Spec Spec.map Scheme Scheme.Modules.Hom.id_app Spec.preimage Scheme.Modules Scheme.ΓSpecIso Polarisation.ThetaPt PolarisedAbelianScheme Scheme.Modules.IsInvertible"
namespace Polarisation
p2m_export "AlgebraicGeometry.Polarisation" "translate_one translate ThetaPt ThetaPt.act baseScalar"
namespace ThetaPt
p2m_export "AlgebraicGeometry.Polarisation.ThetaPt" "one inv act pt iso"
p2m_open "AlgebraicGeometry.Polarisation.ThetaPt AlgebraicGeometry.Polarisation AlgebraicGeometry"

theorem C8a_act_eq_actOf {S : Type} [CommRing S] {A : Scheme.{0}} {f : A ⟶ Spec (CommRingCat.of S)} {L : RelativeGroupLaw S f}
    {𝓛 : A.Modules} {R : Type} [CommRing R] {t : Spec (CommRingCat.of R) ⟶ Spec (CommRingCat.of S)}
    (θ : ThetaPt f L 𝓛 t) (s : Γ((Scheme.Modules.pullback (pullback.fst f t)).obj 𝓛, ⊤)) :
    θ.act s = Scheme.Modules.C8a.actOf _ (translate f L t θ.pt) θ.iso s := rfl

end AlgebraicGeometry.Polarisation.ThetaPt

theorem solution
    {g d n : ℕ} {S : Type} [CommRing S] (u : PolarisedAbelianScheme g d n S)
    {R : Type} [CommRing R] (t : Spec (CommRingCat.of R) ⟶ Spec (CommRingCat.of S))
    (θ : ThetaPt u.f u.L u.pol t) (hθ : θ.pt = u.L.one t) :
    ∃ c : Rˣ, ∀ s : Γ((Scheme.Modules.pullback (pullback.fst u.f t)).obj u.pol, ⊤),
      θ.act s = baseScalar u.f t (c : R) • s := by
  obtain ⟨x, ψ⟩ := θ
  change x = u.L.one t at hθ
  subst hθ
  have hM : Scheme.Modules.IsInvertible ((Scheme.Modules.pullback (pullback.fst u.f t)).obj u.pol) :=
    u.pol_isInvertible.pullback _
  obtain ⟨v, hv⟩ := Scheme.Modules.C8a.exists_units_forall_actOf_eq_smul _ hM (translate_one u.f u.L t) ψ
  obtain ⟨c, hc⟩ := PolarisedAbelianScheme.C8a.exists_units_baseScalar_eq u t v
  refine ⟨c, fun s => ?_⟩
  rw [ThetaPt.C8a_act_eq_actOf, hc]
  exact hv s

end

end S_AlgebraicGeometry_PolarisedAbelianScheme_exists_units_forall_thetaPt_act_eq_smul_of_pt_eq_one
end P2MW
export P2MW.S_AlgebraicGeometry_PolarisedAbelianScheme_exists_units_forall_thetaPt_act_eq_smul_of_pt_eq_one (solution)
