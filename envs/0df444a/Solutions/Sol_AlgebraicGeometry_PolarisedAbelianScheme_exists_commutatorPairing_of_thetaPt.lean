-- Prove2me | solution 1 for AlgebraicGeometry.PolarisedAbelianScheme.exists_commutatorPairing_of_thetaPt
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:02.935278+00:00
-- url     : https://prove2.me/submissions/f343a3a4-93aa-5106-9369-261cdf94ec0d

import Definitions.Def_AlgebraicGeometry_ThetaGroupLaw
import Definitions.Def_AlgebraicGeometry_PolarisedAbelianSchemeOfType
import Theorems.Thm_AlgebraicGeometry_PolarisedAbelianScheme_exists_units_forall_thetaPt_act_act_eq_smul_act_act
import Theorems.Thm_AlgebraicGeometry_PolarisedAbelianScheme_exists_units_forall_thetaPt_act_eq_smul_of_pt_eq_one
import Theorems.Thm_AlgebraicGeometry_Polarisation_ThetaPt_mul_act
import Theorems.Thm_AlgebraicGeometry_Polarisation_ThetaPt_one_act
import Theorems.Thm_AlgebraicGeometry_Polarisation_ThetaPt_act_add_and_act_baseScalar_smul
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_ProjPresentation_exists_mem_isFrameOn
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_ProjPresentation_exists_projPresentation_pullback_sigma_eq_toProj_eq
import Theorems.Thm_GoodReductionJacobian_AbelianSchemePropertyBundle_bijective_specIso_inv_comp_appTop_of_isPullback
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_PolarisedAbelianScheme_exists_commutatorPairing_of_thetaPt
p2m_attr_erase "instance" "TwoChartCech.Sections.M0_moduleA TwoChartCech.Sections.M1_module TwoChartCech.Cover.A01_algebra TwoChartCech.Cover.A0_algebra TwoChartCech.Cover.A1_commRing TwoChartCech.Cover.A1_algebra TwoChartCech.Sections.M01_module TwoChartCech.Sections.M0_addCommGroup TwoChartCech.Sections.M0_tower TwoChartCech.Sections.M01_addCommGroup TwoChartCech.Cover.A0_commRing TwoChartCech.Sections.M1_tower TwoChartCech.Sections.M01_moduleA TwoChartCech.Sections.M0_module TwoChartCech.Sections.M1_moduleA TwoChartCech.Sections.M1_addCommGroup TwoChartCech.Cover.A01_commRing TwoChartCech.Sections.M01_tower CoherentBaseChange.TwoTermComplex.C0_module CoherentBaseChange.TwoTermComplex.C0_addCommGroup CoherentBaseChange.TwoTermComplex.C1_module CoherentBaseChange.TwoTermComplex.C1_addCommGroup CoherentBaseChange.TwoTermComplex.C0_free CoherentBaseChange.TwoTermComplex.C1_finite CoherentBaseChange.TwoTermComplex.C0_finite CoherentBaseChange.TwoTermComplex.C1_free AlgebraicGeometry.SubalgebraStages.compactSpace_pullback AlgebraicGeometry.SubalgebraStages.quasiSeparatedSpace_pullback AlgebraicGeometry.SubalgebraStages.compactSpace_obj AlgebraicGeometry.SubalgebraStages.quasiSeparatedSpace_obj AlgebraicGeometry.SubalgebraStages.quasiCompact_snd AlgebraicGeometry.SubalgebraStages.isAffineHom_leg AlgebraicGeometry.SubalgebraStages.isAffineHom_trans AlgebraicGeometry.SubalgebraStages.isAffineHom_diagram_map AlgebraicGeometry.SubalgebraStages.quasiSeparated_snd AlgebraicGeometry.SubalgebraStages.isCofiltered_op IsDirectLimit.Module.instDirectLimitCoeLinearMapIdOfOfNonempty AdicCompletion.instIsLocalRingMaximalIdeal"
p2m_attr_erase "simp" "AlgebraicGeometry.Scheme.Modules.toUnitSection_ofUnitSection AlgebraicGeometry.Scheme.Modules.pullbackSection_def AlgebraicGeometry.Scheme.Modules.ofUnitSection_toUnitSection AlgebraicGeometry.RelEffCartierDiv.toRelEffDivisor_ofRelEffDivisor AlgebraicGeometry.RelEffCartierDiv.toRelEffDivisor_I AlgebraicGeometry.mapOnProdOver_fst_assoc AlgebraicGeometry.RelEffCartierDiv.mk.sizeOf_spec AlgebraicGeometry.RelEffCartierDiv.mk.injEq AlgebraicGeometry.mapOnProdOver_snd AlgebraicGeometry.mapOnProdOver_fst AlgebraicGeometry.mapOnProdOver_snd_assoc AlgebraicGeometry.mapOnProdOver_id AlgebraicCurve.RelEffDivisor.mk.sizeOf_spec AlgebraicCurve.mapOnProd_fst AlgebraicCurve.mapOnProd_fst_assoc AlgebraicCurve.mapOnProd_snd AlgebraicCurve.UnivDivisorPack.mk.injEq AlgebraicCurve.RelEffDivisor.mk.injEq AlgebraicCurve.UnivDivisorPack.mk.sizeOf_spec AlgebraicCurve.mapOnProd_snd_assoc AlgebraicGeometry.Scheme.TwoAffineOpenCover.mk.injEq AlgebraicGeometry.Scheme.TwoAffineOpenCover.mk.sizeOf_spec AlgebraicGeometry.Scheme.TwoAffineOpenCover.pullback_U1 AlgebraicGeometry.Scheme.TwoAffineOpenCover.pullback_U0 TwoChartCech.Sections.mk.injEq TwoChartCech.Cover.mk.injEq TwoChartCech.GrothendieckComplex.mk.injEq TwoChartCech.Sections.mk.sizeOf_spec TwoChartCech.Cover.mk.sizeOf_spec TwoChartCech.Cover.lineBundle_r0_apply TwoChartCech.GrothendieckComplex.mk.sizeOf_spec TwoChartCech.Cover.lineBundle_r1_apply CoherentBaseChange.TwoTermComplex.mk.sizeOf_spec CoherentBaseChange.TwoTermComplex.mk.injEq AlgebraicGeometry.SubalgebraStages.specCone_π_app AlgebraicGeometry.SubalgebraStages.specLeg_specHom AlgebraicGeometry.SubalgebraStages.specLeg_specTrans AlgebraicGeometry.SubalgebraStages.cone_pt AlgebraicGeometry.SubalgebraStages.trans_fst AlgebraicGeometry.SubalgebraStages.diagram_obj"
p2m_attr_erase "simp" "AlgebraicGeometry.SubalgebraStages.leg_snd AlgebraicGeometry.SubalgebraStages.diagram_map AlgebraicGeometry.SubalgebraStages.specTrans_refl AlgebraicGeometry.SubalgebraStages.trans_snd AlgebraicGeometry.SubalgebraStages.specTrans_specHom AlgebraicGeometry.SubalgebraStages.specCone_pt AlgebraicGeometry.SubalgebraStages.cone_π_app AlgebraicGeometry.SubalgebraStages.specDiagram_map AlgebraicGeometry.SubalgebraStages.specDiagram_obj AlgebraicGeometry.SubalgebraStages.leg_fst AlgebraicGeometry.SubalgebraStages.leg_trans IsDirectLimit.Module.linearEquiv_symm_apply IsDirectLimit.linearEquiv_symm_apply IsDirectLimit.lift_of IsDirectLimit.Module.linearEquiv_apply IsDirectLimit.Module.lift_of IsDirectLimit.Equiv_apply RegularLocalRingQuotientAscent.dualNumberFst_apply GoodReductionJacobian.RelativeGroupLaw.baseChangePointToBase_ofBase GoodReductionJacobian.RelativeGroupLaw.baseChangePointToBase_coe GoodReductionJacobian.RelativeGroupLaw.baseChangePointOfBase_coe GoodReductionJacobian.RelativeGroupLaw.baseChange_inv GoodReductionJacobian.RelativeGroupLaw.baseChangePointOfBase_toBase GoodReductionJacobian.RelativeGroupLaw.baseChange_mul GoodReductionJacobian.RelativeGroupLaw.baseChange_one NeronSpecialFibreInfra.specialFibreRestrict_coe_comp_fst NeronSpecialFibreInfra.fibreRestrictAlong_coe_comp_snd NeronSpecialFibreInfra.fibreRestrictAlong_coe_comp_fst NeronSpecialFibreInfra.neronEndRestrictEquiv_apply NeronSpecialFibreInfra.fibreRestrictAlong_coe_comp_fst_assoc NeronSpecialFibreInfra.specialFibreRestrict_coe_comp_snd NeronSpecialFibreInfra.neronEndExtension_genericFibreRestrict NeronSpecialFibreInfra.specClosedFibreInclusion_eq NeronSpecialFibreInfra.specialFibreRestrict_coe_comp_fst_assoc NeronSpecialFibreInfra.specialFibreRestrict_coe_comp_snd_assoc NeronSpecialFibreInfra.genericFibreRestrict_neronEndExtension NeronSpecialFibreInfra.homOverId_coe NeronSpecialFibreInfra.homOverComp_coe NeronSpecialFibreInfra.fibreRestrictAlong_coe_comp_snd_assoc GoodReductionJacobian.RelativeGroupLaw.fibre_inv"
p2m_attr_erase "simp" "GoodReductionJacobian.RelativeGroupLaw.fibrePointToBase_coe GoodReductionJacobian.RelativeGroupLaw.fibrePointOfBase_toBase GoodReductionJacobian.RelativeGroupLaw.fibre_mul GoodReductionJacobian.RelativeGroupLaw.fibrePointToBase_ofBase GoodReductionJacobian.RelativeGroupLaw.fibre_one GoodReductionJacobian.RelativeGroupLaw.fibrePointOfBase_coe AlgebraicGeometry.schemeFibreEndo_snd AlgebraicGeometry.schemeFibreEndo_fst"

set_option autoImplicit false

noncomputable section

p2m_open "CategoryTheory CategoryTheory.Limits AlgebraicGeometry P2MW.S_AlgebraicGeometry_PolarisedAbelianScheme_exists_commutatorPairing_of_thetaPt.AlgebraicGeometry NeronModelInfra GoodReductionJacobian AlgebraicGeometry.Polarisation TopologicalSpace Opposite"

open scoped BigOperators

namespace AlgebraicGeometry
p2m_export "AlgebraicGeometry" "Spec.map_preimage Scheme.Modules.pullback Spec Spec.map Scheme Spec.preimage Scheme.Modules Scheme.Modules.map_smul PolarisedAbelianScheme Scheme.Modules.ProjPresentation PolarisedAbelianScheme.exists_units_forall_thetaPt_act_act_eq_smul_act_act Scheme.Modules.ProjPresentation.exists_projPresentation_pullback_sigma_eq_toProj_eq"
namespace PolarisedAbelianScheme
p2m_export "AlgebraicGeometry.PolarisedAbelianScheme" "IsPullback pol_veryAmple bundle L A f pol exists_units_forall_thetaPt_act_act_eq_smul_act_act exists_units_forall_thetaPt_act_eq_smul_of_pt_eq_one"
namespace L1
p2m_open "AlgebraicGeometry.PolarisedAbelianScheme AlgebraicGeometry"

variable {g d n : ℕ} {S : Type} [CommRing S] (u : PolarisedAbelianScheme g d n S)
  {R : Type} [CommRing R] (t : Spec (CommRingCat.of R) ⟶ Spec (CommRingCat.of S))

theorem eq_zero_of_forall_baseScalar_smul_eq_zero (a : R)
    (h : ∀ s : Γ((Scheme.Modules.pullback (pullback.fst u.f t)).obj u.pol, ⊤), baseScalar u.f t a • s = 0) : a = 0 := by
  obtain ⟨N, 𝔓, -⟩ := u.pol_veryAmple
  obtain ⟨𝔓', -, -⟩ :=
    Scheme.Modules.ProjPresentation.exists_projPresentation_pullback_sigma_eq_toProj_eq (pullback.fst u.f t) 𝔓
  have key : ∀ x : ↥(pullback u.f t), ∃ U : (pullback u.f t).Opens, x ∈ U ∧
      (pullback u.f t).presheaf.map (homOfLE (le_top : U ≤ ⊤)).op (baseScalar u.f t a) = 0 := by
    intro x
    obtain ⟨i, U, hxU, hfr⟩ := 𝔓'.exists_mem_isFrameOn x
    refine ⟨U, hxU, ?_⟩
    apply (hfr.smul_eq_zero_iff le_top le_rfl _).1
    rw [← Scheme.Modules.map_smul, h (𝔓'.σ i), map_zero]
  choose U hxU hU using key
  have hcover : (⊤ : (pullback u.f t).Opens) ≤ ⨆ x, U x := fun x _ => Opens.mem_iSup.2 ⟨x, hxU x⟩
  have hv : baseScalar u.f t a = 0 := by
    have e0 := (pullback u.f t).sheaf.eq_of_locally_eq' U ⊤ (fun x => homOfLE le_top) hcover (baseScalar u.f t a) 0
      (fun x => by rw [map_zero]; exact hU x)
    exact e0
  have hP : CategoryTheory.IsPullback (pullback.fst u.f t) (pullback.snd u.f t) u.f
      (Spec.map (CommRingCat.ofHom (Spec.preimage t).hom)) := by
    rw [CommRingCat.ofHom_hom, Spec.map_preimage]
    exact CategoryTheory.IsPullback.of_hasPullback u.f t
  have bij := u.bundle.bijective_specIso_inv_comp_appTop_of_isPullback (Spec.preimage t).hom
    (pullback.snd u.f t) (pullback.fst u.f t) hP
  apply bij.1
  change baseScalar u.f t a = baseScalar u.f t 0
  rw [hv]
  exact ((baseScalarHom u.f t).map_zero).symm

theorem baseScalar_mul (a b : R) : baseScalar u.f t (a * b) = baseScalar u.f t a * baseScalar u.f t b :=
  (baseScalarHom u.f t).map_mul a b

theorem baseScalar_one : baseScalar u.f t 1 = 1 := (baseScalarHom u.f t).map_one

theorem units_eq_of_forall_smul_eq (c c' : Rˣ)
    (h : ∀ s : Γ((Scheme.Modules.pullback (pullback.fst u.f t)).obj u.pol, ⊤), baseScalar u.f t (c : R) • s = baseScalar u.f t (c' : R) • s) : c = c' := by
  apply Units.ext
  have h0 := eq_zero_of_forall_baseScalar_smul_eq_zero u t ((c : R) - c') (fun s => by
    rw [show baseScalar u.f t ((c : R) - c') = baseScalar u.f t c - baseScalar u.f t c' from
      (baseScalarHom u.f t).map_sub _ _, sub_smul, h s, sub_self])
  exact sub_eq_zero.1 h0

theorem act_smul (θ : ThetaPt u.f u.L u.pol t) (r : R) (s : Γ((Scheme.Modules.pullback (pullback.fst u.f t)).obj u.pol, ⊤)) :
    θ.act (baseScalar u.f t r • s) = baseScalar u.f t r • θ.act s :=
  (ThetaPt.act_add_and_act_baseScalar_smul u.f u.L u.pol t θ).2 r s

theorem act_surjective (θ : ThetaPt u.f u.L u.pol t) (v : Γ((Scheme.Modules.pullback (pullback.fst u.f t)).obj u.pol, ⊤)) : ∃ s : Γ((Scheme.Modules.pullback (pullback.fst u.f t)).obj u.pol, ⊤), θ.act s = v :=
  ⟨θ⁻¹.act v, by rw [← ThetaPt.mul_act, mul_inv_cancel, ThetaPt.one_act]⟩

theorem exists_units_act_eq_act_smul (θ θ' : ThetaPt u.f u.L u.pol t) (hpt : θ.pt = θ'.pt) :
    ∃ c : Rˣ, ∀ s : Γ((Scheme.Modules.pullback (pullback.fst u.f t)).obj u.pol, ⊤), θ'.act s = baseScalar u.f t (c : R) • θ.act s := by
  have hone : (θ⁻¹ * θ').pt = u.L.one t := by
    rw [ThetaPt.mul_pt, ThetaPt.inv_pt, hpt]
    exact u.L.inv_mul_cancel t θ'.pt
  obtain ⟨c, hc⟩ := exists_units_forall_thetaPt_act_eq_smul_of_pt_eq_one u t (θ⁻¹ * θ') hone
  refine ⟨c, fun s => ?_⟩
  rw [← act_smul, ← hc s, ← ThetaPt.mul_act, mul_inv_cancel_left]

theorem units_eq_of_forall_comp (c c' : Rˣ) (θa θb : ThetaPt u.f u.L u.pol t)
    (H : ∀ s : Γ((Scheme.Modules.pullback (pullback.fst u.f t)).obj u.pol, ⊤), baseScalar u.f t (c : R) • θa.act (θb.act s) = baseScalar u.f t (c' : R) • θa.act (θb.act s)) :
    c = c' := by
  apply units_eq_of_forall_smul_eq u t
  intro v
  obtain ⟨s, hs⟩ := act_surjective u t (θa * θb) v
  rw [ThetaPt.mul_act] at hs
  rw [← hs]
  exact H s

section Pairing

variable {K : Type} [AddCommGroup K] [Fintype K]
  (x : K → SchemeHomOver t u.f) (hx : ∀ k k' : K, x (k + k') = u.L.mul t (x k) (x k'))
  (θ₀ : K → ThetaPt u.f u.L u.pol t) (hθ₀ : ∀ k : K, (θ₀ k).pt = x k)
  (e : K → K → Rˣ)
  (he : ∀ (k k' : K) (s : Γ((Scheme.Modules.pullback (pullback.fst u.f t)).obj u.pol, ⊤)),
    (θ₀ k).act ((θ₀ k').act s) = baseScalar u.f t (e k k' : R) • (θ₀ k').act ((θ₀ k).act s))

include hx hθ₀ he

theorem e_self (k : K) : e k k = 1 := by
  symm
  apply units_eq_of_forall_comp u t 1 (e k k) (θ₀ k) (θ₀ k)
  intro s
  rw [Units.val_one, baseScalar_one, one_smul]
  exact he k k s

theorem e_mul_swap (k k' : K) : e k k' * e k' k = 1 := by
  apply units_eq_of_forall_comp u t (e k k' * e k' k) 1 (θ₀ k) (θ₀ k')
  intro s
  rw [Units.val_one, baseScalar_one, one_smul, Units.val_mul, baseScalar_mul, mul_smul, ← he k' k s, ← he k k' s]

theorem e_add_left (k₁ k₂ k' : K) : e (k₁ + k₂) k' = e k₁ k' * e k₂ k' := by
  obtain ⟨c, hc⟩ := exists_units_act_eq_act_smul u t (θ₀ k₁ * θ₀ k₂) (θ₀ (k₁ + k₂))
    (by rw [ThetaPt.mul_pt, hθ₀, hθ₀, hθ₀, hx])

  have h1 : c * (e k₂ k' * e k₁ k') = e (k₁ + k₂) k' * c := by
    apply units_eq_of_forall_comp u t _ _ (θ₀ k') (θ₀ k₁ * θ₀ k₂)
    intro s

    have A : (θ₀ (k₁ + k₂)).act ((θ₀ k').act s) =
        baseScalar u.f t ((c * (e k₂ k' * e k₁ k') : Rˣ) : R) • (θ₀ k').act ((θ₀ k₁ * θ₀ k₂).act s) := by
      rw [hc, ThetaPt.mul_act, ThetaPt.mul_act, he k₂ k' s, act_smul, he k₁ k', smul_smul, smul_smul,
        ← baseScalar_mul, ← baseScalar_mul, Units.val_mul, Units.val_mul, mul_assoc]
    have B : (θ₀ (k₁ + k₂)).act ((θ₀ k').act s) =
        baseScalar u.f t ((e (k₁ + k₂) k' * c : Rˣ) : R) • (θ₀ k').act ((θ₀ k₁ * θ₀ k₂).act s) := by
      rw [he (k₁ + k₂) k' s, hc, act_smul, smul_smul, ← baseScalar_mul, Units.val_mul]
    rw [← A, ← B]

  have h2 : e k₂ k' * e k₁ k' = e (k₁ + k₂) k' := by
    have := h1
    rw [mul_comm (e (k₁ + k₂) k') c] at this
    exact mul_left_cancel this
  rw [← h2, mul_comm]

theorem e_add_right (k k₁ k₂ : K) : e k (k₁ + k₂) = e k k₁ * e k k₂ := by
  obtain ⟨c, hc⟩ := exists_units_act_eq_act_smul u t (θ₀ k₁ * θ₀ k₂) (θ₀ (k₁ + k₂))
    (by rw [ThetaPt.mul_pt, hθ₀, hθ₀, hθ₀, hx])
  have h1 : c * (e k k₁ * e k k₂) = e k (k₁ + k₂) * c := by
    apply units_eq_of_forall_comp u t _ _ (θ₀ k₁ * θ₀ k₂) (θ₀ k)
    intro s
    have A : (θ₀ k).act ((θ₀ (k₁ + k₂)).act s) =
        baseScalar u.f t ((c * (e k k₁ * e k k₂) : Rˣ) : R) • (θ₀ k₁ * θ₀ k₂).act ((θ₀ k).act s) := by
      rw [hc, act_smul, ThetaPt.mul_act, ThetaPt.mul_act, he k k₁, he k k₂ s, act_smul, smul_smul, smul_smul,
        ← baseScalar_mul, ← baseScalar_mul, Units.val_mul, Units.val_mul, mul_assoc]
    have B : (θ₀ k).act ((θ₀ (k₁ + k₂)).act s) =
        baseScalar u.f t ((e k (k₁ + k₂) * c : Rˣ) : R) • (θ₀ k₁ * θ₀ k₂).act ((θ₀ k).act s) := by
      rw [he k (k₁ + k₂) s, hc, smul_smul, ← baseScalar_mul, Units.val_mul]
    rw [← A, ← B]
  have h2 : e k k₁ * e k k₂ = e k (k₁ + k₂) := by
    have := h1
    rw [mul_comm (e k (k₁ + k₂)) c] at this
    exact mul_left_cancel this
  exact h2.symm

theorem e_zero_left (k' : K) : e 0 k' = 1 := by
  have h := e_add_left u t x hx θ₀ hθ₀ e he 0 0 k'
  rw [add_zero] at h
  exact mul_left_cancel (h.symm.trans (mul_one (e 0 k')).symm)

theorem e_nsmul_left (m : ℕ) (k k' : K) : e (m • k) k' = e k k' ^ m := by
  induction m with
  | zero => rw [zero_nsmul, pow_zero]; exact e_zero_left u t x hx θ₀ hθ₀ e he k'
  | succ m ih => rw [succ_nsmul, e_add_left u t x hx θ₀ hθ₀ e he, ih, pow_succ]

theorem e_pow_card (k k' : K) : e k k' ^ Fintype.card K = 1 := by
  rw [← e_nsmul_left u t x hx θ₀ hθ₀ e he, card_nsmul_eq_zero]
  exact e_zero_left u t x hx θ₀ hθ₀ e he k'

omit hx

theorem indep (θ₁ : K → ThetaPt u.f u.L u.pol t) (hθ₁ : ∀ k : K, (θ₁ k).pt = x k) (k k' : K) (s : Γ((Scheme.Modules.pullback (pullback.fst u.f t)).obj u.pol, ⊤)) :
    (θ₁ k).act ((θ₁ k').act s) = baseScalar u.f t (e k k' : R) • (θ₁ k').act ((θ₁ k).act s) := by
  obtain ⟨c, hc⟩ := exists_units_act_eq_act_smul u t (θ₀ k) (θ₁ k) (by rw [hθ₀, hθ₁])
  obtain ⟨c', hc'⟩ := exists_units_act_eq_act_smul u t (θ₀ k') (θ₁ k') (by rw [hθ₀, hθ₁])
  rw [hc', hc, act_smul, he k k' s, hc, hc', act_smul, smul_smul, smul_smul, smul_smul, smul_smul,
    ← baseScalar_mul, ← baseScalar_mul, ← baseScalar_mul, ← baseScalar_mul]
  congr 1
  congr 1
  ring

end Pairing

end AlgebraicGeometry.PolarisedAbelianScheme.L1

open AlgebraicGeometry.PolarisedAbelianScheme.L1 in
theorem solution
    {g d n : ℕ} {S : Type} [CommRing S] (u : PolarisedAbelianScheme g d n S)
    {R : Type} [CommRing R] (t : Spec (CommRingCat.of R) ⟶ Spec (CommRingCat.of S))
    {K : Type} [AddCommGroup K] [Fintype K]
    (x : K → SchemeHomOver t u.f) (hx0 : x 0 = u.L.one t) (hx : ∀ k k' : K, x (k + k') = u.L.mul t (x k) (x k'))
    (θ₀ : K → ThetaPt u.f u.L u.pol t) (hθ₀ : ∀ k : K, (θ₀ k).pt = x k) :
    ∃ e : K → K → Rˣ,
      (∀ (k k' : K) (s : Γ((Scheme.Modules.pullback (pullback.fst u.f t)).obj u.pol, ⊤)),
        (θ₀ k).act ((θ₀ k').act s) = baseScalar u.f t (e k k' : R) • (θ₀ k').act ((θ₀ k).act s)) ∧
      (∀ k₁ k₂ k' : K, e (k₁ + k₂) k' = e k₁ k' * e k₂ k') ∧
      (∀ k k₁ k₂ : K, e k (k₁ + k₂) = e k k₁ * e k k₂) ∧
      (∀ k : K, e k k = 1) ∧ (∀ k k' : K, e k k' * e k' k = 1) ∧
      (∀ k k' : K, e k k' ^ Fintype.card K = 1) ∧
      (∀ (θ₁ : K → ThetaPt u.f u.L u.pol t), (∀ k : K, (θ₁ k).pt = x k) →
        ∀ (k k' : K) (s : Γ((Scheme.Modules.pullback (pullback.fst u.f t)).obj u.pol, ⊤)),
          (θ₁ k).act ((θ₁ k').act s) = baseScalar u.f t (e k k' : R) • (θ₁ k').act ((θ₁ k).act s)) := by
  classical
  choose e he using fun k k' =>
    AlgebraicGeometry.PolarisedAbelianScheme.exists_units_forall_thetaPt_act_act_eq_smul_act_act u t (θ₀ k) (θ₀ k')
  exact ⟨e, he, fun k₁ k₂ k' => e_add_left u t x hx θ₀ hθ₀ e he k₁ k₂ k',
    fun k k₁ k₂ => e_add_right u t x hx θ₀ hθ₀ e he k k₁ k₂,
    fun k => e_self u t x hx θ₀ hθ₀ e he k, fun k k' => e_mul_swap u t x hx θ₀ hθ₀ e he k k',
    fun k k' => e_pow_card u t x hx θ₀ hθ₀ e he k k',
    fun θ₁ hθ₁ k k' s => indep u t x θ₀ hθ₀ e he θ₁ hθ₁ k k' s⟩

end

end S_AlgebraicGeometry_PolarisedAbelianScheme_exists_commutatorPairing_of_thetaPt
end P2MW
export P2MW.S_AlgebraicGeometry_PolarisedAbelianScheme_exists_commutatorPairing_of_thetaPt (solution)
