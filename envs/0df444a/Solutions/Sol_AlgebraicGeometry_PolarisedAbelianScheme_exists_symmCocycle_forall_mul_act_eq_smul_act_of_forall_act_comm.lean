-- Prove2me | solution 1 for AlgebraicGeometry.PolarisedAbelianScheme.exists_symmCocycle_forall_mul_act_eq_smul_act_of_forall_act_comm
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:02.935278+00:00
-- url     : https://prove2.me/submissions/182188a9-53dc-5789-9ab6-977d2673ab05

import Definitions.Def_AlgebraicGeometry_ThetaGroupLaw
import Definitions.Def_AlgebraicGeometry_PolarisedAbelianSchemeOfType
import Theorems.Thm_AlgebraicGeometry_Polarisation_ThetaPt_mul_act
import Theorems.Thm_AlgebraicGeometry_Polarisation_ThetaPt_one_act
import Theorems.Thm_AlgebraicGeometry_Polarisation_ThetaPt_act_add_and_act_baseScalar_smul
import Theorems.Thm_AlgebraicGeometry_PolarisedAbelianScheme_exists_units_forall_thetaPt_act_eq_smul_of_pt_eq_one
import Theorems.Thm_AlgebraicGeometry_PolarisedAbelianScheme_eq_zero_of_forall_baseScalar_smul_eq_zero
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_PolarisedAbelianScheme_exists_symmCocycle_forall_mul_act_eq_smul_act_of_forall_act_comm
p2m_attr_erase "instance" "TwoChartCech.Sections.M0_moduleA TwoChartCech.Sections.M1_module TwoChartCech.Cover.A01_algebra TwoChartCech.Cover.A0_algebra TwoChartCech.Cover.A1_commRing TwoChartCech.Cover.A1_algebra TwoChartCech.Sections.M01_module TwoChartCech.Sections.M0_addCommGroup TwoChartCech.Sections.M0_tower TwoChartCech.Sections.M01_addCommGroup TwoChartCech.Cover.A0_commRing TwoChartCech.Sections.M1_tower TwoChartCech.Sections.M01_moduleA TwoChartCech.Sections.M0_module TwoChartCech.Sections.M1_moduleA TwoChartCech.Sections.M1_addCommGroup TwoChartCech.Cover.A01_commRing TwoChartCech.Sections.M01_tower CoherentBaseChange.TwoTermComplex.C0_module CoherentBaseChange.TwoTermComplex.C0_addCommGroup CoherentBaseChange.TwoTermComplex.C1_module CoherentBaseChange.TwoTermComplex.C1_addCommGroup CoherentBaseChange.TwoTermComplex.C0_free CoherentBaseChange.TwoTermComplex.C1_finite CoherentBaseChange.TwoTermComplex.C0_finite CoherentBaseChange.TwoTermComplex.C1_free AlgebraicGeometry.SubalgebraStages.compactSpace_pullback AlgebraicGeometry.SubalgebraStages.quasiSeparatedSpace_pullback AlgebraicGeometry.SubalgebraStages.compactSpace_obj AlgebraicGeometry.SubalgebraStages.quasiSeparatedSpace_obj AlgebraicGeometry.SubalgebraStages.quasiCompact_snd AlgebraicGeometry.SubalgebraStages.isAffineHom_leg AlgebraicGeometry.SubalgebraStages.isAffineHom_trans AlgebraicGeometry.SubalgebraStages.isAffineHom_diagram_map AlgebraicGeometry.SubalgebraStages.quasiSeparated_snd AlgebraicGeometry.SubalgebraStages.isCofiltered_op IsDirectLimit.Module.instDirectLimitCoeLinearMapIdOfOfNonempty AdicCompletion.instIsLocalRingMaximalIdeal"
p2m_attr_erase "simp" "AlgebraicGeometry.Scheme.Modules.toUnitSection_ofUnitSection AlgebraicGeometry.Scheme.Modules.pullbackSection_def AlgebraicGeometry.Scheme.Modules.ofUnitSection_toUnitSection AlgebraicGeometry.RelEffCartierDiv.toRelEffDivisor_ofRelEffDivisor AlgebraicGeometry.RelEffCartierDiv.toRelEffDivisor_I AlgebraicGeometry.mapOnProdOver_fst_assoc AlgebraicGeometry.RelEffCartierDiv.mk.sizeOf_spec AlgebraicGeometry.RelEffCartierDiv.mk.injEq AlgebraicGeometry.mapOnProdOver_snd AlgebraicGeometry.mapOnProdOver_fst AlgebraicGeometry.mapOnProdOver_snd_assoc AlgebraicGeometry.mapOnProdOver_id AlgebraicCurve.RelEffDivisor.mk.sizeOf_spec AlgebraicCurve.mapOnProd_fst AlgebraicCurve.mapOnProd_fst_assoc AlgebraicCurve.mapOnProd_snd AlgebraicCurve.UnivDivisorPack.mk.injEq AlgebraicCurve.RelEffDivisor.mk.injEq AlgebraicCurve.UnivDivisorPack.mk.sizeOf_spec AlgebraicCurve.mapOnProd_snd_assoc AlgebraicGeometry.Scheme.TwoAffineOpenCover.mk.injEq AlgebraicGeometry.Scheme.TwoAffineOpenCover.mk.sizeOf_spec AlgebraicGeometry.Scheme.TwoAffineOpenCover.pullback_U1 AlgebraicGeometry.Scheme.TwoAffineOpenCover.pullback_U0 TwoChartCech.Sections.mk.injEq TwoChartCech.Cover.mk.injEq TwoChartCech.GrothendieckComplex.mk.injEq TwoChartCech.Sections.mk.sizeOf_spec TwoChartCech.Cover.mk.sizeOf_spec TwoChartCech.Cover.lineBundle_r0_apply TwoChartCech.GrothendieckComplex.mk.sizeOf_spec TwoChartCech.Cover.lineBundle_r1_apply CoherentBaseChange.TwoTermComplex.mk.sizeOf_spec CoherentBaseChange.TwoTermComplex.mk.injEq AlgebraicGeometry.SubalgebraStages.specCone_π_app AlgebraicGeometry.SubalgebraStages.specLeg_specHom AlgebraicGeometry.SubalgebraStages.specLeg_specTrans AlgebraicGeometry.SubalgebraStages.cone_pt AlgebraicGeometry.SubalgebraStages.trans_fst AlgebraicGeometry.SubalgebraStages.diagram_obj"
p2m_attr_erase "simp" "AlgebraicGeometry.SubalgebraStages.leg_snd AlgebraicGeometry.SubalgebraStages.diagram_map AlgebraicGeometry.SubalgebraStages.specTrans_refl AlgebraicGeometry.SubalgebraStages.trans_snd AlgebraicGeometry.SubalgebraStages.specTrans_specHom AlgebraicGeometry.SubalgebraStages.specCone_pt AlgebraicGeometry.SubalgebraStages.cone_π_app AlgebraicGeometry.SubalgebraStages.specDiagram_map AlgebraicGeometry.SubalgebraStages.specDiagram_obj AlgebraicGeometry.SubalgebraStages.leg_fst AlgebraicGeometry.SubalgebraStages.leg_trans IsDirectLimit.Module.linearEquiv_symm_apply IsDirectLimit.linearEquiv_symm_apply IsDirectLimit.lift_of IsDirectLimit.Module.linearEquiv_apply IsDirectLimit.Module.lift_of IsDirectLimit.Equiv_apply RegularLocalRingQuotientAscent.dualNumberFst_apply GoodReductionJacobian.RelativeGroupLaw.baseChangePointToBase_ofBase GoodReductionJacobian.RelativeGroupLaw.baseChangePointToBase_coe GoodReductionJacobian.RelativeGroupLaw.baseChangePointOfBase_coe GoodReductionJacobian.RelativeGroupLaw.baseChange_inv GoodReductionJacobian.RelativeGroupLaw.baseChangePointOfBase_toBase GoodReductionJacobian.RelativeGroupLaw.baseChange_mul GoodReductionJacobian.RelativeGroupLaw.baseChange_one NeronSpecialFibreInfra.specialFibreRestrict_coe_comp_fst NeronSpecialFibreInfra.fibreRestrictAlong_coe_comp_snd NeronSpecialFibreInfra.fibreRestrictAlong_coe_comp_fst NeronSpecialFibreInfra.neronEndRestrictEquiv_apply NeronSpecialFibreInfra.fibreRestrictAlong_coe_comp_fst_assoc NeronSpecialFibreInfra.specialFibreRestrict_coe_comp_snd NeronSpecialFibreInfra.neronEndExtension_genericFibreRestrict NeronSpecialFibreInfra.specClosedFibreInclusion_eq NeronSpecialFibreInfra.specialFibreRestrict_coe_comp_fst_assoc NeronSpecialFibreInfra.specialFibreRestrict_coe_comp_snd_assoc NeronSpecialFibreInfra.genericFibreRestrict_neronEndExtension NeronSpecialFibreInfra.homOverId_coe NeronSpecialFibreInfra.homOverComp_coe NeronSpecialFibreInfra.fibreRestrictAlong_coe_comp_snd_assoc GoodReductionJacobian.RelativeGroupLaw.fibre_inv"
p2m_attr_erase "simp" "GoodReductionJacobian.RelativeGroupLaw.fibrePointToBase_coe GoodReductionJacobian.RelativeGroupLaw.fibrePointOfBase_toBase GoodReductionJacobian.RelativeGroupLaw.fibre_mul GoodReductionJacobian.RelativeGroupLaw.fibrePointToBase_ofBase GoodReductionJacobian.RelativeGroupLaw.fibre_one GoodReductionJacobian.RelativeGroupLaw.fibrePointOfBase_coe AlgebraicGeometry.schemeFibreEndo_snd AlgebraicGeometry.schemeFibreEndo_fst AlgebraicGeometry.Scheme.Modules.tensorPow_zero AlgebraicGeometry.Scheme.Modules.tensorPow_succ AlgebraicGeometry.Scheme.Modules.tensorSections_zero_right AlgebraicGeometry.Scheme.Modules.map_unitSection AlgebraicGeometry.Scheme.Modules.tensorSectionsBilin_apply AlgebraicGeometry.Scheme.Modules.tensorPowSection_zero AlgebraicGeometry.Scheme.Modules.tensorSections_zero_left"

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian AlgebraicGeometry.Polarisation
open scoped BigOperators

theorem solution
    {g d n : ℕ} {S : Type} [CommRing S] (u : PolarisedAbelianScheme g d n S)
    {R : Type} [CommRing R] (t : Spec (CommRingCat.of R) ⟶ Spec (CommRingCat.of S))
    {K₁ : Type} [AddCommGroup K₁] [Fintype K₁]
    (x : K₁ → SchemeHomOver t u.f) (hx0 : x 0 = u.L.one t) (hx : ∀ k k' : K₁, x (k + k') = u.L.mul t (x k) (x k'))
    (θ₀ : K₁ → ThetaPt u.f u.L u.pol t) (hθ₀ : ∀ k : K₁, (θ₀ k).pt = x k)
    (hcomm : ∀ (k k' : K₁) (s : Γ((Scheme.Modules.pullback (pullback.fst u.f t)).obj u.pol, ⊤)), (θ₀ k).act ((θ₀ k').act s) = (θ₀ k').act ((θ₀ k).act s)) :
    ∃ c : K₁ → K₁ → Rˣ,
      (∀ (k k' : K₁) (s : Γ((Scheme.Modules.pullback (pullback.fst u.f t)).obj u.pol, ⊤)), (θ₀ k * θ₀ k').act s = baseScalar u.f t ((c k k' : Rˣ) : R) • (θ₀ (k + k')).act s) ∧
      (∀ k k' : K₁, c k k' = c k' k) ∧
      (∀ a b k : K₁, c a b * c (a + b) k = c b k * c a (b + k)) := by
  classical

  have hpt : ∀ k k' : K₁, ((θ₀ (k + k'))⁻¹ * (θ₀ k * θ₀ k')).pt = u.L.one t := by
    intro k k'
    simp only [ThetaPt.mul_pt, ThetaPt.inv_pt, hθ₀, ← hx]
    exact u.L.inv_mul_cancel t (x (k + k'))
  choose c hc using fun kk : K₁ × K₁ =>
    AlgebraicGeometry.PolarisedAbelianScheme.exists_units_forall_thetaPt_act_eq_smul_of_pt_eq_one u t ((θ₀ (kk.1 + kk.2))⁻¹ * (θ₀ kk.1 * θ₀ kk.2)) (hpt kk.1 kk.2)

  have hlin : ∀ (θ : ThetaPt u.f u.L u.pol t) (r : R) (s : Γ((Scheme.Modules.pullback (pullback.fst u.f t)).obj u.pol, ⊤)), θ.act (baseScalar u.f t r • s) = baseScalar u.f t r • θ.act s :=
    fun θ r s => (AlgebraicGeometry.Polarisation.ThetaPt.act_add_and_act_baseScalar_smul u.f u.L u.pol t θ).2 r s
  have hsurj : ∀ (θ : ThetaPt u.f u.L u.pol t) (s : Γ((Scheme.Modules.pullback (pullback.fst u.f t)).obj u.pol, ⊤)), ∃ s', θ.act s' = s := by
    intro θ s
    refine ⟨θ⁻¹.act s, ?_⟩
    rw [← AlgebraicGeometry.Polarisation.ThetaPt.mul_act, mul_inv_cancel, AlgebraicGeometry.Polarisation.ThetaPt.one_act]
  have hbsub : ∀ a b : R, baseScalar u.f t (a - b) = baseScalar u.f t a - baseScalar u.f t b := fun a b => (baseScalarHom u.f t).map_sub a b
  have hbmul : ∀ a b : R, baseScalar u.f t a * baseScalar u.f t b = baseScalar u.f t (a * b) := fun a b => ((baseScalarHom u.f t).map_mul a b).symm

  have hrel : ∀ (k k' : K₁) (s : Γ((Scheme.Modules.pullback (pullback.fst u.f t)).obj u.pol, ⊤)), (θ₀ k * θ₀ k').act s = baseScalar u.f t ((c (k, k') : Rˣ) : R) • (θ₀ (k + k')).act s := by
    intro k k' s
    have h1 : θ₀ k * θ₀ k' = θ₀ (k + k') * ((θ₀ (k + k'))⁻¹ * (θ₀ k * θ₀ k')) := by group
    rw [h1, AlgebraicGeometry.Polarisation.ThetaPt.mul_act, hc (k, k'), hlin]

  have hdescale : ∀ (θ : ThetaPt u.f u.L u.pol t) (a b : R),
      (∀ s : Γ((Scheme.Modules.pullback (pullback.fst u.f t)).obj u.pol, ⊤), baseScalar u.f t a • θ.act s = baseScalar u.f t b • θ.act s) → a = b := by
    intro θ a b h
    have h0 : ∀ s' : Γ((Scheme.Modules.pullback (pullback.fst u.f t)).obj u.pol, ⊤), baseScalar u.f t (a - b) • s' = 0 := by
      intro s'
      obtain ⟨s, rfl⟩ := hsurj θ s'
      rw [hbsub, sub_smul, sub_eq_zero]
      exact h s
    exact sub_eq_zero.mp (AlgebraicGeometry.PolarisedAbelianScheme.eq_zero_of_forall_baseScalar_smul_eq_zero u t (a - b) h0)
  refine ⟨fun k k' => c (k, k'), hrel, ?_, ?_⟩
  ·
    intro k k'
    apply Units.ext
    apply hdescale (θ₀ (k + k'))
    intro s
    have hkk : (θ₀ k * θ₀ k').act s = (θ₀ k' * θ₀ k).act s := by
      rw [AlgebraicGeometry.Polarisation.ThetaPt.mul_act, AlgebraicGeometry.Polarisation.ThetaPt.mul_act, hcomm]
    have := hrel k' k s
    rw [add_comm k' k] at this
    rw [← hrel k k' s, hkk, this]
  ·
    intro a b k
    apply Units.ext
    simp only [Units.val_mul]
    apply hdescale (θ₀ (a + b + k))
    intro s
    have hL : (θ₀ a * θ₀ b * θ₀ k).act s = baseScalar u.f t ((c (a, b) : R) * (c (a + b, k) : R)) • (θ₀ (a + b + k)).act s := by
      rw [AlgebraicGeometry.Polarisation.ThetaPt.mul_act (θ₀ a * θ₀ b) (θ₀ k) s, hrel a b, ← AlgebraicGeometry.Polarisation.ThetaPt.mul_act (θ₀ (a + b)) (θ₀ k) s, hrel (a + b) k s, smul_smul, hbmul]
    have hR : (θ₀ a * (θ₀ b * θ₀ k)).act s = baseScalar u.f t ((c (b, k) : R) * (c (a, b + k) : R)) • (θ₀ (a + b + k)).act s := by
      rw [AlgebraicGeometry.Polarisation.ThetaPt.mul_act (θ₀ a) (θ₀ b * θ₀ k) s, hrel b k s, hlin, ← AlgebraicGeometry.Polarisation.ThetaPt.mul_act (θ₀ a) (θ₀ (b + k)) s, hrel a (b + k) s, smul_smul, hbmul, ← add_assoc]
    rw [← hL, ← hR, mul_assoc]

end S_AlgebraicGeometry_PolarisedAbelianScheme_exists_symmCocycle_forall_mul_act_eq_smul_act_of_forall_act_comm
end P2MW
export P2MW.S_AlgebraicGeometry_PolarisedAbelianScheme_exists_symmCocycle_forall_mul_act_eq_smul_act_of_forall_act_comm (solution)
