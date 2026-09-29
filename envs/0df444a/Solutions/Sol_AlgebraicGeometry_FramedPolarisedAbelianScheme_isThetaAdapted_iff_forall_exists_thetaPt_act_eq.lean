-- Prove2me | solution 1 for AlgebraicGeometry.FramedPolarisedAbelianScheme.isThetaAdapted_iff_forall_exists_thetaPt_act_eq
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:02.935278+00:00
-- url     : https://prove2.me/submissions/fe4786ea-70fc-554d-99a8-b2f6a6ef54be

import Definitions.Def_AlgebraicGeometry_ThetaAdaptedFrame
import Theorems.Thm_AlgebraicGeometry_FramedPolarisedAbelianScheme_bijective_sum_baseScalar_smul_of_eq_pullbackLocalSection_frame
import Theorems.Thm_isUnit_natCast_succ_of_pow_eq_one_of_forall_isUnit_one_sub_pow
import Theorems.Thm_AlgebraicGeometry_Polarisation_ThetaPt_exists_forall_act_eq_baseScalar_addChar_smul_of_forall_addMonoidHom
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_FramedPolarisedAbelianScheme_isThetaAdapted_iff_forall_exists_thetaPt_act_eq
p2m_attr_erase "instance" "AlgebraicGeometry.Polarisation.ThetaPt.instMul AlgebraicGeometry.Polarisation.ThetaPt.instPowInt AlgebraicGeometry.Polarisation.ThetaPt.instDiv AlgebraicGeometry.Polarisation.ThetaPt.instGroup AlgebraicGeometry.Polarisation.ThetaPt.instInv AlgebraicGeometry.Polarisation.ThetaPt.instOne AlgebraicGeometry.Polarisation.PtGrp.instGroup AlgebraicGeometry.Polarisation.ThetaPt.instPowNat CategoryTheory.Pseudofunctor.CoGrothendieck.isIso_homMk GoodReductionJacobian.RelativeGroupLaw.AlgPoints.instAddCommGroup GoodReductionJacobian.RelativeGroupLaw.AlgPoints.instDistribMulAction GoodReductionJacobian.RelativeGroupLaw.AlgPoints.instInhabited GoodReductionJacobian.RelativeGroupLaw.isIso_endKerStr_schemeHomOverId TateModule.instModule TateModule.instSMul GaloisRepAdic.instAddCommGroup GaloisRepAdic.instFree GaloisRepAdic.instFinite GaloisRepAdic.instModule ResidualGaloisRep.instModule ResidualGaloisRep.instModuleFinite ResidualGaloisRep.instAddCommGroup WeierstrassCurve.Affine.Point.instSMulCommClassAlgEquivZModTorsionBy instDecEqAlgebraicClosureRat WeierstrassCurve.Affine.Point.instDistribMulActionAlgEquiv WeierstrassCurve.Affine.Point.instModuleZModTorsionBy WeierstrassCurve.Affine.Point.instSMulTorsionBy WeierstrassCurve.Affine.Point.instDistribMulActionTorsionBy WeierstrassCurve.Affine.Point.instSMulAlgEquiv WeierstrassCurve.Affine.Point.instFinite"
p2m_attr_erase "simp" "AlgebraicGeometry.Polarisation.ThetaPt.mul_pt AlgebraicGeometry.Polarisation.ThetaPt.ofScalar_pt AlgebraicGeometry.Polarisation.baseScalarHom_apply AlgebraicGeometry.Polarisation.ThetaPt.ofUnit_pt AlgebraicGeometry.Polarisation.translateIso_hom AlgebraicGeometry.Polarisation.ThetaPt.inv_pt AlgebraicGeometry.Polarisation.translateIso_inv AlgebraicGeometry.Polarisation.ThetaPt.one_pt AlgebraicGeometry.Scheme.Modules.fibration.autOfIso_hom_fiber AlgebraicGeometry.Scheme.Modules.fibration.autOfIso_hom_base AlgebraicGeometry.Scheme.Modules.homothety_app AlgebraicGeometry.Polarisation.ThetaPt.ptHom_apply AlgebraicGeometry.Scheme.Modules.fibration_map_toFunctor CategoryTheory.Pseudofunctor.CoGrothendieck.homMk_base CategoryTheory.Pseudofunctor.CoGrothendieck.isoMk_hom AlgebraicGeometry.RiemannForm.thetaGroup.pt_liftOfIso AlgebraicGeometry.RiemannForm.modulePair_fiber AlgebraicGeometry.RiemannForm.pt_levelLift AlgebraicGeometry.RiemannForm.modulePair_base AlgebraicGeometry.RiemannForm.thetaGroup.pt_apply AlgebraicGeometry.RiemannForm.translationIso_hom AlgebraicGeometry.Scheme.Modules.fibration_obj CategoryTheory.Pseudofunctor.CoGrothendieck.homMk_fiber AlgebraicGeometry.RiemannForm.ofUnitPt_toUnitPt AlgebraicGeometry.RiemannForm.toUnitPt_coe AlgebraicGeometry.RiemannForm.toUnitPt_ofUnitPt AlgebraicGeometry.RiemannForm.ofUnitPt_coe GoodReductionJacobian.RelativeGroupLaw.AlgPoints.ofPoint_toPoint GoodReductionJacobian.RelativeGroupLaw.AlgPoints.toPoint_map_coe GoodReductionJacobian.RelativeGroupLaw.AlgPoints.torsionByEquiv_symm_apply_coe GoodReductionJacobian.RelativeGroupLaw.AlgPoints.toPoint_ofPoint GoodReductionJacobian.RelativeGroupLaw.AlgPoints.torsionByEquiv_apply_coe GoodReductionJacobian.RelativeGroupLaw.AlgPoints.equivPoint_symm_apply GoodReductionJacobian.RelativeGroupLaw.AlgPoints.mapPoint_coe GoodReductionJacobian.RelativeGroupLaw.AlgPoints.toPoint_smul_coe GoodReductionJacobian.RelativeGroupLaw.AlgPoints.equivPoint_apply NeronModelInfra.schemeHomOverNpow_succ NeronModelInfra.schemeHomOverNpow_zero NeronModelInfra.NeronModelPropertyBundle.endExtensionEquiv_symm_restrict NeronModelInfra.schemeHomOverComp_id_left"
p2m_attr_erase "simp" "NeronModelInfra.schemeHomOverComp_id_right NeronModelInfra.schemeHomOverId_coe NeronModelInfra.NeronModelPropertyBundle.endExtensionEquiv_apply NeronModelInfra.NeronModelPropertyBundle.restrict_endExtensionEquiv_symm NeronModelInfra.schemeHomOverComp_coe TateModule.smul_apply TateModule.coe_mulP TateModule.proj_apply TateModule.coe_add TateModule.coe_sub WeierstrassCurve.tateModuleRepOfBasis_V TateModule.coe_zero TateModule.rep_apply WeierstrassCurve.tateModuleRep_V WeierstrassCurve.tateModuleRepOfBasis_ρ_apply GaloisRep.padicIntToRingLevel_apply TateModule.coe_neg WeierstrassCurve.tateModuleRep_ρ_apply GaloisRepAdic.mk.injEq GaloisRepAdic.mk.sizeOf_spec GaloisRepAdic.Equiv.mk.sizeOf_spec GaloisRepAdic.Equiv.mk.injEq ResidualGaloisRep.mk.sizeOf_spec ResidualGaloisRep.mk.injEq WeierstrassCurve.Affine.Point.galoisRepModuleEnd_apply FreyPackage.mk.sizeOf_spec FreyPackage.mk.injEq ResidualGaloisRep.Equiv.mk.sizeOf_spec ResidualGaloisRep.Equiv.mk.injEq"

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian AlgebraicGeometry.Polarisation
open scoped BigOperators

theorem solution
    {g N n : ℕ} (δ : Fin g → ℕ) [hδ : ∀ i, NeZero (δ i)] (e : Fin (N + 1) ≃ ((i : Fin g) → ZMod (δ i)))
    {S : Type} [CommRing S] (ζ : S) (hζ : ζ ^ (N + 1) = 1) (hζu : ∀ j : ℕ, 0 < j → j < N + 1 → IsUnit (1 - ζ ^ j))
    (X : FramedPolarisedAbelianScheme g N n S)
    (σ' : ((i : Fin g) → ZMod (δ i)) →
      Γ((Scheme.Modules.pullback (pullback.fst X.f (𝟙 (Spec (CommRingCat.of S))))).obj X.pol, ⊤))
    (hσ' : ∀ i : Fin (N + 1),
      σ' (e i) =
        (Scheme.Modules.pullbackLocalSection (pullback.fst X.f (𝟙 (Spec (CommRingCat.of S)))) (X.frame.σ i) :
          Γ((Scheme.Modules.pullback (pullback.fst X.f (𝟙 (Spec (CommRingCat.of S))))).obj X.pol,
            (pullback.fst X.f (𝟙 (Spec (CommRingCat.of S)))) ⁻¹ᵁ ⊤))) :
    X.IsThetaAdapted δ e ↔
      (∀ h : (i : Fin g) → ZMod (δ i), ∃ θ : ThetaPt X.f X.L X.pol (𝟙 (Spec (CommRingCat.of S))),
        ∀ h' : (i : Fin g) → ZMod (δ i), θ.act (σ' h') = σ' (h + h')) ∧
      (∀ c : ((i : Fin g) → ZMod (δ i)) →+ ZMod (N + 1), ∃ η : ThetaPt X.f X.L X.pol (𝟙 (Spec (CommRingCat.of S))),
        ∀ h : (i : Fin g) → ZMod (δ i), η.act (σ' h) = Polarisation.baseScalar X.f (𝟙 (Spec (CommRingCat.of S))) (ζ ^ (c h).val) • σ' h) := by
  classical
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
  constructor
  · rintro ⟨F, hF⟩
    have hFσ : ∀ hh, F.σ hh = σ' hh := by
      intro hh
      obtain ⟨i, rfl⟩ := e.surjective hh
      rw [hF i, hσ' i]
    refine ⟨fun h => ⟨F.lift h, fun h' => ?_⟩, fun cc => ⟨F.dualLift (χS cc), fun h => ?_⟩⟩
    · rw [← hFσ, ← hFσ, F.lift_act]
    · rw [← hFσ, F.dualLift_act, hχS]
  · rintro ⟨hlift, hdual⟩
    choose θ hθ using hlift
    choose η hη using hdual
    have hall := fun χ : AddChar ((i : Fin g) → ZMod (δ i)) S =>
      AlgebraicGeometry.Polarisation.ThetaPt.exists_forall_act_eq_baseScalar_addChar_smul_of_forall_addMonoidHom
        X.f X.L X.pol (𝟙 _) N ζ hζ hζu δ e σ' η hη χ
    refine ⟨{ σ := σ'
              basis := AlgebraicGeometry.FramedPolarisedAbelianScheme.bijective_sum_baseScalar_smul_of_eq_pullbackLocalSection_frame
                δ e X σ' hσ'
              lift := θ
              dualLift := fun χ => (hall χ).choose
              lift_act := fun h h' => hθ h h'
              dualLift_act := fun χ h => (hall χ).choose_spec h }, fun i => hσ' i⟩

end S_AlgebraicGeometry_FramedPolarisedAbelianScheme_isThetaAdapted_iff_forall_exists_thetaPt_act_eq
end P2MW
export P2MW.S_AlgebraicGeometry_FramedPolarisedAbelianScheme_isThetaAdapted_iff_forall_exists_thetaPt_act_eq (solution)
