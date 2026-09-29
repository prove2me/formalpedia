-- Prove2me | solution 1 for AlgebraicGeometry.PolarisedAbelianScheme.exists_faithfullyFlat_isThetaAdapted_isPullback_of_thetaTypeLocally
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:02.935278+00:00
-- url     : https://prove2.me/submissions/dfe384d5-2ff1-5b6b-ad59-b6015d48db6b

import Definitions.Def_AlgebraicGeometry_ThetaAdaptedFrame
import Theorems.Thm_AlgebraicGeometry_FramedPolarisedAbelianScheme_reframe_perm
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_PolarisedAbelianScheme_exists_faithfullyFlat_isThetaAdapted_isPullback_of_thetaTypeLocally
p2m_attr_erase "instance" "AlgebraicGeometry.ThetaLevel.Heis.instInv AlgebraicGeometry.ThetaLevel.Heis.Gam.instFinite AlgebraicGeometry.ThetaLevel.Heis.instMul AlgebraicGeometry.ThetaLevel.Heis.Gam.instFintype AlgebraicGeometry.ThetaLevel.Heis.instGroup AlgebraicGeometry.ThetaLevel.Heis.instDecidableEq AlgebraicGeometry.ThetaLevel.Heis.instOne AlgebraicGeometry.ThetaLevel.Heis.instFintype"
p2m_attr_erase "simp" "AlgebraicGeometry.ThetaLevel.Heis.theta_h AlgebraicGeometry.ThetaLevel.Heis.mk.injEq AlgebraicGeometry.ThetaLevel.Heis.one_k AlgebraicGeometry.ThetaLevel.Heis.mk.sizeOf_spec AlgebraicGeometry.ThetaLevel.Heis.mul_a AlgebraicGeometry.ThetaLevel.Heis.eta_a AlgebraicGeometry.ThetaLevel.Heis.mul_h AlgebraicGeometry.ThetaLevel.Heis.inv_k AlgebraicGeometry.ThetaLevel.Heis.mul_k AlgebraicGeometry.ThetaLevel.Heis.one_a AlgebraicGeometry.ThetaLevel.Heis.cen_a AlgebraicGeometry.ThetaLevel.Heis.one_h AlgebraicGeometry.ThetaLevel.Heis.theta_k AlgebraicGeometry.ThetaLevel.Heis.cen_k AlgebraicGeometry.ThetaLevel.Heis.theta_a AlgebraicGeometry.ThetaLevel.Heis.inv_h AlgebraicGeometry.ThetaLevel.diagOp_apply AlgebraicGeometry.ThetaLevel.Heis.cen_h AlgebraicGeometry.ThetaLevel.Heis.eta_h AlgebraicGeometry.ThetaLevel.shiftOp_apply AlgebraicGeometry.ThetaLevel.Heis.inv_a AlgebraicGeometry.ThetaLevel.Heis.eta_k AlgebraicGeometry.Scheme.Modules.tensorPow_zero AlgebraicGeometry.Scheme.Modules.tensorPow_succ AlgebraicGeometry.Scheme.Modules.tensorSections_zero_right AlgebraicGeometry.Scheme.Modules.map_unitSection AlgebraicGeometry.Scheme.Modules.tensorSectionsBilin_apply AlgebraicGeometry.Scheme.Modules.tensorPowSection_zero AlgebraicGeometry.Scheme.Modules.tensorSections_zero_left"

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian AlgebraicGeometry.Polarisation
open scoped BigOperators TensorProduct

theorem solution
    {g N n : ℕ} (δ : Fin g → ℕ) [hδ : ∀ i, NeZero (δ i)] (hδd : ∏ i, δ i = N + 1)
    (e : Fin (N + 1) ≃ ((i : Fin g) → ZMod (δ i)))
    (B : Type) [CommRing B] (ζ : B) (hζ : ζ ^ (N + 1) = 1) (hζu : ∀ j : ℕ, 0 < j → j < N + 1 → IsUnit (1 - ζ ^ j))
    (S : Type) [CommRing S] (s : Spec (CommRingCat.of S) ⟶ Spec (CommRingCat.of B))
    (u : PolarisedAbelianScheme g (N + 1) n S) (hu : PolarisedAbelianScheme.ThetaTypeLocally δ S u) :
    ∃ (S' : Type) (_ : CommRing S') (_ : Algebra S S'), Module.FaithfullyFlat S S' ∧
      ∃ X' : FramedPolarisedAbelianScheme g N n S', X'.IsThetaAdapted δ e ∧
        PolarisedAbelianScheme.IsPullback (algebraMap S S') u X'.toPolarisedAbelianScheme := by

  let sB : B →+* S := (Spec.preimage s).hom
  have hζS : (sB ζ) ^ (N + 1) = 1 := by rw [← map_pow, hζ, map_one]
  have hζSu : ∀ j : ℕ, 0 < j → j < N + 1 → IsUnit (1 - (sB ζ) ^ j) := fun j hj hj' => by
    have h := (hζu j hj hj').map sB
    rwa [map_sub, map_one, map_pow] at h

  dsimp only [PolarisedAbelianScheme.ThetaTypeLocally] at hu
  obtain ⟨R', _, _, hff, -, X'', e', hpb, hadapt⟩ := hu S (sB ζ) hζS hζSu
  rw [Algebra.algebraMap_self, RingHom.comp_id] at hpb

  obtain ⟨F', hF'ci, hF'b, hF'σ⟩ := AlgebraicGeometry.FramedPolarisedAbelianScheme.reframe_perm X'' (e.trans e'.symm)
  obtain ⟨F, hF⟩ := hadapt
  refine ⟨R', inferInstance, inferInstance, hff,
    { toPolarisedAbelianScheme := X''.toPolarisedAbelianScheme, frame := F', frame_isClosedImmersion := hF'ci,
      frame_basis := hF'b }, ⟨F, fun i => ?_⟩, hpb⟩
  show F.σ (e i) = Scheme.Modules.pullbackLocalSection _ (F'.σ i)
  rw [hF'σ i]
  have h := hF ((e.trans e'.symm) i)
  rw [Equiv.trans_apply, Equiv.apply_symm_apply] at h
  exact h

end S_AlgebraicGeometry_PolarisedAbelianScheme_exists_faithfullyFlat_isThetaAdapted_isPullback_of_thetaTypeLocally
end P2MW
export P2MW.S_AlgebraicGeometry_PolarisedAbelianScheme_exists_faithfullyFlat_isThetaAdapted_isPullback_of_thetaTypeLocally (solution)
