-- Prove2me | solution 1 for AddSubgroup.galois_trivial_quotient_of_inertia_absorbing
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:01.734404+00:00
-- url     : https://prove2.me/submissions/199db053-341c-5088-9e2e-b4205f8b0791

import Definitions.Def_FLTPrelim_GaloisRep
import Definitions.Def_FLTPrelim_Ramification
import Theorems.Thm_AlgebraicClosure_subgroup_eq_top_of_inertiaSubgroupIn_le
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AddSubgroup_galois_trivial_quotient_of_inertia_absorbing

open WeierstrassCurve WeierstrassCurve.Affine WeierstrassCurve.Affine.Point ValuationSubring

local notation "Qbar" => AlgebraicClosure ℚ

private def twfAbsorber (W : WeierstrassCurve ℤ) (p m : ℕ)
    (K : AddSubgroup ((W.map (Int.castRingHom ℚ))⁄Qbar).Point) :
    Subgroup (Qbar ≃ₐ[ℚ] Qbar) where
  carrier := {σ : Qbar ≃ₐ[ℚ] Qbar |
    ∀ y : ((W.map (Int.castRingHom ℚ))⁄Qbar).Point, p ^ m • y = 0 → σ • y - y ∈ K}
  one_mem' := fun y _ => by rw [one_smul, sub_self]; exact K.zero_mem
  mul_mem' := by
    intro σ τ hσ hτ y hy
    have htors : p ^ m • (τ • y) = 0 := by
      rw [← natCast_zsmul, ← algEquiv_smul_zsmul, natCast_zsmul, hy, smul_zero]
    have hsplit : (σ * τ) • y - y = (σ • (τ • y) - τ • y) + (τ • y - y) := by
      rw [mul_smul, sub_add_sub_cancel]
    rw [hsplit]
    exact K.add_mem (hσ _ htors) (hτ _ hy)
  inv_mem' := by
    intro σ hσ y hy
    have htors : p ^ m • (σ⁻¹ • y) = 0 := by
      rw [← natCast_zsmul, ← algEquiv_smul_zsmul, natCast_zsmul, hy, smul_zero]
    have h2 := hσ _ htors
    rw [smul_inv_smul] at h2
    have h3 := K.neg_mem h2
    rwa [neg_sub] at h3

theorem solution
    (W : WeierstrassCurve ℤ) (p : ℕ) [Fact p.Prime] (m : ℕ) (hm : 1 ≤ m)
    (K : AddSubgroup ((W.map (Int.castRingHom ℚ))⁄(AlgebraicClosure ℚ)).Point)
    (hopen : IsOpen {σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ |
      ∀ x : Submodule.torsionBy ℤ
        ((W.map (Int.castRingHom ℚ))⁄(AlgebraicClosure ℚ)).Point ((p ^ m : ℕ) : ℤ),
      σ • x = x})
    (hInert : ∀ ℓ : ℕ, ℓ.Prime →
      ∀ A : ValuationSubring (AlgebraicClosure ℚ), A.LiesOverPrime ℓ →
      ∀ τ ∈ A.inertiaSubgroupIn ℚ,
      ∀ y : ((W.map (Int.castRingHom ℚ))⁄(AlgebraicClosure ℚ)).Point,
      p ^ m • y = 0 → τ • y - y ∈ K) :
    ∀ σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ,
      ∀ y : ((W.map (Int.castRingHom ℚ))⁄(AlgebraicClosure ℚ)).Point,
      p ^ m • y = 0 → σ • y - y ∈ K := by
  have _ := hm
  intro σ y hy

  have hsub : {σ : Qbar ≃ₐ[ℚ] Qbar |
      ∀ x : Submodule.torsionBy ℤ
        ((W.map (Int.castRingHom ℚ))⁄Qbar).Point ((p ^ m : ℕ) : ℤ),
      σ • x = x} ⊆ (twfAbsorber W p m K : Set (Qbar ≃ₐ[ℚ] Qbar)) := by
    intro τ hτ z hz
    have hzmem : z ∈ Submodule.torsionBy ℤ
        ((W.map (Int.castRingHom ℚ))⁄Qbar).Point ((p ^ m : ℕ) : ℤ) := by
      rw [Submodule.mem_torsionBy_iff, natCast_zsmul]
      exact hz
    have hfix := hτ ⟨z, hzmem⟩
    have hval : τ • z = z := congrArg Subtype.val hfix
    rw [hval, sub_self]
    exact K.zero_mem

  have hone : (1 : Qbar ≃ₐ[ℚ] Qbar) ∈ {σ : Qbar ≃ₐ[ℚ] Qbar |
      ∀ x : Submodule.torsionBy ℤ
        ((W.map (Int.castRingHom ℚ))⁄Qbar).Point ((p ^ m : ℕ) : ℤ),
      σ • x = x} := fun x => one_smul _ x
  have hopen' : IsOpen ((twfAbsorber W p m K : Subgroup (Qbar ≃ₐ[ℚ] Qbar)) :
      Set (Qbar ≃ₐ[ℚ] Qbar)) :=
    Subgroup.isOpen_of_mem_nhds _ (Filter.mem_of_superset (hopen.mem_nhds hone) hsub)

  have htop : twfAbsorber W p m K = ⊤ :=
    AlgebraicClosure.subgroup_eq_top_of_inertiaSubgroupIn_le _ hopen'
      (fun q hq A hA τ hτ z hz => hInert q hq A hA τ hτ z hz)
  have hσ : σ ∈ twfAbsorber W p m K := htop.ge (Subgroup.mem_top σ)
  exact hσ y hy

end S_AddSubgroup_galois_trivial_quotient_of_inertia_absorbing
end P2MW
export P2MW.S_AddSubgroup_galois_trivial_quotient_of_inertia_absorbing (solution)
