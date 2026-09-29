-- Prove2me | solution 1 for AlgebraicGeometry.ThetaLevel.exists_idempotents_gam_units_mul_eq_mul_inter_of_forall_mul_schrodMat_eq
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.122355+00:00
-- url     : https://prove2.me/submissions/b454948e-e257-5386-8350-8296576481f3

import Definitions.Def_AlgebraicGeometry_ThetaLevelGroup
import Theorems.Thm_AlgebraicGeometry_ThetaLevel_exists_completeOrthogonalIdempotents_forall_smul_mul_schrodMat_eq_smul_schrodMat_mul
import Theorems.Thm_AlgebraicGeometry_ThetaLevel_exists_gam_forall_smul_mul_schrodMat_eq_of_forall_smul_mul_schrodMat_eq
import Theorems.Thm_AlgebraicGeometry_ThetaLevel_exists_units_smul_eq_smul_map_inter_of_forall_smul_mul_schrodMat_eq
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_ThetaLevel_exists_idempotents_gam_units_mul_eq_mul_inter_of_forall_mul_schrodMat_eq

set_option autoImplicit false

open scoped BigOperators
open AlgebraicGeometry AlgebraicGeometry.ThetaLevel

namespace K78LGALG

theorem mul_sum_mul_eq {S : Type} [CommRing S] {m : ℕ} {ε : Fin m → S} (hε : CompleteOrthogonalIdempotents ε)
    (a : Fin m → S) (p : Fin m) : ε p * ∑ q, ε q * a q = ε p * a p := by
  rw [Finset.mul_sum, Finset.sum_eq_single p (fun q _ hq => by rw [← mul_assoc, hε.ortho (Ne.symm hq), zero_mul])
    (fun h => absurd (Finset.mem_univ p) h), ← mul_assoc, (hε.idem p).eq]

theorem sum_mul_mul_sum_mul_eq_one {S : Type} [CommRing S] {m : ℕ} {ε : Fin m → S} (hε : CompleteOrthogonalIdempotents ε)
    (a b : Fin m → S) (hab : ∀ p, a p * b p = 1) : (∑ p, ε p * a p) * (∑ q, ε q * b q) = 1 := by
  rw [Finset.sum_mul]
  have : ∀ p, ε p * a p * ∑ q, ε q * b q = ε p := fun p => by
    rw [mul_assoc, mul_comm (a p), ← mul_assoc, mul_sum_mul_eq hε b p, mul_assoc, mul_comm (b p), hab, mul_one]
  simp_rw [this]
  exact hε.complete

end K78LGALG

open K78LGALG in
theorem solution
    {g : ℕ} (δ : Fin g → ℕ) [hδ : ∀ i, NeZero (δ i)] (N : ℕ) (hδd : ∏ i, δ i = N + 1)
    (e : Fin (N + 1) ≃ ((i : Fin g) → ZMod (δ i)))
    (B : Type) [CommRing B] (hd : IsUnit ((N + 1 : ℕ) : B))
    (ζ : B) (hζ : ζ ^ (N + 1) = 1) (hζu : ∀ j : ℕ, 0 < j → j < N + 1 → IsUnit (1 - ζ ^ j))
    (ω : B) (hω : ω ^ 2 = ζ)
    (hint : ∀ γ : (Heis.Gam (δ := δ) (d := N + 1)), ∃ U : Matrix (Fin (N + 1)) (Fin (N + 1)) B, IsIntertwiner δ (N + 1) B ω e γ.1 U)
    {S : Type} [CommRing S] (φB : B →+* S)
    (T : Matrix (Fin (N + 1)) (Fin (N + 1)) S) (hT : IsUnit T)
    (hmono : ∀ z : Heis δ (N + 1), ∃ (ε : ((i : Fin g) → ZMod (δ i)) × ((i : Fin g) → ZMod (δ i)) → S) (u : Sˣ),
      CompleteOrthogonalIdempotents ε ∧
        T * schrodMat δ (N + 1) S (φB ω) e z =
          (∑ c, ε c • ((u : S) • schrodMat δ (N + 1) S (φB ω) e ⟨0, c.1, c.2⟩)) * T) :
    ∃ (m : ℕ) (ε : Fin m → S) (γ : Fin m → (Heis.Gam (δ := δ) (d := N + 1))) (c : Sˣ),
      CompleteOrthogonalIdempotents ε ∧
      ∀ k, ε k • T = ε k • ((c : S) • (ThetaLevel.inter δ (N + 1) B ω e ((γ k)⁻¹).1).map φB) := by
  classical
  obtain ⟨m, ε, w, hε, hw⟩ := AlgebraicGeometry.ThetaLevel.exists_completeOrthogonalIdempotents_forall_smul_mul_schrodMat_eq_smul_schrodMat_mul δ N hδd e B hd ζ hζ hζu ω hω φB T hT hmono
  have hγ : ∀ p, ∃ γ : Heis.Gam δ (N + 1), ∀ z,
      ε p • (T * schrodMat δ (N + 1) S (φB ω) e z) = ε p • (schrodMat δ (N + 1) S (φB ω) e (γ.1 z) * T) :=
    fun p => AlgebraicGeometry.ThetaLevel.exists_gam_forall_smul_mul_schrodMat_eq_of_forall_smul_mul_schrodMat_eq δ N hδd e B hd ζ hζ hζu ω hω φB T hT (ε p) (hε.idem p) (w p) (hw p)
  choose γ' hγ' using hγ
  have hc : ∀ p, ∃ c : Sˣ, ε p • T = ε p • ((c : S) • (inter δ (N + 1) B ω e (γ' p).1).map φB) :=
    fun p => AlgebraicGeometry.ThetaLevel.exists_units_smul_eq_smul_map_inter_of_forall_smul_mul_schrodMat_eq δ N hδd e B hd ζ hζ hζu ω hω hint φB T hT (ε p) (hε.idem p) (γ' p) (hγ' p)
  choose cp hcp using hc

  let c : Sˣ := Units.mkOfMulEqOne (∑ p, ε p * (cp p : S)) (∑ q, ε q * ((cp q)⁻¹ : Sˣ))
    (sum_mul_mul_sum_mul_eq_one hε _ _ fun p => Units.mul_inv (cp p))
  have hcval : (c : S) = ∑ p, ε p * (cp p : S) := rfl
  refine ⟨m, ε, fun p => (γ' p)⁻¹, c, hε, fun k => ?_⟩
  dsimp only
  rw [inv_inv, hcp k, smul_smul, smul_smul, hcval, mul_sum_mul_eq hε]

end S_AlgebraicGeometry_ThetaLevel_exists_idempotents_gam_units_mul_eq_mul_inter_of_forall_mul_schrodMat_eq
end P2MW
export P2MW.S_AlgebraicGeometry_ThetaLevel_exists_idempotents_gam_units_mul_eq_mul_inter_of_forall_mul_schrodMat_eq (solution)
