-- Prove2me | solution 1 for AlgebraicGeometry.ThetaLevel.exists_units_smul_eq_smul_map_inter_of_forall_smul_mul_schrodMat_eq
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.122355+00:00
-- url     : https://prove2.me/submissions/2fef66da-e190-5325-bac5-2f4e181ec5f1

import Definitions.Def_AlgebraicGeometry_ThetaLevelGroup
import Theorems.Thm_AlgebraicGeometry_ThetaLevel_schrodMat_one_and_schrodMat_mul
import Theorems.Thm_AlgebraicGeometry_ThetaLevel_exists_eq_smul_one_of_forall_mul_schrodMat_eq_schrodMat_mul
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_ThetaLevel_exists_units_smul_eq_smul_map_inter_of_forall_smul_mul_schrodMat_eq

set_option autoImplicit false

noncomputable section

open scoped BigOperators
open AlgebraicGeometry AlgebraicGeometry.ThetaLevel

namespace K77TH3
namespace LGS

variable {g : ℕ} (δ : Fin g → ℕ) [∀ i, NeZero (δ i)] (d : ℕ) [NeZero d] {S : Type} [CommRing S] (ω : S)
  {n : ℕ} (e : Fin n ≃ HH δ)

omit [∀ i, NeZero (δ i)] [NeZero d] in
theorem map_omegaPow {B : Type} [CommRing B] (φ : B →+* S) (ωB : B) (a : ZMod (2 * d)) :
    φ (omegaPow d B ωB a) = omegaPow d S (φ ωB) a := by
  simp [omegaPow, map_pow]

omit [∀ i, NeZero (δ i)] [NeZero d] in
theorem schrodMat_map {B : Type} [CommRing B] (φ : B →+* S) (ωB : B) (z : Heis δ d) :
    (schrodMat δ d B ωB e z).map φ = schrodMat δ d S (φ ωB) e z := by
  ext i j
  rw [Matrix.map_apply, schrodMat_apply, schrodMat_apply]
  split_ifs <;> simp [map_omegaPow]

theorem exists_unit (hδd : ∏ i, δ i = d) (ζ : S) (hζ : ζ ^ d = 1) (hζu : ∀ j : ℕ, 0 < j → j < d → IsUnit (1 - ζ ^ j))
    (hω : ω ^ 2 = ζ) (T : Matrix (Fin n) (Fin n) S) (hT : IsUnit T) (ε : S) (hε : IsIdempotentElem ε)
    (γ : MulAut (Heis δ d)) (U : Matrix (Fin n) (Fin n) S) (hU : IsUnit U)
    (hUint : ∀ z, U * schrodMat δ d S ω e z = schrodMat δ d S ω e (γ z) * U)
    (hγ : ∀ z, ε • (T * schrodMat δ d S ω e z) = ε • (schrodMat δ d S ω e (γ z) * T)) :
    ∃ c : Sˣ, ε • T = ε • ((c : S) • U) := by
  classical

  set Ui : Matrix (Fin n) (Fin n) S := ↑(hU.unit⁻¹) with hUi
  have hUUi : U * Ui = 1 := by rw [hUi]; exact hU.mul_val_inv
  have hUiU : Ui * U = 1 := by rw [hUi]; exact hU.val_inv_mul
  set Ti : Matrix (Fin n) (Fin n) S := ↑(hT.unit⁻¹) with hTi
  have hTTi : T * Ti = 1 := by rw [hTi]; exact hT.mul_val_inv
  have hTiT : Ti * T = 1 := by rw [hTi]; exact hT.val_inv_mul

  have hUi_int : ∀ z, schrodMat δ d S ω e z * Ui = Ui * schrodMat δ d S ω e (γ z) := by
    intro z
    have h := congrArg (fun M => Ui * M * Ui) (hUint z)
    rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, hUiU, Matrix.one_mul, Matrix.mul_assoc, Matrix.mul_assoc, hUUi,
      Matrix.mul_one] at h
    exact h

  have hD : ∀ z, (ε • (Ui * T)) * schrodMat δ d S ω e z = schrodMat δ d S ω e z * (ε • (Ui * T)) := by
    intro z
    rw [Matrix.smul_mul, Matrix.mul_smul, Matrix.mul_assoc, ← Matrix.mul_smul, hγ z, Matrix.mul_smul,
      ← Matrix.mul_assoc, ← hUi_int, Matrix.mul_assoc]
  have hD' : ∀ z, (ε • (Ti * U)) * schrodMat δ d S ω e z = schrodMat δ d S ω e z * (ε • (Ti * U)) := by
    intro z

    have h := hD z

    have h2 := congrArg (fun M => (Ti * U) * M * (Ti * U)) h
    simp only [Matrix.smul_mul, Matrix.mul_smul] at h2
    rw [show Ti * U * (Ui * T * schrodMat δ d S ω e z) * (Ti * U) = schrodMat δ d S ω e z * (Ti * U) by
        rw [← Matrix.mul_assoc (Ti * U), Matrix.mul_assoc Ti U, ← Matrix.mul_assoc U, hUUi, Matrix.one_mul, hTiT,
          Matrix.one_mul],
      show Ti * U * (schrodMat δ d S ω e z * (Ui * T)) * (Ti * U) = Ti * U * schrodMat δ d S ω e z by
        rw [Matrix.mul_assoc (Ti * U), Matrix.mul_assoc (schrodMat δ d S ω e z), Matrix.mul_assoc Ui,
          ← Matrix.mul_assoc T, hTTi, Matrix.one_mul, hUiU, Matrix.mul_one]] at h2
    rw [Matrix.smul_mul, Matrix.mul_smul]
    exact h2.symm

  obtain ⟨c₀, hc₀⟩ := exists_eq_smul_one_of_forall_mul_schrodMat_eq_schrodMat_mul δ d hδd S ζ ω hζ hζu hω e _ hD
  obtain ⟨c₁, hc₁⟩ := exists_eq_smul_one_of_forall_mul_schrodMat_eq_schrodMat_mul δ d hδd S ζ ω hζ hζu hω e _ hD'

  have hprod : (ε • (Ui * T)) * (ε • (Ti * U)) = ε • (1 : Matrix (Fin n) (Fin n) S) := by
    rw [Matrix.smul_mul, Matrix.mul_smul, smul_smul, hε.eq, Matrix.mul_assoc, ← Matrix.mul_assoc T, hTTi,
      Matrix.one_mul, hUiU]
  rw [hc₀, hc₁, smul_mul_smul_comm, Matrix.one_mul] at hprod
  have hεc₀ : ε • (ε • (Ui * T)) = ε • (Ui * T) := by rw [smul_smul, hε.eq]
  rw [hc₀, smul_smul] at hεc₀
  rcases isEmpty_or_nonempty (Fin n) with hn | ⟨⟨i₀⟩⟩
  · exact ⟨1, Matrix.ext fun i _ => (IsEmpty.false i).elim⟩
  have e1 : c₀ * c₁ = ε := by
    have := congrFun (congrFun hprod i₀) i₀
    simpa using this
  have e2 : ε * c₀ = c₀ := by
    have := congrFun (congrFun hεc₀ i₀) i₀
    simpa using this

  refine ⟨⟨ε * c₀ + (1 - ε), ε * c₁ + (1 - ε), ?_, ?_⟩, ?_⟩
  · have : (ε * c₀ + (1 - ε)) * (ε * c₁ + (1 - ε)) = ε * ε * (c₀ * c₁) + (1 - ε) * (1 - ε) + ε * (1 - ε) * (c₀ + c₁) := by
      ring
    rw [this, e1, hε.eq, show (1 - ε) * (1 - ε) = 1 - ε by rw [mul_sub, mul_one, sub_mul, one_mul, hε.eq, sub_self, sub_zero],
      show ε * (1 - ε) = 0 by rw [mul_sub, mul_one, hε.eq, sub_self], zero_mul, add_zero, hε.eq, add_sub_cancel]
  · have : (ε * c₁ + (1 - ε)) * (ε * c₀ + (1 - ε)) = ε * ε * (c₀ * c₁) + (1 - ε) * (1 - ε) + ε * (1 - ε) * (c₀ + c₁) := by
      ring
    rw [this, e1, hε.eq, show (1 - ε) * (1 - ε) = 1 - ε by rw [mul_sub, mul_one, sub_mul, one_mul, hε.eq, sub_self, sub_zero],
      show ε * (1 - ε) = 0 by rw [mul_sub, mul_one, hε.eq, sub_self], zero_mul, add_zero, hε.eq, add_sub_cancel]
  ·
    change ε • T = ε • ((ε * c₀ + (1 - ε)) • U)
    have hT' : ε • T = U * (ε • (Ui * T)) := by
      rw [Matrix.mul_smul, ← Matrix.mul_assoc, hUUi, Matrix.one_mul]
    rw [hT', hc₀, Matrix.mul_smul, Matrix.mul_one, smul_smul]
    congr 1
    rw [mul_add, ← mul_assoc, hε.eq, e2, mul_sub, mul_one, hε.eq, sub_self, add_zero]

end K77TH3.LGS

open K77TH3.LGS in
theorem solution
    {g : ℕ} (δ : Fin g → ℕ) [hδ : ∀ i, NeZero (δ i)] (N : ℕ) (hδd : ∏ i, δ i = N + 1)
    (e : Fin (N + 1) ≃ ((i : Fin g) → ZMod (δ i)))
    (B : Type) [CommRing B] (hd : IsUnit ((N + 1 : ℕ) : B))
    (ζ : B) (hζ : ζ ^ (N + 1) = 1) (hζu : ∀ j : ℕ, 0 < j → j < N + 1 → IsUnit (1 - ζ ^ j))
    (ω : B) (hω : ω ^ 2 = ζ)
    (hint : ∀ γ : (Heis.Gam (δ := δ) (d := N + 1)), ∃ U : Matrix (Fin (N + 1)) (Fin (N + 1)) B, IsIntertwiner δ (N + 1) B ω e γ.1 U)
    {S : Type} [CommRing S] (φB : B →+* S)
    (T : Matrix (Fin (N + 1)) (Fin (N + 1)) S) (hT : IsUnit T)
    (ε : S) (hε : IsIdempotentElem ε)
    (γ : (Heis.Gam (δ := δ) (d := N + 1)))
    (hγ : ∀ z : Heis δ (N + 1), ε • (T * schrodMat δ (N + 1) S (φB ω) e z) =
      ε • (schrodMat δ (N + 1) S (φB ω) e (γ.1 z) * T)) :
    ∃ c : Sˣ, ε • T = ε • ((c : S) • (ThetaLevel.inter δ (N + 1) B ω e γ.1).map φB) := by
  obtain ⟨hUu, hUint⟩ := isIntertwiner_inter δ (N + 1) B ω e γ.1 (hint γ)
  have hζS : φB ζ ^ (N + 1) = 1 := by rw [← map_pow, hζ, map_one]
  have hωS : φB ω ^ 2 = φB ζ := by rw [← map_pow, hω]
  have hζuS : ∀ j : ℕ, 0 < j → j < N + 1 → IsUnit (1 - φB ζ ^ j) := fun j hj hj' => by
    have := (hζu j hj hj').map φB
    rwa [map_sub, map_one, map_pow] at this
  have hU : IsUnit ((inter δ (N + 1) B ω e γ.1).map φB) :=
    hUu.map (RingHom.mapMatrix φB : Matrix (Fin (N + 1)) (Fin (N + 1)) B →+* Matrix (Fin (N + 1)) (Fin (N + 1)) S)
  have hUintS : ∀ z, (inter δ (N + 1) B ω e γ.1).map φB * schrodMat δ (N + 1) S (φB ω) e z =
      schrodMat δ (N + 1) S (φB ω) e (γ.1 z) * (inter δ (N + 1) B ω e γ.1).map φB := by
    intro z
    have := congrArg (fun M : Matrix (Fin (N + 1)) (Fin (N + 1)) B => M.map φB) (hUint z)
    simpa only [Matrix.map_mul, schrodMat_map] using this
  exact exists_unit δ (N + 1) (φB ω) e hδd (φB ζ) hζS hζuS hωS T hT ε hε γ.1 _ hU hUintS hγ

end

end S_AlgebraicGeometry_ThetaLevel_exists_units_smul_eq_smul_map_inter_of_forall_smul_mul_schrodMat_eq
end P2MW
export P2MW.S_AlgebraicGeometry_ThetaLevel_exists_units_smul_eq_smul_map_inter_of_forall_smul_mul_schrodMat_eq (solution)
