-- Prove2me | Definitions.Def_GroundTheory_ProfiniteCohomology_KummerFinite
-- name    : GroundTheory_ProfiniteCohomology_KummerFinite
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T08:11:21.907533+00:00
-- url     : https://prove2.me/theorems/8d96b360-45bc-4bb6-a404-68a016560593
-- title:
--   Kummer Finite
-- statement:
--   Definitions and structural lemmas for Kummer Finite, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ProfiniteCohomology/KummerFinite.lean

import Mathlib
import Definitions.Def_GroundTheory_ProfiniteCohomology_KummerBasic
import Theorems.Thm_GroundTheory_ProfCoh_kummerPairingLeft_apply
import Theorems.Thm_GroundTheory_ProfCoh_kummerPairingRight_apply
import Theorems.Thm_GroundTheory_ProfCoh_mk_mem_kummerGroup
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GroundTheory.ProfCoh.kummerPairingLeft_apply
attribute [local simp] GroundTheory.ProfCoh.kummerPairingRight_apply


set_option autoImplicit false
namespace GroundTheory.ProfCoh
open Polynomial
section Characters
variable {K : Type*} [Field K] {n : ℕ} [NeZero n] [HasEnoughRootsOfUnity K n]
def monoidHomRootsOfUnityEquiv (G : Type*) [Group G] (hG : ∀ g : G, g ^ n = 1) :
    (G →* rootsOfUnity n K) ≃ (G →* Kˣ) where
  toFun φ := (rootsOfUnity n K).subtype.comp φ
  invFun ψ := ψ.codRestrict (rootsOfUnity n K) fun g => by
    rw [mem_rootsOfUnity, ← map_pow, hG g, map_one]
  left_inv φ := by ext; rfl
  right_inv ψ := by ext; rfl
lemma card_monoidHom_rootsOfUnity (G : Type*) [CommGroup G] [Finite G]
    (hG : ∀ g : G, g ^ n = 1) : Nat.card (G →* rootsOfUnity n K) = Nat.card G := by
  have : HasEnoughRootsOfUnity K (Monoid.exponent G) :=
    HasEnoughRootsOfUnity.of_dvd K (Monoid.exponent_dvd_of_forall_pow_eq_one hG)
  rw [Nat.card_congr (monoidHomRootsOfUnityEquiv G hG),
    CommGroup.card_monoidHom_of_hasEnoughRootsOfUnity]
lemma finite_monoidHom_rootsOfUnity (G : Type*) [Group G] [Finite G] :
    Finite (G →* rootsOfUnity n K) :=
  .of_injective _ DFunLike.coe_injective
end Characters
section Finite
variable (K : Type*) [Field K] (n : ℕ) [NeZero n] [HasEnoughRootsOfUnity K n]
variable (L : Type*) [Field L] [Algebra K L]
omit [NeZero n] [HasEnoughRootsOfUnity K n] in

lemma kummerGroup_pow_eq_one (x : kummerGroup K n L) : x ^ n = 1 :=
  Subtype.ext (UnitsModPow.pow_eq_one K n x.1)
variable {K n L}
omit [NeZero n] [HasEnoughRootsOfUnity K n] in

lemma exists_eigenvector_of_character [FiniteDimensional K L] (χ : Gal(L/K) →* Kˣ) :
    ∃ β : Lˣ, ∀ σ : Gal(L/K), σ (β : L) = algebraMap K L (χ σ : K) * β := by
  let f : Gal(L/K) → Lˣ := fun σ => Units.map (algebraMap K L : K →* L) (χ σ)
  have hf : groupCohomology.IsMulCocycle₁ f := by
    intro g h
    ext
    simp only [f, map_mul, Units.val_mul, Units.coe_map, MonoidHom.coe_coe, AlgEquiv.smul_units_def,
      AlgEquiv.commutes]
    ring
  obtain ⟨β, hβ⟩ := groupCohomology.isMulCoboundary₁_of_isMulCocycle₁_of_aut_to_units f hf
  refine ⟨β, fun σ => ?_⟩
  have := congrArg Units.val (hβ σ)
  simp only [AlgEquiv.smul_units_def, Units.val_div_eq_div_val, Units.coe_map, MonoidHom.coe_coe,
    f] at this
  rw [← this, div_mul_cancel₀ _ β.ne_zero]
omit [NeZero n] [HasEnoughRootsOfUnity K n] in

lemma exists_kummer_eigenvector [FiniteDimensional K L] [IsGalois K L]
    (hexp : Monoid.exponent Gal(L/K) ∣ n) (χ : Gal(L/K) →* Kˣ) :
    ∃ a : Kˣ, ∃ β : L, β ^ n = algebraMap K L a ∧
      ∀ σ : Gal(L/K), σ β = algebraMap K L (χ σ : K) * β := by
  obtain ⟨β, hβ⟩ := exists_eigenvector_of_character χ
  have hfix : ∀ σ : Gal(L/K), σ ((β : L) ^ n) = (β : L) ^ n := by
    intro σ
    rw [map_pow, hβ σ, mul_pow, ← map_pow, ← Units.val_pow_eq_pow_val, ← map_pow,
      Monoid.exponent_dvd_iff_forall_pow_eq_one.mp hexp σ, map_one, Units.val_one, map_one, one_mul]
  obtain ⟨b, hb⟩ := (IsGalois.mem_range_algebraMap_iff_fixed (F := K) _).mpr hfix
  have hb0 : b ≠ 0 := by
    rintro rfl
    rw [map_zero] at hb
    exact pow_ne_zero n β.ne_zero hb.symm
  exact ⟨Units.mk0 b hb0, β, hb.symm, hβ⟩
variable (K n L)
theorem kummerPairingRight_injective [FiniteDimensional K L] [IsGalois K L] :
    Function.Injective (kummerPairingRight K n L) := by
  rw [injective_iff_map_eq_one]
  intro x hx
  obtain ⟨a, ha, α, hα⟩ := exists_rep x
  have hfix : ∀ σ : Gal(L/K), σ α = α := fun σ =>
    (kummerPairing_eq_one_iff σ x ha hα).mp (DFunLike.congr_fun hx σ)
  obtain ⟨b, rfl⟩ := (IsGalois.mem_range_algebraMap_iff_fixed (F := K) α).mpr hfix
  have hb0 : b ≠ 0 := by
    rintro rfl
    rw [map_zero, zero_pow (NeZero.ne n)] at hα
    exact (map_ne_zero (algebraMap K L)).mpr a.ne_zero hα.symm
  have hba : (Units.mk0 b hb0) ^ n = a := by
    ext
    simpa using (algebraMap K L).injective (by simpa using hα)
  apply Subtype.ext
  rw [← ha, OneMemClass.coe_one, QuotientGroup.eq_one_iff]
  exact mem_unitsPow.mpr ⟨_, hba⟩
theorem kummerPairingLeft_injective [FiniteDimensional K L] [IsGalois K L]
    [IsMulCommutative Gal(L/K)] (hexp : Monoid.exponent Gal(L/K) ∣ n) :
    Function.Injective (kummerPairingLeft K n L) := by
  let _ : CommGroup Gal(L/K) :=
    { (inferInstance : Group Gal(L/K)) with
      mul_comm := fun a b => (IsMulCommutative.is_comm (M := Gal(L/K))).comm a b }
  have : HasEnoughRootsOfUnity K (Monoid.exponent Gal(L/K)) := HasEnoughRootsOfUnity.of_dvd K hexp
  rw [injective_iff_map_eq_one]
  intro σ hσ
  by_contra hne
  obtain ⟨χ, hχ⟩ := CommGroup.exists_apply_ne_one_of_hasEnoughRootsOfUnity Gal(L/K) K hne
  obtain ⟨a, β, hβ, hχβ⟩ := exists_kummer_eigenvector hexp χ
  have hx : (a : UnitsModPow K n) ∈ kummerGroup K n L := mk_mem_kummerGroup.mpr ⟨β, hβ⟩
  have h1 : σ β = β :=
    (kummerPairing_eq_one_iff σ ⟨_, hx⟩ rfl hβ).mp (DFunLike.congr_fun hσ ⟨_, hx⟩)
  rw [hχβ σ] at h1
  have h2 : algebraMap K L (χ σ : K) = 1 :=
    mul_right_cancel₀ (ne_zero_of_pow_eq_algebraMap hβ) (h1.trans (one_mul β).symm)
  apply hχ
  ext
  simpa using (algebraMap K L).injective (h2.trans (map_one _).symm)
theorem kummerGroup_finite [FiniteDimensional K L] [IsGalois K L] :
    Finite (kummerGroup K n L) :=
  have := finite_monoidHom_rootsOfUnity (K := K) (n := n) Gal(L/K)
  Finite.of_injective _ (kummerPairingRight_injective K n L)
theorem card_kummerGroup [FiniteDimensional K L] [IsGalois K L]
    [IsMulCommutative Gal(L/K)] (hexp : Monoid.exponent Gal(L/K) ∣ n) :
    Nat.card (kummerGroup K n L) = Module.finrank K L := by
  let _ : CommGroup Gal(L/K) :=
    { (inferInstance : Group Gal(L/K)) with
      mul_comm := fun a b => (IsMulCommutative.is_comm (M := Gal(L/K))).comm a b }
  have := kummerGroup_finite K n L
  have := finite_monoidHom_rootsOfUnity (K := K) (n := n) Gal(L/K)
  have := finite_monoidHom_rootsOfUnity (K := K) (n := n) (kummerGroup K n L)
  rw [← IsGalois.card_aut_eq_finrank]
  apply le_antisymm
  · calc Nat.card (kummerGroup K n L) ≤ Nat.card (Gal(L/K) →* rootsOfUnity n K) :=
          Nat.card_le_card_of_injective _ (kummerPairingRight_injective K n L)
      _ = Nat.card Gal(L/K) :=
          card_monoidHom_rootsOfUnity Gal(L/K) (Monoid.exponent_dvd_iff_forall_pow_eq_one.mp hexp)
  · calc Nat.card Gal(L/K) ≤ Nat.card (kummerGroup K n L →* rootsOfUnity n K) :=
          Nat.card_le_card_of_injective _ (kummerPairingLeft_injective K n L hexp)
      _ = Nat.card (kummerGroup K n L) :=
          card_monoidHom_rootsOfUnity (kummerGroup K n L) (kummerGroup_pow_eq_one K n L)
theorem kummerPairingLeft_bijective [FiniteDimensional K L] [IsGalois K L]
    [IsMulCommutative Gal(L/K)] (hexp : Monoid.exponent Gal(L/K) ∣ n) :
    Function.Bijective (kummerPairingLeft K n L) := by
  have := kummerGroup_finite K n L
  have := finite_monoidHom_rootsOfUnity (K := K) (n := n) (kummerGroup K n L)
  rw [Nat.bijective_iff_injective_and_card]
  refine ⟨kummerPairingLeft_injective K n L hexp, ?_⟩
  rw [IsGalois.card_aut_eq_finrank, ← card_kummerGroup K n L hexp]
  exact (card_monoidHom_rootsOfUnity (kummerGroup K n L) (kummerGroup_pow_eq_one K n L)).symm
theorem kummerPairingRight_bijective [FiniteDimensional K L] [IsGalois K L]
    [IsMulCommutative Gal(L/K)] (hexp : Monoid.exponent Gal(L/K) ∣ n) :
    Function.Bijective (kummerPairingRight K n L) := by
  let _ : CommGroup Gal(L/K) :=
    { (inferInstance : Group Gal(L/K)) with
      mul_comm := fun a b => (IsMulCommutative.is_comm (M := Gal(L/K))).comm a b }
  have := finite_monoidHom_rootsOfUnity (K := K) (n := n) Gal(L/K)
  rw [Nat.bijective_iff_injective_and_card]
  refine ⟨kummerPairingRight_injective K n L, ?_⟩
  rw [card_kummerGroup K n L hexp, ← IsGalois.card_aut_eq_finrank]
  exact (card_monoidHom_rootsOfUnity Gal(L/K) (Monoid.exponent_dvd_iff_forall_pow_eq_one.mp hexp)).symm
noncomputable def galEquivDual [FiniteDimensional K L] [IsGalois K L]
    [IsMulCommutative Gal(L/K)] (hexp : Monoid.exponent Gal(L/K) ∣ n) :
    Gal(L/K) ≃* (kummerGroup K n L →* rootsOfUnity n K) :=
  MulEquiv.ofBijective _ (kummerPairingLeft_bijective K n L hexp)
noncomputable def kummerGroupEquivDual [FiniteDimensional K L] [IsGalois K L]
    [IsMulCommutative Gal(L/K)] (hexp : Monoid.exponent Gal(L/K) ∣ n) :
    kummerGroup K n L ≃* (Gal(L/K) →* rootsOfUnity n K) :=
  MulEquiv.ofBijective _ (kummerPairingRight_bijective K n L hexp)
end Finite
end GroundTheory.ProfCoh


