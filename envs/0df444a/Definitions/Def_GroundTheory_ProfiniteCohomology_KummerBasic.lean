-- Prove2me | Definitions.Def_GroundTheory_ProfiniteCohomology_KummerBasic
-- name    : GroundTheory_ProfiniteCohomology_KummerBasic
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T05:07:19.582458+00:00
-- url     : https://prove2.me/theorems/c994a033-5952-488c-9913-1558b1b120bf
-- title:
--   Kummer Basic
-- statement:
--   Definitions and structural lemmas for Kummer Basic, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ProfiniteCohomology/KummerBasic.lean

import Mathlib
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
namespace GroundTheory.ProfCoh
open Polynomial
section Defs
variable (K : Type*) [Field K] (n : ℕ)
def unitsPow : Subgroup Kˣ := (powMonoidHom n : Kˣ →* Kˣ).range
abbrev UnitsModPow : Type _ := Kˣ ⧸ unitsPow K n
variable {K n} in
lemma mem_unitsPow {a : Kˣ} : a ∈ unitsPow K n ↔ ∃ b : Kˣ, b ^ n = a := by
  simp [unitsPow]
lemma UnitsModPow.pow_eq_one (x : UnitsModPow K n) : x ^ n = 1 := by
  induction x using QuotientGroup.induction_on with
  | H a =>
    rw [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff]
    exact mem_unitsPow.mpr ⟨a, rfl⟩
variable (L : Type*) [Field L] [Algebra K L]
def unitsPowIn : Subgroup Kˣ := (unitsPow L n).comap (Units.map (algebraMap K L : K →* L))
variable {K n L} in
lemma mem_unitsPowIn {a : Kˣ} : a ∈ unitsPowIn K n L ↔ ∃ α : L, α ^ n = algebraMap K L a := by
  simp only [unitsPowIn, Subgroup.mem_comap, mem_unitsPow]
  constructor
  · rintro ⟨b, hb⟩
    exact ⟨b, by simpa [Units.ext_iff] using congrArg Units.val hb⟩
  · rintro ⟨α, hα⟩
    by_cases h0 : α = 0
    · have hn : n = 0 := by
        by_contra hn
        rw [h0, zero_pow hn] at hα
        exact (map_ne_zero (algebraMap K L)).mpr a.ne_zero hα.symm
      subst hn
      refine ⟨1, ?_⟩
      ext
      simpa using hα
    · exact ⟨Units.mk0 α h0, by ext; simpa using hα⟩
def kummerGroup : Subgroup (UnitsModPow K n) :=
  (unitsPowIn K n L).map (QuotientGroup.mk' (unitsPow K n))
noncomputable def toKummerGroup : unitsPowIn K n L →* kummerGroup K n L :=
  ((QuotientGroup.mk' (unitsPow K n)).comp (unitsPowIn K n L).subtype).codRestrict _
    (fun a => Subgroup.mem_map_of_mem _ a.2)
lemma toKummerGroup_surjective : Function.Surjective (toKummerGroup K n L) := by
  rintro ⟨x, a, ha, rfl⟩
  exact ⟨⟨a, ha⟩, rfl⟩
lemma ker_toKummerGroup :
    (toKummerGroup K n L).ker = (unitsPow K n).subgroupOf (unitsPowIn K n L) := by
  ext a
  rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf, ← QuotientGroup.eq_one_iff (N := unitsPow K n)]
  constructor
  · intro h
    exact congrArg Subtype.val h
  · intro h
    exact Subtype.ext h
noncomputable def kummerGroupEquiv :
    (unitsPowIn K n L ⧸ (unitsPow K n).subgroupOf (unitsPowIn K n L)) ≃* kummerGroup K n L :=
  (QuotientGroup.quotientMulEquivOfEq (ker_toKummerGroup K n L).symm).trans
    (QuotientGroup.quotientKerEquivOfSurjective _ (toKummerGroup_surjective K n L))
end Defs
section RootsOfUnity
variable {K : Type*} [Field K] {n : ℕ} [NeZero n] [HasEnoughRootsOfUnity K n]
variable {L : Type*} [Field L] [Algebra K L]
lemma exists_algebraMap_eq_of_pow_eq_one {x : L} (hx : x ^ n = 1) :
    ∃ ζ : rootsOfUnity n K, algebraMap K L ((ζ : Kˣ) : K) = x := by
  obtain ⟨ζ, hζ⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot K n
  obtain ⟨i, -, hi⟩ := (hζ.map_of_injective (algebraMap K L).injective).eq_pow_of_pow_eq_one hx
  refine ⟨⟨(hζ.isUnit (NeZero.ne n)).unit ^ i, ?_⟩, ?_⟩
  · rw [mem_rootsOfUnity', Units.val_pow_eq_pow_val, IsUnit.unit_spec, ← pow_mul, mul_comm,
      pow_mul, hζ.pow_eq_one, one_pow]
  · simpa using hi
lemma algHom_apply_eq_self_of_pow_eq_one {x : L} (hx : x ^ n = 1) (σ : L →ₐ[K] L) :
    σ x = x := by
  obtain ⟨ζ, rfl⟩ := exists_algebraMap_eq_of_pow_eq_one (K := K) hx
  exact σ.commutes _
omit [HasEnoughRootsOfUnity K n] in
lemma ne_zero_of_pow_eq_algebraMap {a : Kˣ} {α : L} (hα : α ^ n = algebraMap K L a) : α ≠ 0 := by
  rintro rfl
  rw [zero_pow (NeZero.ne n)] at hα
  exact (map_ne_zero (algebraMap K L)).mpr a.ne_zero hα.symm
end RootsOfUnity
section Pairing
variable (K : Type*) [Field K] (n : ℕ) [NeZero n] [HasEnoughRootsOfUnity K n]
variable (L : Type*) [Field L] [Algebra K L]
lemma exists_kummer_value (σ : Gal(L/K)) (x : kummerGroup K n L) :
    ∃ ζ : rootsOfUnity n K, ∀ a : Kˣ, (a : UnitsModPow K n) = x →
      ∀ α : L, α ^ n = algebraMap K L a → σ α = algebraMap K L ((ζ : Kˣ) : K) * α := by
  obtain ⟨x, a₀, ha₀, rfl⟩ := x
  obtain ⟨α₀, hα₀⟩ := mem_unitsPowIn.mp ha₀
  have hα₀0 : α₀ ≠ 0 := ne_zero_of_pow_eq_algebraMap hα₀
  have hσ : (σ α₀ / α₀) ^ n = 1 := by
    rw [div_pow, ← map_pow, hα₀, AlgEquiv.commutes, div_self]
    exact (map_ne_zero (algebraMap K L)).mpr a₀.ne_zero
  obtain ⟨ζ, hζ⟩ := exists_algebraMap_eq_of_pow_eq_one (K := K) hσ
  refine ⟨ζ, fun a ha α hα => ?_⟩

  obtain ⟨c, hc⟩ := mem_unitsPow.mp (QuotientGroup.eq.mp ha)
  set γ := algebraMap K L (c : K) with hγ
  have hγ0 : γ ≠ 0 := (map_ne_zero (algebraMap K L)).mpr c.ne_zero
  have ha0 : algebraMap K L (a : K) ≠ 0 := (map_ne_zero (algebraMap K L)).mpr a.ne_zero
  have ha' : algebraMap K L (a₀ : K) = algebraMap K L (a : K) * γ ^ n := by
    have h1 : (c : K) ^ n = (a : K)⁻¹ * (a₀ : K) := by
      simpa only [Units.val_pow_eq_pow_val, Units.val_mul, Units.val_inv_eq_inv_val]
        using congrArg Units.val hc
    have h2 : (a₀ : K) = (a : K) * (c : K) ^ n := by
      rw [h1, ← mul_assoc, mul_inv_cancel₀ a.ne_zero, one_mul]
    rw [h2, map_mul, map_pow]
  have hη : (α * γ / α₀) ^ n = 1 := by
    rw [div_pow, mul_pow, hα, hα₀, ha']
    exact div_self (mul_ne_zero ha0 (pow_ne_zero _ hγ0))
  have hfix : σ (α * γ / α₀) = α * γ / α₀ :=
    algHom_apply_eq_self_of_pow_eq_one (K := K) hη (σ : L →ₐ[K] L)
  have hσγ : σ γ = γ := σ.commutes _
  have hσα₀ : σ α₀ = algebraMap K L ((ζ : Kˣ) : K) * α₀ := by
    rw [hζ, div_mul_cancel₀ _ hα₀0]
  have hσα₀0 : σ α₀ ≠ 0 := (map_ne_zero σ).mpr hα₀0
  have key : σ α * γ / σ α₀ = α * γ / α₀ := by
    rw [← hfix, map_div₀, map_mul, hσγ]
  calc σ α = (σ α * γ / σ α₀) * (σ α₀ / γ) := by field_simp
    _ = (α * γ / α₀) * (algebraMap K L ((ζ : Kˣ) : K) * α₀ / γ) := by rw [key, hσα₀]
    _ = algebraMap K L ((ζ : Kˣ) : K) * α := by field_simp
noncomputable def kummerPairing (σ : Gal(L/K)) (x : kummerGroup K n L) : rootsOfUnity n K :=
  (exists_kummer_value K n L σ x).choose
variable {K n L}
lemma kummerPairing_spec (σ : Gal(L/K)) (x : kummerGroup K n L) {a : Kˣ}
    (ha : (a : UnitsModPow K n) = x) {α : L} (hα : α ^ n = algebraMap K L a) :
    σ α = algebraMap K L ((kummerPairing K n L σ x : Kˣ) : K) * α :=
  (exists_kummer_value K n L σ x).choose_spec a ha α hα
lemma kummerPairing_eq_of_apply (σ : Gal(L/K)) (x : kummerGroup K n L) {a : Kˣ}
    (ha : (a : UnitsModPow K n) = x) {α : L} (hα : α ^ n = algebraMap K L a)
    (ζ : rootsOfUnity n K) (h : σ α = algebraMap K L ((ζ : Kˣ) : K) * α) :
    kummerPairing K n L σ x = ζ := by
  have h' := kummerPairing_spec σ x ha hα
  rw [h] at h'
  have := mul_right_cancel₀ (ne_zero_of_pow_eq_algebraMap hα) h'
  ext
  exact ((algebraMap K L).injective this).symm
lemma kummerPairing_eq_one_iff (σ : Gal(L/K)) (x : kummerGroup K n L) {a : Kˣ}
    (ha : (a : UnitsModPow K n) = x) {α : L} (hα : α ^ n = algebraMap K L a) :
    kummerPairing K n L σ x = 1 ↔ σ α = α := by
  constructor
  · intro h
    rw [kummerPairing_spec σ x ha hα, h]
    simp
  · intro h
    exact kummerPairing_eq_of_apply σ x ha hα 1 (by rw [h]; simp)
omit [NeZero n] [HasEnoughRootsOfUnity K n] in
lemma exists_rep (x : kummerGroup K n L) :
    ∃ a : Kˣ, (a : UnitsModPow K n) = x ∧ ∃ α : L, α ^ n = algebraMap K L a := by
  obtain ⟨x, a, ha, rfl⟩ := x
  exact ⟨a, rfl, mem_unitsPowIn.mp ha⟩
lemma kummerPairing_mul_left (σ τ : Gal(L/K)) (x : kummerGroup K n L) :
    kummerPairing K n L (σ * τ) x = kummerPairing K n L σ x * kummerPairing K n L τ x := by
  obtain ⟨a, ha, α, hα⟩ := exists_rep x
  apply kummerPairing_eq_of_apply (σ * τ) x ha hα
  rw [AlgEquiv.mul_apply, kummerPairing_spec τ x ha hα, map_mul, AlgEquiv.commutes,
    kummerPairing_spec σ x ha hα]
  simp only [Subgroup.coe_mul, Units.val_mul, map_mul]
  ring
lemma kummerPairing_mul_right (σ : Gal(L/K)) (x y : kummerGroup K n L) :
    kummerPairing K n L σ (x * y) = kummerPairing K n L σ x * kummerPairing K n L σ y := by
  obtain ⟨a, ha, α, hα⟩ := exists_rep x
  obtain ⟨b, hb, β, hβ⟩ := exists_rep y
  have hab : ((a * b : Kˣ) : UnitsModPow K n) =
      ((x * y : kummerGroup K n L) : UnitsModPow K n) := by
    rw [QuotientGroup.mk_mul, ha, hb]
    rfl
  have hαβ : (α * β) ^ n = algebraMap K L ((a * b : Kˣ) : K) := by
    rw [mul_pow, hα, hβ, Units.val_mul, map_mul]
  apply kummerPairing_eq_of_apply σ (x * y) hab hαβ
  rw [map_mul, kummerPairing_spec σ x ha hα, kummerPairing_spec σ y hb hβ]
  simp only [Subgroup.coe_mul, Units.val_mul, map_mul]
  ring
lemma kummerPairing_one_left (x : kummerGroup K n L) : kummerPairing K n L 1 x = 1 := by
  obtain ⟨a, ha, α, hα⟩ := exists_rep x
  exact (kummerPairing_eq_one_iff 1 x ha hα).mpr rfl
lemma kummerPairing_one_right (σ : Gal(L/K)) : kummerPairing K n L σ 1 = 1 := by
  have h := kummerPairing_mul_right σ (1 : kummerGroup K n L) 1
  rw [mul_one] at h
  exact (mul_eq_left.mp h.symm)
variable (K n L)
noncomputable def kummerPairingLeft : Gal(L/K) →* (kummerGroup K n L →* rootsOfUnity n K) where
  toFun σ :=
    { toFun := kummerPairing K n L σ
      map_one' := kummerPairing_one_right σ
      map_mul' := kummerPairing_mul_right σ }
  map_one' := by ext x : 1; exact kummerPairing_one_left x
  map_mul' σ τ := by ext x : 1; exact kummerPairing_mul_left σ τ x
noncomputable def kummerPairingRight : kummerGroup K n L →* (Gal(L/K) →* rootsOfUnity n K) where
  toFun x :=
    { toFun := fun σ => kummerPairing K n L σ x
      map_one' := kummerPairing_one_left x
      map_mul' := fun σ τ => kummerPairing_mul_left σ τ x }
  map_one' := by ext σ : 1; exact kummerPairing_one_right σ
  map_mul' x y := by ext σ : 1; exact kummerPairing_mul_right σ x y
end Pairing
section Field
variable (K : Type*) [Field K] (n : ℕ)
def kummerField (Ω : Type*) [Field Ω] [Algebra K Ω] (Δ : Subgroup (UnitsModPow K n)) :
    IntermediateField K Ω :=
  IntermediateField.adjoin K
    {α : Ω | ∃ a : Kˣ, (a : UnitsModPow K n) ∈ Δ ∧ α ^ n = algebraMap K Ω a}
end Field
end GroundTheory.ProfCoh


