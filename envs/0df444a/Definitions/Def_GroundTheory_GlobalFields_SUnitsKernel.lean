-- Prove2me | Definitions.Def_GroundTheory_GlobalFields_SUnitsKernel
-- name    : GroundTheory_GlobalFields_SUnitsKernel
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T05:07:45.330804+00:00
-- url     : https://prove2.me/theorems/3bc27a55-3ebf-4619-8536-3000ebbdbdf4
-- title:
--   SUnits Kernel
-- statement:
--   Definitions and structural lemmas for SUnits Kernel, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/SUnitsKernel.lean

import Mathlib
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
set_option synthInstance.maxHeartbeats 400000
-- END pinned source Lake options
set_option autoImplicit false
namespace GroundTheory.Global
open NumberField IsDedekindDomain IsDedekindDomain.HeightOneSpectrum Module
open scoped NumberField nonZeroDivisors
noncomputable section
variable {K : Type*} [Field K] [NumberField K]
namespace SUnit
theorem forall_valuation_eq_one_iff (x : Kˣ) :
    (∀ v : HeightOneSpectrum (𝓞 K), v.valuation K (x : K) = 1) ↔
      x ∈ (Units.map (algebraMap (𝓞 K) K : 𝓞 K →* K)).range := by
  constructor
  · intro h
    obtain ⟨a, ha⟩ := mem_integers_of_valuation_le_one (R := 𝓞 K) K (x : K) fun v => (h v).le
    obtain ⟨b, hb⟩ := mem_integers_of_valuation_le_one (R := 𝓞 K) K ((x⁻¹ : Kˣ) : K) fun v => by
      rw [Units.val_inv_eq_inv_val, map_inv₀, h v, inv_one]
    have hab : a * b = 1 := by
      apply IsFractionRing.injective (𝓞 K) K
      rw [map_mul, ha, hb, map_one, Units.mul_inv]
    have hba : b * a = 1 := by rw [mul_comm, hab]
    refine ⟨⟨a, b, hab, hba⟩, ?_⟩
    ext
    simp [ha]
  · rintro ⟨u, rfl⟩ v
    rw [← valuationOfNeZero_eq, valuation_of_unit_eq, WithZero.coe_one]
variable (S : Set (HeightOneSpectrum (𝓞 K)))
def ofUnits : (𝓞 K)ˣ →* S.unit K where
  toFun u := ⟨Units.map (algebraMap (𝓞 K) K : 𝓞 K →* K) u, fun v _ =>
    (forall_valuation_eq_one_iff _).mpr ⟨u, rfl⟩ v⟩
  map_one' := by ext; simp
  map_mul' _ _ := by ext; simp
@[simp]
theorem coe_ofUnits (u : (𝓞 K)ˣ) : ((ofUnits S u : Kˣ) : K) = algebraMap (𝓞 K) K u := rfl
theorem ofUnits_injective : Function.Injective (ofUnits S (K := K)) := by
  intro u u' h
  have : ((ofUnits S u : Kˣ) : K) = ((ofUnits S u' : Kˣ) : K) := by rw [h]
  simp only [coe_ofUnits] at this
  exact Units.ext (IsFractionRing.injective (𝓞 K) K this)
def valuationVector : Additive (S.unit K) →ₗ[ℤ] (S → ℤ) :=
  AddMonoidHom.toIntLinearMap
    { toFun := fun x v => Multiplicative.toAdd (v.1.valuationOfNeZero ((x.toMul : S.unit K) : Kˣ))
      map_zero' := by funext v; simp
      map_add' := fun x y => by funext v; simp }
theorem valuationVector_apply (x : S.unit K) (v : S) :
    valuationVector S (Additive.ofMul x) v = Multiplicative.toAdd (v.1.valuationOfNeZero (x : Kˣ)) :=
  rfl
theorem mem_ker_valuationVector_iff (x : S.unit K) :
    Additive.ofMul x ∈ LinearMap.ker (valuationVector S) ↔
      ∀ v : HeightOneSpectrum (𝓞 K), v.valuation K ((x : Kˣ) : K) = 1 := by
  rw [LinearMap.mem_ker]
  constructor
  · intro h v
    by_cases hv : v ∈ S
    · have h1 := congrFun h ⟨v, hv⟩
      rw [valuationVector_apply, Pi.zero_apply, toAdd_eq_zero] at h1
      rw [← valuationOfNeZero_eq, h1, WithZero.coe_one]
    · exact x.2 v hv
  · intro h
    funext v
    rw [valuationVector_apply, Pi.zero_apply, toAdd_eq_zero, ← WithZero.coe_inj,
      valuationOfNeZero_eq, WithZero.coe_one]
    exact h v.1
theorem ker_valuationVector :
    LinearMap.ker (valuationVector S) =
      LinearMap.range (ofUnits S).toAdditive.toIntLinearMap := by
  ext x
  rw [← ofMul_toMul x, mem_ker_valuationVector_iff, LinearMap.mem_range]
  constructor
  · intro h
    obtain ⟨u, hu⟩ := (forall_valuation_eq_one_iff _).mp h
    exact ⟨Additive.ofMul u, by
      change Additive.ofMul (ofUnits S u) = _
      congr 1
      exact Subtype.ext hu⟩
  · rintro ⟨u, hu⟩
    have hx : ofUnits S u.toMul = x.toMul := congrArg Additive.toMul hu
    rw [← hx]
    exact (forall_valuation_eq_one_iff _).mpr ⟨u.toMul, rfl⟩
def unitsEquivKer : Additive (𝓞 K)ˣ ≃ₗ[ℤ] LinearMap.ker (valuationVector S) :=
  (LinearEquiv.ofInjective (ofUnits S).toAdditive.toIntLinearMap
    (ofUnits_injective S)).trans (LinearEquiv.ofEq _ _ (ker_valuationVector S).symm)
end SUnit
end
end GroundTheory.Global


