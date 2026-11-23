-- Prove2me | Definitions.Def_GroundTheory_GlobalFields_CyclotomicCharacters_Character
-- name    : GroundTheory_GlobalFields_CyclotomicCharacters_Character
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T05:24:58.566677+00:00
-- url     : https://prove2.me/theorems/41cb7cd4-e385-40aa-8860-2bf6ff253ba0
-- title:
--   Character
-- statement:
--   Definitions and structural lemmas for Character, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/CyclotomicCharacters/Character.lean

import Mathlib
import Definitions.Def_GroundTheory_LocalFields_AbstractLocalReciprocity_ProfiniteInteger
import Definitions.Def_GroundTheory_GlobalFields_CyclotomicCharacters_Frobenius
import Theorems.Thm_GroundTheory_LocalField_Abstract_ProfiniteInteger_castHom_proj

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
set_option synthInstance.maxHeartbeats 400000
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IntermediateField
open scoped Pointwise
open scoped GroundTheory.LocalField.Abstract
namespace GroundTheory.Global
namespace Cyclotomic
open GroundTheory.LocalField.Abstract
local notation "ℚ̄" => AlgebraicClosure ℚ
instance isAlgClosure_rat : IsAlgClosure ℚ ℚ̄ := by
  let i : Algebra ℚ ℚ̄ := AlgebraicClosure.instAlgebra ℚ (R := ℚ)
  have h : IsAlgClosure ℚ ℚ̄ := inferInstance
  convert h
  exact Subsingleton.elim _ _
section FixingSubgroup
variable {F E : Type*} [Field F] [Field E] [Algebra F E]
end FixingSubgroup
section Fields
noncomputable def rootsOfUnityField (n : ℕ) : IntermediateField ℚ ℚ̄ :=
  adjoin ℚ {x : ℚ̄ | x ^ n = 1}
noncomputable def maxCyclotomic : IntermediateField ℚ ℚ̄ :=
  adjoin ℚ {x : ℚ̄ | ∃ n : ℕ, 0 < n ∧ x ^ n = 1}
theorem rootsOfUnityField_eq_adjoin {n : ℕ} [NeZero n] {ζ : ℚ̄} (hζ : IsPrimitiveRoot ζ n) :
    rootsOfUnityField n = ℚ⟮ζ⟯ := by
  refine le_antisymm (adjoin_le_iff.mpr fun x hx => ?_) (adjoin_le_iff.mpr ?_)
  · obtain ⟨i, -, rfl⟩ := hζ.eq_pow_of_pow_eq_one hx
    exact pow_mem (mem_adjoin_simple_self ℚ ζ) i
  · rw [Set.singleton_subset_iff]
    exact subset_adjoin ℚ _ hζ.pow_eq_one
instance (n : ℕ) [NeZero n] : IsCyclotomicExtension {n} ℚ (rootsOfUnityField n) := by
  obtain ⟨ζ, hζ⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot ℚ̄ n
  rw [rootsOfUnityField_eq_adjoin hζ]
  exact hζ.intermediateField_adjoin_isCyclotomicExtension ℚ
instance (n : ℕ) [NeZero n] : NumberField (rootsOfUnityField n) :=
  IsCyclotomicExtension.numberField {n} ℚ _
instance (n : ℕ) [NeZero n] : IsGalois ℚ (rootsOfUnityField n) :=
  IsCyclotomicExtension.isGalois {n} ℚ _
end Fields
section Modular
theorem pow_val_natCast {M : Type*} [Monoid M] {n : ℕ} {t : M} (ht : t ^ n = 1) (k : ℕ) :
    t ^ (k : ZMod n).val = t ^ k := by
  rw [ZMod.val_natCast]
  conv_rhs => rw [← Nat.mod_add_div k n, pow_add, pow_mul, ht, one_pow, mul_one]
theorem natCard_rootsOfUnity (n : ℕ) [NeZero n] : Nat.card (rootsOfUnity n ℚ̄) = n :=
  HasEnoughRootsOfUnity.natCard_rootsOfUnity ℚ̄ n
noncomputable def modCharacter (n : ℕ) [NeZero n] : Gal(ℚ̄/ℚ) →* (ZMod n)ˣ :=
  (modularCyclotomicCharacter ℚ̄ (natCard_rootsOfUnity n)).comp
    (MulSemiringAction.toRingAut Gal(ℚ̄/ℚ) ℚ̄)
variable {n : ℕ} [NeZero n]
theorem modCharacter_spec (σ : Gal(ℚ̄/ℚ)) {t : ℚ̄} (ht : t ^ n = 1) :
    σ t = t ^ (modCharacter n σ : ZMod n).val := by
  have ht0 : t ≠ 0 := by
    rintro rfl
    simp [NeZero.ne n] at ht
  have hmem : Units.mk0 t ht0 ∈ rootsOfUnity n ℚ̄ := by
    rw [mem_rootsOfUnity]; ext; simpa using ht
  exact modularCyclotomicCharacter.spec ℚ̄ (natCard_rootsOfUnity n)
    (MulSemiringAction.toRingAut Gal(ℚ̄/ℚ) ℚ̄ σ) hmem
theorem modCharacter_unique (σ : Gal(ℚ̄/ℚ)) {c : ZMod n}
    (hc : ∀ t : ℚ̄, t ^ n = 1 → σ t = t ^ c.val) : (modCharacter n σ : ZMod n) = c := by
  refine (modularCyclotomicCharacter.unique ℚ̄ (natCard_rootsOfUnity n)
    (MulSemiringAction.toRingAut Gal(ℚ̄/ℚ) ℚ̄ σ) fun t ht => ?_).symm
  have ht' : (t : ℚ̄) ^ n = 1 := by
    rw [mem_rootsOfUnity] at ht
    simpa using congrArg Units.val ht
  simpa using hc t ht'
theorem castHom_modCharacter {m : ℕ} [NeZero m] (h : m ∣ n) (σ : Gal(ℚ̄/ℚ)) :
    ZMod.castHom h (ZMod m) (modCharacter n σ : ZMod n) = modCharacter m σ := by
  refine (modCharacter_unique σ fun t ht => ?_).symm
  have ht' : t ^ n = 1 := by
    obtain ⟨k, rfl⟩ := h
    rw [pow_mul, ht, one_pow]
  rw [modCharacter_spec σ ht', ZMod.castHom_apply]
  conv_rhs => rw [← ZMod.natCast_zmod_val (modCharacter n σ : ZMod n), ZMod.cast_natCast h,
    pow_val_natCast ht]
end Modular
section Character
noncomputable def characterToZHat : Gal(ℚ̄/ℚ) →* ℤ̂ where
  toFun σ := ⟨fun n => (modCharacter n σ : ZMod n), mem_profiniteIntegers.mpr
    fun m n h => castHom_modCharacter h σ⟩
  map_one' := by
    ext n
    simp [ProfiniteInteger.proj_apply]
  map_mul' σ τ := by
    ext n
    simp [ProfiniteInteger.proj_apply]
noncomputable def character : Gal(ℚ̄/ℚ) →* ℤ̂ˣ :=
  characterToZHat.toHomUnits
@[simp] theorem proj_character (n : ℕ+) (σ : Gal(ℚ̄/ℚ)) :
    ProfiniteInteger.proj n (character σ : ℤ̂) = (modCharacter n σ : ZMod n) :=
  rfl
end Character
section Frobenius
variable (m : ℕ) [NeZero m] (p : ℕ) [Fact p.Prime] (P : Ideal (𝓞 (rootsOfUnityField m)))
  [P.IsPrime] [P.LiesOver (Ideal.span {(p : ℤ)})]
end Frobenius
section Padic
variable (ℓ : ℕ) [hℓ : Fact ℓ.Prime]
def primePowPNat (k : ℕ) : ℕ+ := ⟨ℓ ^ k, pow_pos hℓ.out.pos k⟩
@[simp] theorem coe_primePowPNat (k : ℕ) : (primePowPNat ℓ k : ℕ) = ℓ ^ k := rfl
noncomputable def toPadicInt : ℤ̂ →+* ℤ_[ℓ] :=
  PadicInt.lift (f := fun k => ProfiniteInteger.proj (primePowPNat ℓ k))
    fun k₁ k₂ hk => by
      ext x
      exact ProfiniteInteger.castHom_proj (m := primePowPNat ℓ k₁) (n := primePowPNat ℓ k₂)
        (pow_dvd_pow ℓ hk) x
end Padic
end Cyclotomic
end GroundTheory.Global


