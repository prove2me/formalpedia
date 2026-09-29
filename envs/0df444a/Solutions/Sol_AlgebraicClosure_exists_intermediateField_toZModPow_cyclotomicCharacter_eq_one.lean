-- Prove2me | solution 1 for AlgebraicClosure.exists_intermediateField_toZModPow_cyclotomicCharacter_eq_one
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:01.734404+00:00
-- url     : https://prove2.me/submissions/7e261640-5694-5e90-a986-a1ab2e4358bc

import Mathlib
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicClosure_exists_intermediateField_toZModPow_cyclotomicCharacter_eq_one

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 1600000
open IntermediateField in

theorem solution
    (p : ℕ) [Fact p.Prime] (n : ℕ) :
    ∃ F : IntermediateField ℚ (AlgebraicClosure ℚ), FiniteDimensional ℚ F ∧
      ∀ τ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ, (∀ x ∈ F, τ x = x) →
        PadicInt.toZModPow n ((cyclotomicCharacter (AlgebraicClosure ℚ) p τ.toRingEquiv : ℤ_[p]ˣ) : ℤ_[p]) = 1 := by
  classical
  haveI hp0 : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
  haveI hEn : ∀ i : ℕ, HasEnoughRootsOfUnity (AlgebraicClosure ℚ) (p ^ i) := fun i => inferInstance
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · exact ⟨⊥, inferInstance, fun τ _ => (ZMod.subsingleton_iff.2 (pow_zero p)).elim _ _⟩
  · haveI : NeZero (p ^ n) := ⟨pow_ne_zero n (Fact.out : p.Prime).ne_zero⟩
    obtain ⟨ζ, hζ⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot (AlgebraicClosure ℚ) (p ^ n)
    refine ⟨ℚ⟮ζ⟯, IntermediateField.adjoin.finiteDimensional (hζ.isIntegral (NeZero.pos _)).tower_top, ?_⟩
    intro σ hσ
    rw [cyclotomicCharacter.toZModPow, eq_comm]
    apply modularCyclotomicCharacter.unique
    intro t ht
    obtain ⟨i, -, rfl⟩ := (hζ.isUnit_unit NeZero.out).eq_pow_of_mem_rootsOfUnity ht
    rw [ZMod.val_one'', pow_one]
    · exact hσ (ζ ^ i) (pow_mem (IntermediateField.mem_adjoin_simple_self ℚ ζ) _)
    · exact (one_lt_pow₀ (Fact.out : p.Prime).one_lt hn.ne').ne'

end S_AlgebraicClosure_exists_intermediateField_toZModPow_cyclotomicCharacter_eq_one
end P2MW
export P2MW.S_AlgebraicClosure_exists_intermediateField_toZModPow_cyclotomicCharacter_eq_one (solution)
