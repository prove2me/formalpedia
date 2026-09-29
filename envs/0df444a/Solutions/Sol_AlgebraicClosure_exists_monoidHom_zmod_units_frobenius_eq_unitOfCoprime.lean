-- Prove2me | solution 1 for AlgebraicClosure.exists_monoidHom_zmod_units_frobenius_eq_unitOfCoprime
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:01.734404+00:00
-- url     : https://prove2.me/submissions/43e8dfbe-a5bd-502b-a609-5cdee516d589

import Mathlib
import Definitions.Def_EllipticCurve_FrobeniusTrace
import Theorems.Thm_ValuationSubring_cycloChar_eq_unitOfCoprime_of_isFrobeniusAt
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicClosure_exists_monoidHom_zmod_units_frobenius_eq_unitOfCoprime

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 1600000
open IntermediateField in
theorem solution
    (L : ℕ) [NeZero L] :
    ∃ (χ : (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) →* (ZMod L)ˣ)
      (F : IntermediateField ℚ (AlgebraicClosure ℚ)), FiniteDimensional ℚ F ∧
      (∀ τ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ, (∀ x ∈ F, τ x = x) → χ τ = 1) ∧
      ∀ (ℓ : ℕ) (hℓ : ℓ.Prime) (hℓL : ¬ ℓ ∣ L)
        (A : ValuationSubring (AlgebraicClosure ℚ)), A.LiesOverPrime ℓ →
        ∀ σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ, A.IsFrobeniusAt σ ℓ →
          χ σ = ZMod.unitOfCoprime ℓ ((Nat.Prime.coprime_iff_not_dvd hℓ).mpr hℓL) := by
  classical
  obtain ⟨ζ, hζ⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot (AlgebraicClosure ℚ) L
  have hn : Nat.card (rootsOfUnity L (AlgebraicClosure ℚ)) = L := hζ.card_rootsOfUnity

  let χ : (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) →* (ZMod L)ˣ :=
    { toFun := fun σ => modularCyclotomicCharacter (AlgebraicClosure ℚ) hn σ.toRingEquiv
      map_one' := map_one _
      map_mul' := fun a b => by rw [← map_mul]; rfl }
  have hχ : ∀ σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ,
      χ σ = modularCyclotomicCharacter (AlgebraicClosure ℚ) hn σ.toRingEquiv := fun _ => rfl
  have hspec : ∀ (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) (μ : AlgebraicClosure ℚ),
      μ ^ L = 1 → σ μ = μ ^ ((χ σ : ZMod L)).val := by
    intro σ μ hμ
    have h := modularCyclotomicCharacter.spec (AlgebraicClosure ℚ) hn σ.toRingEquiv
      (t := (rootsOfUnity.mkOfPowEq μ hμ : (AlgebraicClosure ℚ)ˣ)) (rootsOfUnity.mkOfPowEq μ hμ).2
    rw [rootsOfUnity.val_mkOfPowEq_coe] at h
    rw [hχ]
    exact h
  refine ⟨χ, ℚ⟮ζ⟯, IntermediateField.adjoin.finiteDimensional (hζ.isIntegral (NeZero.pos L)).tower_top,
    ?_, ?_⟩
  ·
    intro τ hτ
    rcases eq_or_ne L 1 with rfl | hL1
    · exact Units.ext ((ZMod.subsingleton_iff.2 rfl).elim _ _)
    · rw [hχ]
      apply Units.ext
      rw [Units.val_one]
      refine (modularCyclotomicCharacter.unique (AlgebraicClosure ℚ) hn τ.toRingEquiv ?_).symm
      intro t ht
      obtain ⟨i, -, rfl⟩ := (hζ.isUnit_unit NeZero.out).eq_pow_of_mem_rootsOfUnity ht
      rw [ZMod.val_one'' hL1, pow_one]
      exact hτ (ζ ^ i) (pow_mem (IntermediateField.mem_adjoin_simple_self ℚ ζ) _)
  ·
    intro ℓ hℓ hℓL A hA σ hσ
    exact ValuationSubring.cycloChar_eq_unitOfCoprime_of_isFrobeniusAt L χ hspec ℓ hℓ hℓL A hA σ hσ

end S_AlgebraicClosure_exists_monoidHom_zmod_units_frobenius_eq_unitOfCoprime
end P2MW
export P2MW.S_AlgebraicClosure_exists_monoidHom_zmod_units_frobenius_eq_unitOfCoprime (solution)
