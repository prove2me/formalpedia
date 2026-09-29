-- Prove2me | solution 1 for AlgEquiv.isGalois_and_orderOf_eq_finrank_of_finrank_prime_of_ne_one
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:01.734404+00:00
-- url     : https://prove2.me/submissions/065d38a2-c49a-54ec-aec2-ac671937e5aa

import Mathlib
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgEquiv_isGalois_and_orderOf_eq_finrank_of_finrank_prime_of_ne_one

set_option autoImplicit false

open IntermediateField

theorem solution (K L : Type*) [Field K] [Field L] [Algebra K L]
    (hdeg : (Module.finrank K L).Prime) (σ : L ≃ₐ[K] L) (hσ : σ ≠ 1) :
    IsGalois K L ∧ orderOf σ = Module.finrank K L ∧ Subgroup.zpowers σ = ⊤ := by
  haveI : FiniteDimensional K L := Module.finite_of_finrank_pos hdeg.pos
  set H : Subgroup (L ≃ₐ[K] L) := Subgroup.zpowers σ with hH

  have h1 : Module.finrank (fixedField H) L = orderOf σ := by
    rw [finrank_fixedField_eq_card, hH, Nat.card_zpowers]

  have htower : Module.finrank K (fixedField H) * Module.finrank (fixedField H) L = Module.finrank K L :=
    Module.finrank_mul_finrank K (fixedField H) L
  have hordpos : 0 < orderOf σ := orderOf_pos σ
  have hord_ne_one : orderOf σ ≠ 1 := fun h => hσ (orderOf_eq_one_iff.1 h)
  have hdvd : orderOf σ ∣ Module.finrank K L := ⟨Module.finrank K (fixedField H), by rw [← h1, mul_comm]; exact htower.symm⟩
  have hord : orderOf σ = Module.finrank K L := by
    rcases (Nat.dvd_prime hdeg).1 hdvd with h | h
    · exact absurd h hord_ne_one
    · exact h
  have hbot : fixedField H = ⊥ := by
    rw [← IntermediateField.finrank_eq_one_iff]
    have h2 : Module.finrank K (fixedField H) * Module.finrank K L = 1 * Module.finrank K L := by
      rw [one_mul]
      conv_rhs => rw [← htower]
      rw [h1, hord]
    exact Nat.eq_of_mul_eq_mul_right hdeg.pos h2
  have hgal : IsGalois K L := by
    apply IsGalois.of_fixedField_eq_bot
    exact le_bot_iff.1 (hbot ▸ fixedField_le le_top)
  refine ⟨hgal, hord, ?_⟩
  haveI := hgal
  apply Subgroup.eq_top_of_card_eq
  rw [hH, Nat.card_zpowers, hord, IsGalois.card_aut_eq_finrank]

end S_AlgEquiv_isGalois_and_orderOf_eq_finrank_of_finrank_prime_of_ne_one
end P2MW
export P2MW.S_AlgEquiv_isGalois_and_orderOf_eq_finrank_of_finrank_prime_of_ne_one (solution)
