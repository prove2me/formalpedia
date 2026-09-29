-- Prove2me | solution 1 for AddMonoidHom.exists_pos_forall_nsmul_eq_zero_of_add_eq_zero_of_finite_fixedPoints_comp_self
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:01.734404+00:00
-- url     : https://prove2.me/submissions/6671e34e-b5dc-5e1f-882f-7bca0f8268a9

import Mathlib
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AddMonoidHom_exists_pos_forall_nsmul_eq_zero_of_add_eq_zero_of_finite_fixedPoints_comp_self

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

theorem solution
    {M : Type u} [AddCommGroup M] (F : M →+ M)
    (hfin : (Function.fixedPoints (F ∘ F)).Finite) :
    ∃ c : ℕ, 0 < c ∧ ∀ a₀ a₁ : M, a₀ + F a₁ = 0 → F a₀ + a₁ = 0 → c • a₀ = 0 ∧ c • a₁ = 0 := by

  let H : AddSubgroup M :=
    { carrier := Function.fixedPoints (F ∘ F)
      add_mem' := fun {a b} ha hb => by
        simp only [Function.mem_fixedPoints_iff, Function.comp_apply, map_add] at ha hb ⊢
        rw [ha, hb]
      zero_mem' := by
        change F (F 0) = 0
        rw [map_zero, map_zero]
      neg_mem' := fun {a} ha => by
        simp only [Function.mem_fixedPoints_iff, Function.comp_apply, map_neg] at ha ⊢
        rw [ha] }
  haveI : Finite H := hfin.to_subtype
  refine ⟨Nat.card H, Nat.card_pos, fun a₀ a₁ h₀ h₁ => ?_⟩
  have ha₀ : a₀ = -F a₁ := eq_neg_of_add_eq_zero_left h₀
  have ha₁ : a₁ ∈ H := by
    change F (F a₁) = a₁
    rw [ha₀, map_neg, neg_add_eq_zero] at h₁
    exact h₁
  have hc₁ : Nat.card H • a₁ = 0 := by
    have h := card_nsmul_eq_zero' (G := H) (x := ⟨a₁, ha₁⟩)
    exact congrArg Subtype.val h
  exact ⟨by rw [ha₀, smul_neg, ← map_nsmul, hc₁, map_zero, neg_zero], hc₁⟩

end S_AddMonoidHom_exists_pos_forall_nsmul_eq_zero_of_add_eq_zero_of_finite_fixedPoints_comp_self
end P2MW
export P2MW.S_AddMonoidHom_exists_pos_forall_nsmul_eq_zero_of_add_eq_zero_of_finite_fixedPoints_comp_self (solution)
