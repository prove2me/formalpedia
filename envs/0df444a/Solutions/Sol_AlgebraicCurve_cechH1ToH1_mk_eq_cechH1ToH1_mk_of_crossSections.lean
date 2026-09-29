-- Prove2me | solution 1 for AlgebraicCurve.cechH1ToH1_mk_eq_cechH1ToH1_mk_of_crossSections
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:02.4153+00:00
-- url     : https://prove2.me/submissions/abaad9f6-229f-567d-9aa8-de403450dcf7

import Mathlib
import Definitions.Def_AlgebraicCurve_CechSectionsOfDivisor
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicCurve_cechH1ToH1_mk_eq_cechH1ToH1_mk_of_crossSections

set_option autoImplicit false

open AlgebraicCurve

theorem solution
    {K F : Type*} [Field K] [Field F] [Algebra K F]
    {S₀ S₁ T₀ T₁ : Set (Place K F)} (hS : S₀ ∪ S₁ = Set.univ) (hT : T₀ ∪ T₁ = Set.univ)
    (f : ↥(lSpaceOn (S₀ ∩ S₁) (0 : Divisor K F))) (f' : ↥(lSpaceOn (T₀ ∩ T₁) (0 : Divisor K F)))
    (g₀₀ g₀₁ g₁₀ g₁₁ : F)
    (h₀₀ : g₀₀ ∈ lSpaceOn (S₀ ∩ T₀) (0 : Divisor K F)) (h₀₁ : g₀₁ ∈ lSpaceOn (S₀ ∩ T₁) (0 : Divisor K F))
    (h₁₀ : g₁₀ ∈ lSpaceOn (S₁ ∩ T₀) (0 : Divisor K F)) (h₁₁ : g₁₁ ∈ lSpaceOn (S₁ ∩ T₁) (0 : Divisor K F))
    (e₀ : g₀₀ = g₁₀ + (f : F)) (e₁ : g₀₁ = g₁₁ + (f : F)) (e₀' : g₀₁ = g₀₀ + (f' : F)) :
    cechH1ToH1 hS 0 (Submodule.Quotient.mk f) = cechH1ToH1 hT 0 (Submodule.Quotient.mk f') := by
  have key : extendOffChart K S₀ (f : F) - extendOffChart K T₀ (f' : F)
      - algebraMap F (↥(repartitions K F)) g₀₀ ∈ repartitionsOf (0 : Divisor K F) := by
    intro v
    rw [AddSubgroupClass.coe_sub, AddSubgroupClass.coe_sub, Pi.sub_apply, Pi.sub_apply,
      Subalgebra.coe_algebraMap, Pi.algebraMap_apply, Algebra.algebraMap_self, RingHom.id_apply]
    have hS' : v ∈ S₀ ∪ S₁ := hS ▸ Set.mem_univ v
    have hT' : v ∈ T₀ ∪ T₁ := hT ▸ Set.mem_univ v
    by_cases hvS : v ∈ S₀ <;> by_cases hvT : v ∈ T₀
    · rw [coe_extendOffChart_apply_of_mem _ hvS, coe_extendOffChart_apply_of_mem _ hvT,
        show (0 : F) - 0 - g₀₀ = -g₀₀ by ring, Valuation.map_neg]
      exact h₀₀ v ⟨hvS, hvT⟩
    · rw [coe_extendOffChart_apply_of_mem _ hvS, coe_extendOffChart_apply_of_not_mem _ hvT,
        show (0 : F) - (f' : F) - g₀₀ = -g₀₁ by rw [e₀']; ring, Valuation.map_neg]
      exact h₀₁ v ⟨hvS, hT'.resolve_left hvT⟩
    · rw [coe_extendOffChart_apply_of_not_mem _ hvS, coe_extendOffChart_apply_of_mem _ hvT,
        show (f : F) - 0 - g₀₀ = -g₁₀ by rw [e₀]; ring, Valuation.map_neg]
      exact h₁₀ v ⟨hS'.resolve_left hvS, hvT⟩
    · rw [coe_extendOffChart_apply_of_not_mem _ hvS, coe_extendOffChart_apply_of_not_mem _ hvT,
        show (f : F) - (f' : F) - g₀₀ = -g₁₁ by linear_combination e₀' - e₁, Valuation.map_neg]
      exact h₁₁ v ⟨hS'.resolve_left hvS, hT'.resolve_left hvT⟩
  rw [cechH1ToH1_mk, cechH1ToH1_mk, Submodule.Quotient.eq,
    ← sub_add_cancel (extendOffChart K S₀ (f : F) - extendOffChart K T₀ (f' : F))
      (algebraMap F (↥(repartitions K F)) g₀₀)]
  exact Submodule.add_mem _ (Submodule.mem_sup_left key)
    (Submodule.mem_sup_right (algebraMap_mem_principalRepartitions _))

end S_AlgebraicCurve_cechH1ToH1_mk_eq_cechH1ToH1_mk_of_crossSections
end P2MW
export P2MW.S_AlgebraicCurve_cechH1ToH1_mk_eq_cechH1ToH1_mk_of_crossSections (solution)
