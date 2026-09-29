-- Prove2me | solution 1 for ArtinL.trace_restrict_invariants_eq_inv_card_mul_sum_trace
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.553648+00:00
-- url     : https://prove2.me/submissions/9704c69c-a727-5eb6-a6b4-cb6508c5e0d7

import Mathlib
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ArtinL_trace_restrict_invariants_eq_inv_card_mul_sum_trace
set_option autoImplicit false

theorem solution
    {K : Type*} [Field K] [CharZero K] {G : Type*} [Group G]
    {V : Type*} [AddCommGroup V] [Module K V] [FiniteDimensional K V]
    (ρ : Representation K G V) (I : Subgroup G) [Fintype ↥I]
    (g : G)
    (h : ∀ v ∈ Representation.invariants (ρ.comp I.subtype),
      ρ g v ∈ Representation.invariants (ρ.comp I.subtype)) :
    LinearMap.trace K _ ((ρ g).restrict h) =
      (Fintype.card ↥I : K)⁻¹ * ∑ τ : ↥I, LinearMap.trace K V (ρ (g * τ)) := by
  classical
  haveI : Invertible (Fintype.card ↥I : K) :=
    invertibleOfNonzero (Nat.cast_ne_zero.2 Fintype.card_ne_zero)

  set W := Representation.invariants (ρ.comp I.subtype) with hW
  have hproj := Representation.isProj_averageMap (ρ.comp I.subtype)
  set e := Representation.averageMap (ρ.comp I.subtype) with he

  have key : LinearMap.trace K W ((ρ g).restrict h) = LinearMap.trace K V (ρ g ∘ₗ e) := by
    let e' : V →ₗ[K] W := e.codRestrict W hproj.map_mem
    have hfac : ρ g ∘ₗ e = W.subtype ∘ₗ (((ρ g).restrict h) ∘ₗ e') := by
      apply LinearMap.ext
      intro v
      rfl
    have hid : e' ∘ₗ W.subtype = LinearMap.id := by
      apply LinearMap.ext
      intro w
      apply Subtype.ext
      exact hproj.map_id w w.2
    rw [hfac, LinearMap.trace_comp_comm', LinearMap.comp_assoc, hid, LinearMap.comp_id]
  rw [key, he, Representation.averageMap, GroupAlgebra.average, map_smul, map_sum]
  simp only [Representation.asAlgebraHom_of, LinearMap.comp_smul, map_smul, smul_eq_mul, invOf_eq_inv]
  congr 1
  change (LinearMap.trace K V) (ρ g * ∑ x : ↥I, (ρ.comp I.subtype) x) = _
  rw [Finset.mul_sum, map_sum]
  refine Finset.sum_congr rfl fun τ _ => ?_
  change (LinearMap.trace K V) (ρ g * ρ (τ : G)) = _
  rw [← map_mul]

end S_ArtinL_trace_restrict_invariants_eq_inv_card_mul_sum_trace
end P2MW
export P2MW.S_ArtinL_trace_restrict_invariants_eq_inv_card_mul_sum_trace (solution)
