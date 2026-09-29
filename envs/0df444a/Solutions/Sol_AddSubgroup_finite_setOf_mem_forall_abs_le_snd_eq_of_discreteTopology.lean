-- Prove2me | solution 1 for AddSubgroup.finite_setOf_mem_forall_abs_le_snd_eq_of_discreteTopology
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:01.734404+00:00
-- url     : https://prove2.me/submissions/2d13a9a9-b36f-5e30-aa39-62b8aeecd50b

import Mathlib
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AddSubgroup_finite_setOf_mem_forall_abs_le_snd_eq_of_discreteTopology

set_option autoImplicit false

theorem solution
    {r c : ℕ} (Λ : AddSubgroup ((Fin r → ℝ) × (Fin c → ℤ))) [DiscreteTopology Λ] (R : ℝ) (k₀ : Fin c → ℤ) :
    {γ : (Fin r → ℝ) × (Fin c → ℤ) | γ ∈ Λ ∧ (∀ i, |γ.1 i| ≤ R) ∧ γ.2 = k₀}.Finite := by
  have hcl : IsClosed (Λ : Set ((Fin r → ℝ) × (Fin c → ℤ))) := AddSubgroup.isClosed_of_discrete
  have hbox : IsCompact ({x : Fin r → ℝ | ∀ i, |x i| ≤ R} ×ˢ ({k₀} : Set (Fin c → ℤ))) := by
    refine IsCompact.prod ?_ isCompact_singleton
    have : {x : Fin r → ℝ | ∀ i, |x i| ≤ R} = Set.pi Set.univ fun _ => Set.Icc (-R) R := by
      ext x
      simp only [Set.mem_setOf_eq, Set.mem_pi, Set.mem_univ, Set.mem_Icc, forall_const, abs_le]
    rw [this]
    exact isCompact_univ_pi fun _ => isCompact_Icc
  have hK : IsCompact ((Λ : Set ((Fin r → ℝ) × (Fin c → ℤ))) ∩
      ({x : Fin r → ℝ | ∀ i, |x i| ≤ R} ×ˢ ({k₀} : Set (Fin c → ℤ)))) := hbox.inter_left hcl
  have hfin : ((Λ : Set ((Fin r → ℝ) × (Fin c → ℤ))) ∩
      ({x : Fin r → ℝ | ∀ i, |x i| ≤ R} ×ˢ ({k₀} : Set (Fin c → ℤ)))).Finite := by
    refine hK.finite ?_
    have : IsDiscrete (Λ : Set ((Fin r → ℝ) × (Fin c → ℤ))) :=
      isDiscrete_iff_discreteTopology.2 ‹DiscreteTopology Λ›
    exact this.mono Set.inter_subset_left
  refine hfin.subset ?_
  rintro γ ⟨hγ, hx, hk⟩
  exact ⟨hγ, hx, hk⟩

end S_AddSubgroup_finite_setOf_mem_forall_abs_le_snd_eq_of_discreteTopology
end P2MW
export P2MW.S_AddSubgroup_finite_setOf_mem_forall_abs_le_snd_eq_of_discreteTopology (solution)
