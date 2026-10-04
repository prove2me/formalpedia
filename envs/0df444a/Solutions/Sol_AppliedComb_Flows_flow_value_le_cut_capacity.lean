-- Prove2me | solution 1 for AppliedComb.Flows.flow_value_le_cut_capacity
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-02T15:37:12.332345+00:00
-- url     : https://prove2.me/submissions/45db7705-3da3-4761-ad4e-5df303c11920

import Mathlib
import Definitions.Def_AppliedComb_Flows_Network

set_option autoImplicit false

open AppliedComb.Flows in
theorem e81308d1_value_eq {V : Type*} [Fintype V] [DecidableEq V]
    (N : Network V) (ϕ : V → V → ℝ) (hϕ : N.IsFlow ϕ) (L : Finset V) (hL : N.IsCut L) :
    N.value ϕ = ∑ y ∈ L, ((∑ x, ϕ y x) - ∑ x, ϕ x y) := by
  obtain ⟨_, hz, _, hc⟩ := hϕ
  obtain ⟨hS, hT⟩ := hL
  rw [Finset.sum_eq_single_of_mem N.S hS]
  · have : ∑ x, ϕ x N.S = 0 :=
      Finset.sum_eq_zero (fun x _ => hz x N.S (N.no_edge_into_source x))
    simp [Network.value, this]
  · intro y hy hyS
    have hyT : y ≠ N.T := fun h => hT (h ▸ hy)
    rw [hc y hyS hyT]; ring

open AppliedComb.Flows in
theorem solution {V : Type*} [Fintype V] [DecidableEq V]
    (N : Network V) (ϕ : V → V → ℝ) (hϕ : N.IsFlow ϕ) (L : Finset V) (hL : N.IsCut L) :
    N.value ϕ ≤ N.cutCapacity L := by
  rw [e81308d1_value_eq N ϕ hϕ L hL]
  obtain ⟨hb, hz, _, _⟩ := hϕ
  have hnn : ∀ x y, 0 ≤ ϕ x y := by
    intro x y
    by_cases h : N.adj x y
    · exact (hb x y h).1
    · rw [hz x y h]
  have hsplit : ∀ f : V → ℝ, ∑ x, f x = ∑ x ∈ L, f x + ∑ x ∈ Lᶜ, f x :=
    fun f => (Finset.sum_add_sum_compl L f).symm
  rw [Finset.sum_sub_distrib]
  simp_rw [hsplit (ϕ _), hsplit (fun x => ϕ x _)]
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib]
  have hcomm : ∑ y ∈ L, ∑ x ∈ L, ϕ x y = ∑ y ∈ L, ∑ x ∈ L, ϕ y x := Finset.sum_comm
  rw [hcomm]
  have h1 : 0 ≤ ∑ y ∈ L, ∑ x ∈ Lᶜ, ϕ x y :=
    Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => hnn _ _
  have h2 : ∑ y ∈ L, ∑ x ∈ Lᶜ, ϕ y x ≤ N.cutCapacity L := by
    unfold Network.cutCapacity
    apply Finset.sum_le_sum; intro y _
    apply Finset.sum_le_sum; intro x _
    by_cases h : N.adj y x
    · rw [if_pos h]; exact (hb y x h).2
    · rw [if_neg h, hz y x h]
  linarith
