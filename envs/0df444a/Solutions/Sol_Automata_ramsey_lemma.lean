-- Prove2me | solution 1 for Automata.ramsey_lemma
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T04:51:08.107731+00:00
-- url     : https://prove2.me/submissions/70b14ab8-b51b-46aa-afe5-65e9192fe281

import Definitions.Def_AutomataTheory_Languages_RegLang
import Definitions.Def_AutomataTheory_Mathlib_InfGraphRamsey
import Definitions.Def_AutomataTheory_Languages_ChouekaLemma
import Theorems.Thm_inf_graph_ramsey
import Theorems.Thm_infinite_strict_mono
import Theorems.Thm_strict_mono_infinite


set_option autoImplicit true
open Function Set Filter Stream'
open scoped Computability
open Classical
attribute [local implicit_reducible] Stream'
open Automata
attribute [local instance_reducible] DA.toNA
variable {A : Type}
namespace Automata
theorem _root_.solution {C : Type} {cs : Set C} {φ : ℕ → ℕ} {col : ℕ → ℕ → C}
    (h_fin : cs.Finite) (h_mono : StrictMono φ) (h_col : ∀ i j, i < j → col (φ i) (φ j) ∈ cs) :
    ∃ c ∈ cs, ∃ σ : ℕ → ℕ, StrictMono σ ∧ ∀ i j, i < j → col (φ (σ i)) (φ (σ j)) = c := by
  let Vertex := ↑(Set.range φ)
  have : Infinite Vertex := by refine Infinite.to_subtype (strict_mono_infinite h_mono)
  let Color := {c // c ∈ cs}
  have : Finite Color := by exact h_fin
  have φ' := Equiv.ofInjective φ <| StrictMono.injective h_mono
  let color (e : Finset Vertex) : Color :=
    let ns := e.image φ'.invFun
    if h_2 : ns.card = 2 then
      have h_ne : ns.Nonempty := by apply Finset.card_ne_zero.mp ; simp +instances [h_2]
      ⟨col (φ (ns.min' h_ne)) (φ (ns.max' h_ne)), by
        obtain ⟨x, y, h_xy, h_ns⟩ := Finset.card_eq_two.mp h_2
        simp +instances [h_ns, h_col (min x y) (max x y) (by simp +instances [h_xy.symm])]⟩
    else ⟨col (φ 0) (φ 1), by exact h_col 0 1 (by omega)⟩
  obtain ⟨c, vs, h_inf_vs, h_col_vs⟩ := inf_graph_ramsey color
  use ↑c ; constructor
  · exact Subtype.coe_prop c
  let ns := φ' ⁻¹' vs
  have h_inf_ns : ns.Infinite := by
    apply Infinite.preimage h_inf_vs
    exact subset_range_of_surjective φ'.surjective vs
  obtain ⟨σ, h_mono_σ, h_ns⟩ := infinite_strict_mono h_inf_ns
  use σ ; simp +instances [h_mono_σ] ; intro i j h_ij
  obtain ⟨rfl⟩ := h_col_vs {φ' (σ i), φ' (σ j)} (by
    apply Finset.card_pair ; by_contra h_contra
    have := StrictMono.injective h_mono_σ <| φ'.injective h_contra ; omega
  ) (by
    simp +instances [insert_subset_iff] ; constructor
    · have h_i : σ i ∈ ns := by simp +instances [← h_ns]
      unfold ns at h_i ; rwa [← mem_preimage]
    · have h_j : σ j ∈ ns := by simp +instances [← h_ns]
      unfold ns at h_j ; rwa [← mem_preimage])
  have h_2 : Finset.card {σ i, σ j} = 2 := by
    apply Finset.card_pair ; by_contra h_contra
    have := StrictMono.injective h_mono_σ h_contra ; omega
  have h_ij_σ := h_mono_σ h_ij
  simp +instances [color, h_2, min_eq_left_of_lt h_ij_σ, max_eq_right_of_lt h_ij_σ]
end Automata
