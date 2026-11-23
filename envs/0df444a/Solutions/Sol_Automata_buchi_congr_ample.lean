-- Prove2me | solution 1 for Automata.buchi_congr_ample
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T04:51:37.737803+00:00
-- url     : https://prove2.me/submissions/e4b8a43f-0fa8-4589-b8d1-df6a58e1155f

import Definitions.Def_AutomataTheory_Automata_Pair
import Definitions.Def_AutomataTheory_Mathlib_InfGraphRamsey
import Definitions.Def_AutomataTheory_Congruences_BuchiCongr
import Theorems.Thm_Automata_buchi_congr_finite_index
import Theorems.Thm_Automata_strict_mono_of_infinite
import Theorems.Thm_P2M_Stream__append_extract_drop_29d8f2c46a9f
import Theorems.Thm_P2M_Stream__extract_drop_9b771096fa3e
import Theorems.Thm_base_zero_strict_mono
import Theorems.Thm_inf_graph_ramsey


set_option autoImplicit true
open Function Set Filter Stream'
open Automata
attribute [local instance_reducible] NA.BuchiCongr
open Classical
variable {A : Type}
variable {M : NA A} {acc : Set M.State}
namespace Automata
theorem _root_.solution [Finite M.State] : (M.BuchiCongr acc).Ample := by
  intro as
  have : Finite (M.BuchiCongr acc).QuotType := buchi_congr_finite_index
  let color (t : Finset ℕ) : (M.BuchiCongr acc).QuotType :=
    if h : t.Nonempty then ⟦ as.extract (t.min' h) (t.max' h) ⟧ else ⟦ [] ⟧
  obtain ⟨q, ns, h_ns, h_color⟩ := inf_graph_ramsey color
  obtain ⟨φ, h_mono, rfl⟩ := strict_mono_of_infinite h_ns
  let p : (M.BuchiCongr acc).QuotType := ⟦ as.extract 0 (φ 0) ⟧
  use p, q, (as.extract 0 (φ 0)), (as.drop (φ 0)) ; constructorm* _ ∧ _
  · simp +instances [Congruence.EqvCls, p]
    rfl
  · use (φ · - φ 0) ; simp [base_zero_strict_mono h_mono]
    intro m
    have := StrictMono.monotone h_mono (show 0 ≤ m by omega)
    have := StrictMono.monotone h_mono (show 0 ≤ m + 1 by omega)
    simp [extract_drop, (show φ 0 + (φ m - φ 0) = φ m by omega),
      (show φ 0 + (φ (m + 1) - φ 0) = φ (m + 1) by omega)]
    have h_card2 : Finset.card {φ m, φ (m + 1)} = 2 := by
      apply Finset.card_pair
      have := h_mono (show m < m + 1 by omega)
      omega
    have h_ne2 : Finset.Nonempty {φ m, φ (m + 1)} := by apply Finset.card_pos.mp ; omega
    have := h_mono (show m < m + 1 by omega)
    have h_min : Finset.min' {φ m, φ (m + 1)} h_ne2 = φ m := by simp ; omega
    have h_max : Finset.max' {φ m, φ (m + 1)} h_ne2 = φ (m + 1) := by simp ; omega
    have h_color := h_color {φ m, φ (m + 1)} h_card2 (by intro x ; simp ; grind)
    simp [color, h_min, h_max] at h_color
    simp +instances [Congruence.EqvCls, h_color]
    rfl
  · simp [append_extract_drop]
end Automata
