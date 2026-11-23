-- Prove2me | solution 1 for Automata.na_loop_fin_run
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T04:19:34.147836+00:00
-- url     : https://prove2.me/submissions/05a9c552-7657-4d97-9da9-030f5aaeb3c5

import Definitions.Def_AutomataTheory_Automata_Basic
import Definitions.Def_AutomataTheory_Languages_Basic
import Definitions.Def_AutomataTheory_Sequences_Segments
import Definitions.Def_AutomataTheory_Automata_Loop
section
open Function Set Sum Filter Stream'
open Classical
open scoped Computability
attribute [local instance_reducible] Stream'
namespace Automata
@[simp] private theorem loop_drop_apply {α : Type*} (s : Stream' α) (n k : ℕ) :
    (s.drop n) k = s (n + k) := by simp [Stream'.drop, Stream'.get, Nat.add_comm]
section AutomataLoop
variable {A : Type}
attribute [local instance_reducible] NA.Loop
variable {M : NA A} {acc : Set M.State}
end AutomataLoop
attribute [local instance_reducible] NA.Loop
section AcceptedLangLoop
variable {A : Type} {M : NA A} {acc : Set M.State}
end AcceptedLangLoop
end Automata
end

set_option autoImplicit true
open Function Set Sum Filter Stream'
open Classical
open scoped Computability
attribute [local instance_reducible] Stream'
open Automata
variable {A : Type}
attribute [local instance_reducible] NA.Loop
variable {M : NA A} {acc : Set M.State}
namespace Automata
theorem _root_.solution {n : ℕ} {as : Stream' A} {ss : Stream' (M.Loop acc).State} (h : n > 0) :
    (M.Loop acc).FinRun n as ss ∧ ss n = inl () ∧ (∀ k < n, k > 0 → ss k ∈ range inr) ↔
    ∃ ss', M.FinRun n as ss' ∧ ss' n ∈ acc ∧ ss 0 = inl () ∧ ss n = inl () ∧ (∀ k < n, k > 0 → ss k = inr (ss' k)) := by
  constructor
  · rintro ⟨⟨h_init, h_next⟩, h_inl_n, h_inr⟩
    simp +instances [NA.Loop] at h_init
    rcases (show n = 1 ∨ n > 1 by omega) with h_n | h_n
    · obtain ⟨rfl⟩ := h_n
      specialize h_next 0 (by omega)
      simp +instances [h_init, h_inl_n, NA.Loop] at h_next
      obtain ⟨s0, h_s0, s1, h_acc, h_next⟩ := h_next
      use (fun k ↦ if k = 0 then s0 else if k = 1 then s1 else s0)
      simp +instances [h_init, h_acc, h_inl_n, NA.FinRun, h_s0, h_next]
    · obtain ⟨s1, h_s1⟩ := h_inr 1 h_n (by omega)
      have h_next_0 := h_next 0 h
      simp +instances [h_init, ← h_s1, NA.Loop] at h_next_0
      obtain ⟨s0, h_s0, h_next_0⟩ := h_next_0
      obtain ⟨sn1, h_sn1⟩ := h_inr (n - 1) (by omega) (by omega)
      have h_next_n1 := h_next (n - 1) (by omega)
      have h_n1 : n - 1 + 1 = n := by omega
      simp +instances [h_n1, h_inl_n, ← h_sn1, NA.Loop] at h_next_n1
      obtain ⟨sn, h_sn, h_next_n1⟩ := h_next_n1
      have h_ss' : ∀ k, k > 0 → k < n → ∃ ss', ss k = inr ss' := by
        intro k h_k_0 h_k_n
        obtain ⟨s', h_s'⟩ := h_inr k h_k_n h_k_0
        use s' ; simp +instances [h_s']
      choose ss' h_ss' using h_ss'
      use (fun k ↦ if h0 : k = 0 then s0 else if hn : k < n then ss' k (by omega) hn else if k = n then sn else s0)
      simp +instances [(show n ≠ 0 by omega), h_init, h_inl_n, h_sn, NA.FinRun, h_s0]
      constructor
      · intro k h_k_n
        rcases (show k = 0 ∨ k = n - 1 ∨ k > 0 ∧ k < n - 1 by omega) with h_k_0 | h_k_n' | ⟨h_k_0, h_k_n'⟩
        · obtain ⟨rfl⟩ := h_k_0
          have h_ss_1 := h_ss' 1 (by omega) (h_n)
          rw [← h_s1, inr.inj_iff] at h_ss_1
          simp +instances [h_n, ← h_ss_1, h_next_0]
        · obtain ⟨rfl⟩ := h_k_n'
          have h_ss_n1 := h_ss' (n - 1) (by omega) h_k_n
          rw [← h_sn1, inr.inj_iff] at h_ss_n1
          simp +instances [(show n - 1 + 1 = n by omega), (show n - 1 ≠ 0 by omega), h, ← h_ss_n1, h_next_n1]
        · have h_ss_k := h_ss' k h_k_0 h_k_n
          have h_ss_k1 := h_ss' (k + 1) (by omega) (by omega)
          have h_next_k := h_next k h_k_n
          simp +instances [h_ss_k, h_ss_k1, NA.Loop] at h_next_k
          simp +instances [(show k + 1 < n by omega), (show k ≠ 0 by omega), h_k_n, h_next_k]
      · intro k h_k_n h_k_0
        simp +instances [h_k_n, h_k_0, (show k ≠ 0 by omega), h_ss']
  · rintro ⟨ss', ⟨h_init, h_next⟩, h_acc, h_inl_0, h_inl_n, h_inr⟩
    constructor <;> [constructor ; constructor]
    · simp +instances [h_inl_0, NA.Loop]
    · intro k h_k_n
      rcases (show k = 0 ∨ k > 0 by omega) with h_k_0 | h_k_0
      · specialize h_next 0 h
        rcases (show n = 1 ∨ n > 1 by omega) with h_n | h_n
        · obtain ⟨rfl⟩ := h_n
          simp +instances [h_k_0, h_inl_0, NA.Loop, h_inl_n]
          use (ss' 0) ; simp +instances [h_init] ; use (ss' 1)
        · specialize h_inr 1 h_n (by omega)
          simp +instances [h_k_0, h_inl_0, NA.Loop, h_inr]
          use (ss' 0)
      · specialize h_next k (h_k_n)
        have h_ss_k := h_inr k h_k_n h_k_0
        rcases (show k + 1 < n ∨ k = n - 1 by omega) with h_k_n' | h_k_n'
        · have h_ss_k' := h_inr (k + 1) h_k_n' (by omega)
          simpa +instances [h_ss_k, h_ss_k', NA.Loop]
        · obtain ⟨rfl⟩ := h_k_n'
          have h_n1 : n - 1 + 1 = n := by omega
          simp +instances [h_n1] at h_next
          simp +instances [h_n1, h_ss_k, h_inl_n, NA.Loop]
          use (ss' n)
    · exact h_inl_n
    · intro k h_k_n h_k_0
      simp +instances [h_inr k h_k_n h_k_0]
end Automata
