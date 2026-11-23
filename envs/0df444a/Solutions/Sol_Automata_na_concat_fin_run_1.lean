-- Prove2me | solution 1 for Automata.na_concat_fin_run_1
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T04:34:21.456606+00:00
-- url     : https://prove2.me/submissions/5ba29bb3-b12e-40c1-b56a-dd0da83431a4

import Definitions.Def_AutomataTheory_Languages_Basic
import Definitions.Def_AutomataTheory_Automata_Basic
import Definitions.Def_AutomataTheory_Automata_Concat
import Theorems.Thm_P2M_Stream__get_drop__05b839498f63

section
open Function Set Filter Sum Stream'
open Classical
namespace Automata
section AutomataConcat
variable {A : Type}
attribute [local instance_reducible] NA.Concat
variable {M0 M1 : NA A} {acc0 : Set M0.State}
private lemma not_M1_state {s : (M0.Concat acc0 M1).State}
    (h : ¬ ∃ s1, s = inr s1) : ∃ s0, s = inl s0 := by
  rw [← isRight_iff, not_isRight] at h
  simpa +instances [← isLeft_iff]
end AutomataConcat
section AcceptedLangConcat
variable {A : Type} {M0 M1 : NA A} {acc0 : Set M0.State} {acc1 : Set M1.State}
end AcceptedLangConcat
end Automata
end

set_option autoImplicit true
open Function Set Filter Sum Stream'
open Classical
open Automata
variable {A : Type}
attribute [local instance_reducible] NA.Concat
variable {M0 M1 : NA A} {acc0 : Set M0.State}
namespace Automata
theorem _root_.solution {m : ℕ} {as : Stream' A} {ss : Stream' (M0.Concat acc0 M1).State} :
    (M0.Concat acc0 M1).FinRun m as ss ∧ (∃ s1, ss m = inr s1) ↔
    ∃ n < m, (∃ ss0, M0.FinRun n as ss0 ∧ ss0 n ∈ acc0 ∧ ∀ k < n + 1, ss k = inl (ss0 k)) ∧
             (∃ ss1, M1.FinRun (m - n) (as.drop n) ss1 ∧ ∀ k ≥ n + 1, k < m + 1 → ss k = inr (ss1 (k - n))) := by
  constructor
  · rintro ⟨⟨⟨s0, h_s0_init, h_s0⟩, h_next⟩, h_sm⟩
    have h_n : ∃ n s1, ss n = inr s1 := by use m
    use (Nat.find h_n - 1)
    have h_n_pos : 0 < Nat.find h_n := by
      by_contra
      have h_n_0 : Nat.find h_n = 0 := by omega
      obtain ⟨s1, h_s1⟩ := Nat.find_spec h_n
      rw [h_n_0] at h_s1
      simp +instances [← h_s0] at h_s1
    have h_n_dec_inc := Nat.sub_one_add_one_eq_of_pos h_n_pos
    have h_ss0 : ∀ k < Nat.find h_n, ∃ s0, ss k = inl s0 := by
      intro k h_k ; exact not_M1_state (Nat.find_min h_n h_k)
    choose ss0 h_ss0 using h_ss0
    have h_n' : Nat.find h_n - 1 < Nat.find h_n := by omega
    have h_ss_n' := h_ss0 (Nat.find h_n - 1) h_n'
    obtain ⟨sn, h_ss_n⟩ := Nat.find_spec h_n
    have h_n_m := Nat.find_min' h_n h_sm
    have h_next_n := h_next (Nat.find h_n - 1) (by omega)
    simp +instances [h_ss_n', h_ss_n, h_n_dec_inc, NA.Concat] at h_next_n
    obtain ⟨h_n'_acc, ⟨sn1, h_sn1_init, h_sn1_next⟩⟩ := h_next_n
    simp +instances only [h_n_dec_inc]
    constructor <;> [skip ; constructor]
    . omega
    · use (fun k ↦ if h : k < Nat.find h_n then ss0 k h else s0)
      constructor <;> [constructor ; constructor]
      · have h_ss_0 := h_ss0 0 h_n_pos
        rw [← h_s0, inl.inj_iff] at h_ss_0
        simpa +instances [h_n_pos, ← h_ss_0]
      · intro k h_k
        have h_k0 : k < Nat.find h_n := by omega
        have h_k1 : k + 1 < Nat.find h_n := by omega
        have h_ss_k0 := h_ss0 k h_k0
        have h_ss_k1 := h_ss0 (k + 1) h_k1
        have h_next_k := h_next k (by omega)
        simp +instances [h_ss_k0, h_ss_k1, NA.Concat] at h_next_k
        simpa +instances [h_k0, h_k1]
      · simpa +instances [h_n']
      · intro k h_k ; simp +instances [h_k, h_ss0 k h_k]
    · have h_ss1 : ∀ k < m - Nat.find h_n + 1, ∃ s1, ss (k + Nat.find h_n) = inr s1 := by
        intro k h_k ; induction' k with k k_ind
        · use sn ; simpa +instances
        obtain ⟨sk, h_sk⟩ := k_ind (by omega)
        have h_next_k := h_next (k + Nat.find h_n) (by omega)
        simp +instances [h_sk, NA.Concat] at h_next_k
        rcases h_next_k with ⟨sk1, _, h_sk1⟩
        use sk1 ; rw [h_sk1] ; congr 1 ; omega
      choose ss1 h_ss1 using h_ss1
      use (fun k ↦ if k = 0 then sn1 else if h : k < m - Nat.find h_n + 2 then ss1 (k - 1) (by omega) else sn1)
      constructor <;> [constructor ; skip]
      · simpa +instances
      · intro k h_k_m
        rcases (by omega : k = 0 ∨ k ≠ 0) with h_k | h_k
        · have h_ss_n'' := h_ss1 0
          simp +instances [h_ss_n] at h_ss_n''
          rw [inr.inj_iff] at h_ss_n''
          simpa +instances [get_drop', h_k, ← h_ss_n'']
        · have h_k0 : k - 1 + Nat.find h_n + 1 = k + Nat.find h_n := by omega
          have h_next_k := h_next (k - 1 + Nat.find h_n) (by omega)
          simp +instances [NA.Concat, h_k0, h_ss1 (k - 1) (by omega)] at h_next_k
          obtain ⟨sk1, h_sk1_next, h_sk1⟩ := h_next_k
          have h_k1 : k < m - Nat.find h_n + 1 := by omega
          have h_k2 : k < m - Nat.find h_n + 2 := by omega
          have h_k3 : (Nat.find h_n - 1) + k = (k - 1) + Nat.find h_n := by omega
          rw [h_ss1 k (by omega), inr.inj_iff] at h_sk1
          simpa +instances [get_drop', h_k, h_k1, h_k2, h_k3, ← h_sk1]
      · intro k h_k h_k_m
        have h_k1 : k - (Nat.find h_n - 1) ≠ 0 := by omega
        have h_k2 : (k - (Nat.find h_n - 1) - 1) = k - Nat.find h_n := by omega
        have h_k3 : k - (Nat.find h_n - 1) < m - Nat.find h_n + 2 := by omega
        simp +instances [h_k1, h_k2, h_k3, ← h_ss1 (k - Nat.find h_n)]
        congr ; omega
  · rintro ⟨n, h_n, ⟨ss0, ⟨h_init0, h_next0⟩, h_acc0, h_ss0⟩, ⟨ss1, ⟨h_init1, h_next1⟩, h_ss1⟩⟩
    constructor <;> [constructor ; skip]
    · simpa +instances [h_ss0 0 (by omega), NA.Concat]
    · intro k h_k'
      rcases (by omega : k < n ∨ k = n ∨ k > n) with h_k | h_k | h_k
      · have h_next_k := h_next0 k h_k
        simpa +instances [h_ss0 k (by omega), h_ss0 (k + 1) (by omega), NA.Concat]
      · obtain ⟨rfl⟩ := h_k
        have h_next_k := h_next1 0 (by omega)
        simp +instances [get_drop'] at h_next_k
        simp +instances [h_ss0 n (by omega), h_ss1 (n + 1) (by omega) (by omega), NA.Concat, h_acc0]
        use (ss1 0)
      · have h_next_k := h_next1 (k - n) (by omega)
        simp +instances [get_drop', (by omega : n + (k - n) = k), (by omega : k - n + 1 = k + 1 - n)] at h_next_k
        simpa +instances [h_ss1 k (by omega) (by omega), h_ss1 (k + 1) (by omega) (by omega), NA.Concat]
    . have := h_ss1 m (by omega) (by omega)
      use (ss1 (m - n))
end Automata
