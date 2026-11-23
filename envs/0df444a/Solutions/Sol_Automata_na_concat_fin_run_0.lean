-- Prove2me | solution 1 for Automata.na_concat_fin_run_0
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T04:34:20.989362+00:00
-- url     : https://prove2.me/submissions/eeff5e46-c183-4a2a-86c0-c5af5a537bcc

import Definitions.Def_AutomataTheory_Languages_Basic
import Definitions.Def_AutomataTheory_Automata_Basic
import Definitions.Def_AutomataTheory_Automata_Concat
section
open Function Set Filter Sum Stream'
open Classical
namespace Automata
section AutomataConcat
variable {A : Type}
attribute [local instance_reducible] NA.Concat
variable {M0 M1 : NA A} {acc0 : Set M0.State}
private lemma not_M0_state {s : (M0.Concat acc0 M1).State}
    (h : ¬ ∃ s0, s = inl s0) : ∃ s1, s = inr s1 := by
  rw [← isLeft_iff, not_isLeft] at h
  simpa +instances [← isRight_iff]
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
    (M0.Concat acc0 M1).FinRun m as ss ∧ (∃ s0, ss m = inl s0) ↔
    (∃ ss0, M0.FinRun m as ss0 ∧ ∀ k < m + 1, ss k = inl (ss0 k)) := by
  constructor
  · rintro ⟨⟨h_init, h_next⟩, ⟨s0_m, h_s0_m⟩⟩
    have h_all0 : ∀ k < m + 1, ∃ s0, ss k = inl s0 := by
      by_contra h_contra
      simp +instances only [not_forall] at h_contra
      obtain ⟨n, h_n, h_ss_n⟩ := h_contra
      obtain ⟨s1, h_ss_n⟩ := not_M0_state h_ss_n
      have h_contra : ∀ k < m - n + 1, ∃ s1, ss (k + n) = inr s1 := by
        intro k h_k ; induction' k with k k_ind
        · use s1 ; simpa +instances
        obtain ⟨s1', h_s1'⟩ := k_ind (by omega)
        have h_next_k := h_next (k + n) (by omega)
        simp +instances [h_s1', NA.Concat] at h_next_k
        obtain ⟨s1'', _, h_s1''⟩ := h_next_k
        use s1'' ; rw [h_s1''] ; congr 1 ; omega
      obtain ⟨s1_m, h_s1_m⟩ := h_contra (m - n) (by omega)
      simp +instances [(by omega: m - n + n = m), h_s0_m] at h_s1_m
    choose ss0 h_ss0 using h_all0
    use (fun k ↦ if h : k < m + 1 then ss0 k h else s0_m)
    constructor <;> [constructor ; skip]
    · simp +instances [h_ss0 0 (by omega), NA.Concat] at h_init
      simpa +instances
    · intro k h_k
      have h_next_k := h_next k h_k
      simp +instances [h_ss0 k (by omega), h_ss0 (k + 1) (by omega), NA.Concat] at h_next_k
      simpa +instances [h_k, (by omega : k < m + 1)]
    · intro k h_k ; simp +instances [h_k, h_ss0 k h_k]
  · rintro ⟨ss0, ⟨h_init0, h_next0⟩, h_ss0⟩
    constructor <;> [constructor ; skip]
    · simpa +instances [h_ss0 0 (by omega), NA.Concat]
    · intro k h_k
      simp +instances [h_ss0 k (by omega), h_ss0 (k + 1) (by omega), NA.Concat]
      exact h_next0 k h_k
    · use (ss0 m) ; exact h_ss0 m (by omega)
end Automata
