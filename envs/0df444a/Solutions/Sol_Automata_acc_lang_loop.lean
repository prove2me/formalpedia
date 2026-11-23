-- Prove2me | solution 1 for Automata.acc_lang_loop
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T04:42:52.178961+00:00
-- url     : https://prove2.me/submissions/0422ee3e-3b0b-4c19-b8d9-f02505d45a96

import Definitions.Def_AutomataTheory_Automata_Basic
import Definitions.Def_AutomataTheory_Languages_Basic
import Definitions.Def_AutomataTheory_Sequences_Segments
import Definitions.Def_AutomataTheory_Automata_Loop
import Theorems.Thm_Automata_na_loop_fin_run
import Theorems.Thm_Automata_na_loop_fin_run_exists
import Theorems.Thm_Automata_acc_lang_loop_concat
import Theorems.Thm_Automata_na_FinRun_imp_FinRun
import Theorems.Thm_P2M_Stream__append_extract_extract_2ca0e177dfc2
import Theorems.Thm_P2M_Stream__extract_drop_9b771096fa3e
import Theorems.Thm_P2M_Stream__extract_eq_nil_7f26d60de260
import Theorems.Thm_P2M_Stream__get_drop__05b839498f63
import Theorems.Thm_epsilon_ConcatFin

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
private lemma not_inl_unit {s : (M.Loop acc).State} :
    s ≠ inl () ↔ ∃ s' : M.State, s = inr s' := by
  constructor
  · rw [← isRight_iff, ← not_isLeft, isLeft_iff]
    rintro h1 ⟨u, h_s⟩
    have h_u := Unit.ext u ()
    simp +instances [h_s] at h1
  · rintro ⟨s', h_s'⟩ ; simp +instances [h_s']
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
attribute [local instance_reducible] NA.Loop
variable {A : Type} {M : NA A} {acc : Set M.State}
namespace Automata
theorem _root_.solution [Inhabited A] :
    (M.Loop acc).AcceptedLang {inl ()} = (M.AcceptedLang acc)∗ := by
  ext al ; constructor
  · rintro ⟨n, as, ⟨ss, h_run, h_acc⟩, h_al⟩ ; simp +instances [instIterStar, IterStar]
    revert al
    induction' n using Nat.strong_induction_on with n h_ind
    intro al h_al
    let loop k := 0 < k ∧ k < n ∧ ss k = inl ()
    rcases Classical.em (∃ k, loop k) with h_loop | h_loop
    · let m := Nat.findGreatest loop n
      have h_m : loop m := by
        obtain ⟨k, h_loop⟩ := h_loop
        apply Nat.findGreatest_spec (m := k) (by omega) h_loop
      obtain ⟨h_m_0, h_m_n, h_m_inl⟩ := h_m
      let al' := as.extract 0 m
      have h_run' := na_FinRun_imp_FinRun h_m_n h_run
      obtain ⟨j, h_j⟩ := h_ind m h_m_n h_run' (by simp +instances [h_m_inl]) (al') (by simp +instances [al'])
      have h_d : n - m > 0 := by omega
      have h_run'' : (M.Loop acc).FinRun (n - m) (as.drop m) (ss.drop m) := by
        constructor
        · simp +instances [NA.Loop, get_drop', h_m_inl]
        intro k h_k
        have h_next := h_run.2 (k + m) (by omega)
        simp +instances [h_next, get_drop', (show m + (k + 1) = k + m + 1 by omega), (show m + k = k + m by omega)]
      have h_inl'' : (ss.drop m) (n - m) = inl () := by
        simp at h_acc
        simp +instances [get_drop', (show m + (n - m) = n by omega), h_acc]
      have h_inr'' : ∀ k < n - m, k > 0 → (ss.drop m) k ∈ range inr := by
        intro k h_k_d h_k_0
        have h_not_loop : ¬ loop (k + m) := by
          exact Nat.findGreatest_is_greatest (show m < k + m by omega) (by omega)
        simp +instances [loop, -add_pos_iff] at h_not_loop
        obtain ⟨s', h_s'⟩ := not_inl_unit.mp <| h_not_loop (by omega) (by omega)
        simp +instances [get_drop'] ; use s' ; rw [add_comm] ; simp +instances [h_s']
      obtain ⟨ss'', h_run'', h_acc'', _⟩ := (na_loop_fin_run h_d).mp ⟨h_run'', h_inl'', h_inr''⟩
      let al'' := as.extract m n
      use (j + 1) ; simp +instances [instIterFin, IterFin]
      use al', al'' ; constructorm* _ ∧ _
      · exact h_j
      · use (n - m), (as.drop m)
        simp +instances [al'', extract_drop, (show m + (n - m) = n by omega)]
        use ss''
      · simp (disch := omega) [← h_al, al', al'', append_extract_extract]
    · rcases (show n = 0 ∨ n > 0 by omega) with ⟨rfl⟩ | h_n
      · use 0 ; simp +instances [← h_al, instIterFin, IterFin, extract_eq_nil]
      simp +instances [loop] at h_loop
      have h_inr : ∀ k < n, k > 0 → ss k ∈ range inr := by
        intro k h_k_n h_k_0
        obtain ⟨s', h_s'⟩ := not_inl_unit.mp <| h_loop k h_k_0 h_k_n
        use s' ; simp +instances [h_s']
      simp at h_acc
      obtain ⟨ss', h_run', h_acc', _⟩ := (na_loop_fin_run h_n).mp ⟨h_run, h_acc, h_inr⟩
      use 1 ; simp +instances [instIterFin, IterFin, epsilon_ConcatFin]
      use n, as ; simp +instances [h_al]
      use ss'
  · rintro ⟨L, ⟨i, rfl⟩, h_al⟩ ; simp at h_al
    revert al
    induction' i with i h_ind
    · intro al ; simp +instances [instIterFin, IterFin] ; rintro ⟨rfl⟩
      use 0 ; simp +instances [extract_eq_nil]
      use (fun k ↦ default), (fun k ↦ inl ()) ; simp +instances [NA.FinRun, NA.Loop]
    rintro al ⟨al1, al2, h_al1, h_al2, h_al⟩
    specialize h_ind al1 h_al1
    suffices _ : al2 ∈ (M.Loop acc).AcceptedLang {inl ()} by
      apply acc_lang_loop_concat ; use al1, al2
    obtain ⟨n2, as2, ⟨ss2', h_run2, h_acc2⟩, h_al2⟩ := h_al2
    obtain ⟨ss2, h_run2, h_acc2, _⟩ := na_loop_fin_run_exists h_run2 h_acc2
    use n2, as2 ; simp +instances [h_al2]
    use ss2 ; simp +instances [h_run2, h_acc2]
end Automata
