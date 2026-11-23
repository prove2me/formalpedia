-- Prove2me | solution 1 for Automata.acc_omega_lang_concat
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T04:35:22.25992+00:00
-- url     : https://prove2.me/submissions/3416eb26-cf50-415b-b65c-f809960a529e

import Definitions.Def_AutomataTheory_Languages_Basic
import Definitions.Def_AutomataTheory_Automata_Basic
import Definitions.Def_AutomataTheory_Automata_Concat
import Theorems.Thm_Automata_na_concat_inf_run
import Theorems.Thm_P2M_Stream__append_extract_drop_29d8f2c46a9f
import Theorems.Thm_P2M_Stream__get_append_left__364c5eb8ed49
import Theorems.Thm_P2M_Stream__get_extract__ebf059d6908b


set_option autoImplicit true
open Function Set Filter Sum Stream'
open Classical
open Automata
variable {A : Type} {M0 M1 : NA A} {acc0 : Set M0.State} {acc1 : Set M1.State}
namespace Automata
theorem _root_.solution :
    (M0.Concat acc0 M1).AcceptedOmegaLang (inr '' acc1) =
    (M0.AcceptedLang acc0) * (M1.AcceptedOmegaLang acc1) := by
  ext as ; constructor
  · rintro ⟨ss, h_run, h_acc⟩
    obtain ⟨n, s1, h_s1_acc, h_s1⟩ := Frequently.exists h_acc
    have h_s1_ex : ∃ n s1, ss n = inr s1 := by use n, s1 ; simp +instances [h_s1]
    obtain ⟨n, ⟨ss0, h_run0, h_acc0, h_ss0⟩, ⟨ss1, h_run1, h_ss1⟩⟩ := na_concat_inf_run.mp ⟨h_run, h_s1_ex⟩
    use (as.extract 0 n), (as.drop n) ; simp +instances [append_extract_drop] ; constructor
    · use n, as ; constructor
      · use ss0
      · rfl
    · use ss1 ; simp +instances [h_run1]
      have h_ss1_ev : ∀ᶠ k in atTop, ss k = inr (ss1 (k - n)) := by
        simp +instances only [eventually_atTop] ; use (n + 1)
      have h_ss1_acc := Frequently.and_eventually h_acc h_ss1_ev
      simp +instances [frequently_atTop] at h_ss1_acc ⊢
      intro k ; obtain ⟨j, h_j, ⟨t1, h_t1_acc, h_t1⟩, h_j_ss1⟩ := h_ss1_acc (n + k)
      use (j - n) ; rw [← h_t1] at h_j_ss1
      have h_j_ss1 := Sum.inr.inj h_j_ss1
      simpa +instances [(by omega : k ≤ j - n), ← h_j_ss1]
  · rintro ⟨al0, as1, ⟨n, as0, ⟨ss0, ⟨h_init0, h_next0⟩, h_acc0⟩, rfl⟩, ⟨ss1, h_run1, h_acc1⟩, h_as⟩
    let ss := fun k ↦ if k < n + 1 then inl (ss0 k) else inr (ss1 (k - n))
    use ss  ; constructor
    · suffices (M0.Concat acc0 M1).InfRun as ss ∧ (∃ n s1, ss n = inr s1) by tauto
      apply na_concat_inf_run.mpr
      use n ; constructor
      · refine ⟨ss0, ⟨h_init0, ?_⟩, h_acc0, ?_⟩
        · intro k h_k
          have h1 : k < (as0.extract 0 n).length := by simp +instances [length_extract, h_k]
          simpa +instances (disch := omega) [← h_as, get_append_left' h1, get_extract'] using h_next0 k h_k
        · intro k h_k
          simp only [ss, if_pos h_k] <;> rfl
      · refine ⟨ss1, ?_, ?_⟩
        · have h1 : (as0.extract 0 n).length = n := by simp +instances [length_extract]
          rw [← h1]
          simpa +instances [← h_as, drop_append_stream] using h_run1
        · intro k hk
          exact if_neg (by omega : ¬ k < n + 1)
    · have h_ss1_ev : ∀ᶠ k in atTop, ss (k + n) = inr (ss1 k) := by
        simp +instances only [eventually_atTop]
        use (n + 1) ; intro k h_k ; simp +instances [ss] ; omega
      have h_ss1_acc := Frequently.and_eventually h_acc1 h_ss1_ev
      simp +instances [frequently_atTop] at h_ss1_acc ⊢
      intro k ; obtain ⟨j, h_j, h_j_acc, h_j_ss1⟩ := h_ss1_acc (n + k)
      use (j + n) ; simp +instances [(by omega : k ≤ j + n)]
      use (ss1 j) ; simp +instances [h_j_acc, h_j_ss1] <;> rfl
end Automata
