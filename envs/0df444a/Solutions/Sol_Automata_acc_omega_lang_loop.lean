-- Prove2me | solution 1 for Automata.acc_omega_lang_loop
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T04:41:26.190662+00:00
-- url     : https://prove2.me/submissions/1a0f3b96-2797-482b-891a-69bd4394c4c6

import Definitions.Def_AutomataTheory_Automata_Basic
import Definitions.Def_AutomataTheory_Languages_Basic
import Definitions.Def_AutomataTheory_Sequences_Segments
import Definitions.Def_AutomataTheory_Automata_Loop
import Theorems.Thm_Automata_na_loop_fin_run
import Theorems.Thm_Automata_na_FinRun_modulo
import Theorems.Thm_P2M_Stream__extract_drop_9b771096fa3e
import Theorems.Thm_P2M_Stream__extract_eq_extract_14275bcbb551
import Theorems.Thm_P2M_Stream__get_drop__05b839498f63
import Theorems.Thm_nth_succ_gap
import Theorems.Thm_segment_lower_bound
import Theorems.Thm_segment_range_gap
import Theorems.Thm_segment_range_val
import Theorems.Thm_segment_upper_bound
import Theorems.Thm_strict_mono_infinite

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
theorem _root_.solution :
    (M.Loop acc).AcceptedOmegaLang {inl ()} = (M.AcceptedLang acc)^ω := by
  ext as ; constructor
  · rintro ⟨ss, h_run, h_acc⟩ ; simp at h_acc
    let φ m := Nat.nth (fun k ↦ ss k = inl ()) m
    have h_inf : {k | ss k = inl ()}.Infinite := by simpa +instances [← Nat.frequently_atTop_iff_infinite]
    have h_mono : StrictMono φ := by exact Nat.nth_strictMono h_inf
    use φ ; simp +instances [h_mono] ; constructor
    · have h_init := h_run.1
      simp +instances [NA.Loop] at h_init
      apply Nat.nth_zero_of_zero h_init
    · intro m
      use (φ (m + 1) - φ m), (as.drop (φ m)) ; constructor
      · have h_mono_m : φ (m + 1) - φ m > 0 := by have := h_mono (show m < m + 1 by omega) ; omega
        let ss1 := ss.drop (φ m)
        have h_run1 : (M.Loop acc).FinRun (φ (m + 1) - φ m) (as.drop (φ m)) ss1 := by
          constructor
          · simp +instances [ss1, get_drop', NA.Loop]
            apply Nat.nth_mem_of_infinite (p := fun k ↦ ss k = inl ()) h_inf
          intro k h_k
          simp +instances [ss1, get_drop', ← add_assoc, h_run.2 (φ m + k)]
        have h_inl : ss1 (φ (m + 1) - φ m) = inl () := by
          simp +instances [ss1, get_drop', (show φ m + (φ (m + 1) - φ m) = φ (m + 1) by omega)]
          apply Nat.nth_mem_of_infinite (p := fun k ↦ ss k = inl ()) h_inf
        have h_inr : ∀ k < φ (m + 1) - φ m, k > 0 → ss1 k ∈ range inr := by
          intro k h_k1 h_k0
          obtain ⟨s', h_s'⟩ := not_inl_unit.mp <| nth_succ_gap h_inf m k h_k1 h_k0
          use s' ; rw [add_comm] at h_s'
          simp +instances [φ, ss1, ← h_s', get_drop']
        obtain ⟨ss', h_run', h_acc', _⟩ := (na_loop_fin_run h_mono_m).mp ⟨h_run1, h_inl, h_inr⟩
        use ss'
      · have := h_mono (show m < m + 1 by omega)
        simp +instances [extract_drop, (show φ m + (φ (m + 1) - φ m) = φ (m + 1) by omega)]
  · rintro ⟨φ, h_mono, h_0, h_acc⟩
    choose len as' h_acc h_as' using h_acc
    choose ss' h_run h_acc using h_acc
    let seg k := Segment φ k
    let ss : Stream' (Unit ⊕ NA.State A) := fun k ↦ if k ∈ range φ then inl () else inr (ss' (seg k) (k - φ (seg k)))
    use ss ; constructor <;> [constructor ; skip]
    · have h_0' : ∃ k, φ k = 0 := by use 0
      simp +instances [ss, h_0', NA.Loop]
    · intro k
      have h_seg_k : φ (seg k) ≤ k := by exact segment_lower_bound h_mono h_0 k
      have h_seg_k1 : k < φ (seg k + 1) := by exact segment_upper_bound h_mono h_0 k
      have h_mono_k : φ (seg k + 1) - φ (seg k) > 0 := by omega
      suffices h_lhs :
          (M.Loop acc).FinRun (φ (seg k + 1) - φ (seg k)) (as.drop (φ (seg k))) (ss.drop (φ (seg k))) ∧
          (ss.drop (φ (seg k))) (φ (seg k + 1) - φ (seg k)) = inl () ∧
          (∀ j < φ (seg k + 1) - φ (seg k), j > 0 → (ss.drop (φ (seg k))) j ∈ range inr) by
        have h_run_k := h_lhs.1.2 (k - φ (seg k)) (show k - φ (seg k) < φ (seg k + 1) - φ (seg k) by omega)
        simp +instances [get_drop', (show φ (seg k) + (k - φ (seg k)) = k by omega),
          (show φ (seg k) + (k - φ (seg k) + 1) = k + 1 by omega)] at h_run_k
        exact h_run_k
      apply (na_loop_fin_run h_mono_k).mpr
      use (ss' (seg k))
      obtain ⟨h_len_k, h_as'_k⟩ := extract_eq_extract <| h_as' (seg k)
      simp at h_len_k h_as'_k
      simp +instances [← h_len_k, get_drop']
      constructorm* _ ∧ _
      · apply na_FinRun_modulo (n := len (seg k)) (as := as' (seg k)) (ss := ss' (seg k)) (hr := h_run (seg k))
        · intro j h_j ; simp +instances [get_drop', h_as'_k j h_j, add_comm]
        · simp
      · exact h_acc (seg k)
      · simp +instances [ss]
      · simp +instances [ss, (show φ (seg k) + len (seg k) = φ (seg k + 1) by omega)]
      · intro j h_j_1 h_j_0
        have h_j_2 : ¬ ∃ m, φ m = φ (seg k) + j := by
          exact segment_range_gap h_mono (show φ (seg k) < φ (seg k) + j by omega) (show φ (seg k) + j < φ (seg k + 1) by omega)
        have h_j_3 : seg (φ (seg k) + j) = seg k := by
          exact segment_range_val h_mono (show φ (seg k) ≤ φ (seg k) + j by omega) (show φ (seg k) + j < φ (seg k + 1) by omega)
        simp +instances [ss, h_j_2, h_j_3]
    · have h_uset : {k | ss k = inl ()} = range φ := by ext k ; simp +instances [ss]
      simp +instances [Nat.frequently_atTop_iff_infinite, h_uset]
      exact strict_mono_infinite h_mono
end Automata
