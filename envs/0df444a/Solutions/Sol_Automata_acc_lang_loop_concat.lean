-- Prove2me | solution 1 for Automata.acc_lang_loop_concat
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T04:41:22.35007+00:00
-- url     : https://prove2.me/submissions/d6c9926e-9350-41e5-8cb9-927d36a8d647

import Definitions.Def_AutomataTheory_Automata_Basic
import Definitions.Def_AutomataTheory_Languages_Basic
import Definitions.Def_AutomataTheory_Sequences_Segments
import Definitions.Def_AutomataTheory_Automata_Loop
import Theorems.Thm_P2M_Stream__extract_append_zero_right_6dd07cb04cbe
import Theorems.Thm_P2M_Stream__get_append_left__364c5eb8ed49
import Theorems.Thm_P2M_Stream__get_append_right__3668139ab712
import Theorems.Thm_P2M_Stream__get_extract__ebf059d6908b

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
attribute [local instance_reducible] NA.Loop
variable {A : Type} {M : NA A} {acc : Set M.State}
namespace Automata
theorem _root_.solution :
    ((M.Loop acc).AcceptedLang {inl ()}) * ((M.Loop acc).AcceptedLang {inl ()}) ⊆
    (M.Loop acc).AcceptedLang {inl ()} := by
  rintro al ⟨al1, al2, ⟨n1, as1, ⟨ss1, h_run1, h_acc1⟩, rfl⟩, ⟨n2, as2, ⟨ss2, h_run2, h_acc2⟩, rfl⟩, rfl⟩
  use (n1 + n2), ((as1.extract 0 n1) ++ₛ as2) ; symm ; constructor
  · have h1 : (as1.extract 0 n1).length ≤ n1 + n2 := by simp +instances [length_extract]
    simp +instances [extract_append_zero_right h1, length_extract]
  let ss k := if k < n1 then ss1 k else ss2 (k - n1)
  use ss ; symm ; constructor
  · simp at h_acc2 ; simp +instances [ss, h_acc2]
  constructor
  · suffices h_0 : ss 0 = inl () by simp +instances [h_0, NA.Loop]
    rcases (show n1 = 0 ∨ n1 > 0 by omega) with h_n1 | h_n1 <;> simp +instances [ss, h_n1]
    · exact h_run2.1
    · exact h_run1.1
  intro k h_k
  rcases (show k + 1 < n1 ∨ k + 1 = n1 ∨ k + 1 > n1 by omega) with h_k | h_k | h_k
  · have h1 : k < (as1.extract 0 n1).length := by simp +instances [length_extract] ; omega
    simp (disch := omega) [get_append_left' h1, get_extract']
    have h_next := h_run1.2 k (by omega)
    simp +instances [ss, h_next, h_k, (show k < n1 by omega)]
  · have h_next := h_run1.2 k (by omega)
    suffices h_n1 : ss2 0 = ss1 (k + 1) by
      have h1 : k < (as1.extract 0 n1).length := by simp +instances [length_extract] ; omega
      simp (disch := omega) [get_append_left' h1, get_extract']
      simp +instances [ss, ← h_k, h_n1, h_next]
    simp +instances [← h_k] at h_acc1
    simp +instances [h_acc1] ; exact h_run2.1
  · have h_next := h_run2.2 (k - n1) (by omega)
    have h1 : (as1.extract 0 n1).length ≤ k := by simp +instances [length_extract] ; omega
    simp +instances [get_append_right' h1, length_extract, ss, h_next,
      (show ¬ k + 1 < n1 by omega), (show ¬ k < n1 by omega), (show k + 1 - n1 = k - n1 + 1 by omega)]
end Automata
