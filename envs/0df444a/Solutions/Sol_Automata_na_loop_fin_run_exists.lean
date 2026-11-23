-- Prove2me | solution 1 for Automata.na_loop_fin_run_exists
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T04:40:36.237813+00:00
-- url     : https://prove2.me/submissions/fa5ff80e-613b-4342-bf2a-520a61e00e90

import Definitions.Def_AutomataTheory_Automata_Basic
import Definitions.Def_AutomataTheory_Languages_Basic
import Definitions.Def_AutomataTheory_Sequences_Segments
import Definitions.Def_AutomataTheory_Automata_Loop
import Theorems.Thm_Automata_na_loop_fin_run
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
theorem _root_.solution {n : ℕ} {as : Stream' A} {ss' : Stream' M.State}
    (h_run' : M.FinRun n as ss') (h_acc' : ss' n ∈ acc) :
    ∃ ss, (M.Loop acc).FinRun n as ss ∧ ss n = inl () ∧ (∀ k < n, k > 0 → ss k = inr (ss' k)) := by
  rcases (show n = 0 ∨ n > 0 by omega) with ⟨rfl⟩ | h_n
  · use (fun k ↦ inl ()) ; simp +instances [NA.FinRun, NA.Loop]
  let ss k := if k = 0 ∨ k = n then inl () else inr (ss' k)
  suffices h : ∃ ss', M.FinRun n as ss' ∧ ss' n ∈ acc ∧ ss 0 = inl () ∧ ss n = inl () ∧ (∀ k < n, k > 0 → ss k = inr (ss' k)) by
    obtain ⟨h_run, h_ss_n, _⟩ := (na_loop_fin_run h_n).mpr h
    use ss ; simp +instances [h_run, h_ss_n]
    intro k h_k_n h_k_0 ; simp +instances [ss] ; omega
  use ss' ; simp +instances [h_run', h_acc', ss] ; omega
end Automata
