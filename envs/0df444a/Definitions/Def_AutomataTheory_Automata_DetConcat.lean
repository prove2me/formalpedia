-- Prove2me | Definitions.Def_AutomataTheory_Automata_DetConcat
-- name    : AutomataTheory_Automata_DetConcat
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-23T04:32:55.28056+00:00
-- url     : https://prove2.me/theorems/3950c3cf-c0c5-4b19-aae3-a2b9b0e2a419
-- title:
--   Det Concat
-- statement:
--   Definitions and structural lemmas for Det Concat, from Ching-Tsun Chou's pinned Omega-regular languages and deterministic Muller automata development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/ctchou/AutomataTheory/blob/f196548710ce1ba8e7d4aa73b1cf846248ecfcb8/AutomataTheory/Automata/DetConcat.lean

import Definitions.Def_AutomataTheory_Automata_Det
import Theorems.Thm_P2M_Stream__get_drop__05b839498f63
import Theorems.Thm_option_some_pigeonhole

set_option autoImplicit true
open Function Set Prod Option Filter Stream'
open Classical
attribute [local instance_reducible] Stream'
namespace Automata
section AutomataDetConcat
variable {A : Type} (M1 : DA A) (acc1 : Set M1.State) (M2 : DA A)
noncomputable def DA.Concat : DA A where
  State := M1.State × (Fin (Nat.card M2.State + 2) → Option M2.State)
  init := (M1.init, fun _ ↦ none)
  next := fun s a ↦ (M1.next s.1 a, fun i ↦
    match (s.2 i) with
    | some s2 =>
      if ∀ j < i, (h : (s.2 j).isSome) → (s.2 j).get h ≠ s2
      then some (M2.next s2 a)
      else none
    | none =>
      if s.1 ∈ acc1 ∧ ∀ j < i, (s.2 j).isSome
      then some (M2.next M2.init a)
      else none
    )
attribute [local instance_reducible] DA.Concat
lemma da_concat_next_2 (s : (M1.Concat acc1 M2).State) (a : A) (i : Fin (Nat.card M2.State + 2)) :
    ((M1.Concat acc1 M2).next s a).2 i =
    match (s.2 i) with
    | some s2 =>
      if ∀ j < i, (h : (s.2 j).isSome) → (s.2 j).get h ≠ s2
      then some (M2.next s2 a)
      else none
    | none =>
      if s.1 ∈ acc1 ∧ ∀ j < i, (s.2 j).isSome
      then some (M2.next M2.init a)
      else none
  := by rfl
theorem da_concat_det_run_1 (as : Stream' A) (k : ℕ) :
    ((M1.Concat acc1 M2).DetRun as k).1 = M1.DetRun as k := by
  induction' k with k h_ind <;> simp +instances [DA.DetRun]
  · rfl
  simp +instances [← h_ind] ; rfl
variable [Finite M2.State]
theorem da_concat_det_run_cnt2 (as : Stream' A) (n : ℕ) :
    ∃ i, ((M1.Concat acc1 M2).DetRun as n).2 i = none := by
  induction' n with n h_ind
  · use 0 ; simp +instances [DA.DetRun, DA.Concat]
  let s_n := (M1.Concat acc1 M2).DetRun as n
  obtain ⟨i, h_i⟩ := h_ind
  rcases Classical.em (∃ j, j ≠ i ∧ s_n.2 j = none) with h_none | h_some
  · obtain ⟨j, h_ne, h_j⟩ := h_none
    simp +instances [s_n] at h_j
    wlog h : i < j generalizing i j with h'
    · exact h' j h_j i (Ne.symm h_ne) h_i (by fin_omega)
    use j ; simp +instances [DA.DetRun, da_concat_next_2, h_j]
    intro _ ; use i
  · simp +instances [ne_none_iff_isSome] at h_some
    have h1 : {j | (s_n.2 j).isSome} = {i}ᶜ := by ext j ; simp +instances ; grind
    have h2 : {j | (s_n.2 j).isSome}.ncard = Nat.card M2.State + 1 := by
      have h_sum := ncard_add_ncard_compl {i} ; simp +instances at h_sum
      rw [h1] ; omega
    obtain ⟨j1, j2, h_ne, s2, h_j1, h_j2⟩ := option_some_pigeonhole s_n.2 (by omega)
    wlog h : j1 < j2 generalizing j1 j2 with h'
    · exact h' j2 j1 (Ne.symm h_ne) h_j2 h_j1 (by fin_omega)
    simp +instances [s_n] at h_j1 h_j2
    use j2 ; simp +instances [DA.DetRun, da_concat_next_2, h_j2]
    use j1 ; simp +instances [h, h_j1]
theorem da_concat_ptr2_exists (as : Stream' A) (n : ℕ) (h_n : M1.DetRun as n ∈ acc1) (k : ℕ) :
    ∃ i, ((M1.Concat acc1 M2).DetRun as (n + k + 1)).2 i = some (M2.DetRun (as.drop n) (k + 1)) ∧
      if k = 0 then
        ((M1.Concat acc1 M2).DetRun as (n + k)).2 i = none ∧
        ∀ j < i, (((M1.Concat acc1 M2).DetRun as (n + k)).2 j).isSome
      else
        ((M1.Concat acc1 M2).DetRun as (n + k)).2 i = some (M2.DetRun (as.drop n) k) ∧
        ∀ j < i, ((M1.Concat acc1 M2).DetRun as (n + k)).2 j ≠ ((M1.Concat acc1 M2).DetRun as (n + k)).2 i := by
  induction' k with k h_ind
  . let I := {i | ((M1.Concat acc1 M2).DetRun as n).2 i = none}
    have h_fin : I.Finite := by exact toFinite I
    have h_ne : I.Nonempty := by exact da_concat_det_run_cnt2 M1 acc1 M2 as n
    obtain ⟨i, h_i, h_min⟩ := Finite.exists_minimal h_fin h_ne
    simp +instances [I] at h_i h_min
    use i
    simp +instances [h_i, DA.DetRun, da_concat_next_2, da_concat_det_run_1, h_n, get_drop', ← ne_none_iff_isSome]
    intro j h_j h_contra ; have := h_min h_contra ; fin_omega
  obtain ⟨i, h_i, _⟩ := h_ind
  let I := {j | ((M1.Concat acc1 M2).DetRun as (n + k + 1)).2 j = some (M2.DetRun (as.drop n) (k + 1))}
  have h_fin : I.Finite := by exact toFinite I
  have h_ne : I.Nonempty := by use i ; simp +instances [I, h_i]
  obtain ⟨j, h_j, h_min⟩ := Finite.exists_minimal h_fin h_ne
  simp +instances [I] at h_j h_min
  use j
  simp +instances [h_j, ← add_assoc]
  rw [DA.DetRun]
  simp +instances [da_concat_next_2, h_j]
  have h_min' : ∀ j' < j, ¬((M1.Concat acc1 M2).DetRun as (n + k + 1)).2 j' = some (M2.DetRun (as.drop n) (k + 1)) := by
    intro j' h_j' h_contra ; have := h_min h_contra ; fin_omega
  constructorm* _ ∧ _
  · grind
  · simp +instances [DA.DetRun, get_drop', (show n + (k + 1) = n + k + 1 by omega)]
  · grind
noncomputable def DA.ConcatPtr2 (as : Stream' A) (n : ℕ) (h_n : M1.DetRun as n ∈ acc1) (k : ℕ) : Fin (Nat.card M2.State + 2) :=
  choose (da_concat_ptr2_exists M1 acc1 M2 as n h_n k)
variable [Finite M1.State]
instance : Finite ((M1.Concat acc1 M2).State) := by apply Finite.instProd
variable (accSet2 : Set (Set M2.State))
def DA.MullerAcc_Concat : Set (Set (M1.Concat acc1 M2).State) :=
  { acc | ∃ i, {s2 | ∃ s ∈ acc, s.2 i = some s2} ∈ accSet2 ∧ (∀ s ∈ acc, (s.2 i).isSome) }
end AutomataDetConcat


