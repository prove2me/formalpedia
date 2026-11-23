-- Prove2me | solution 1 for Automata.da_concat_det_run_2
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T04:38:07.595062+00:00
-- url     : https://prove2.me/submissions/1c558bba-b941-4129-ac06-1a73286e215e

import Definitions.Def_AutomataTheory_Automata_Det
import Definitions.Def_AutomataTheory_Automata_DetConcat
import Theorems.Thm_P2M_Stream__get_drop__05b839498f63


set_option autoImplicit true
open Function Set Prod Option Filter Stream'
open Classical
attribute [local instance_reducible] Stream'
open Automata
variable {A : Type} (M1 : DA A) (acc1 : Set M1.State) (M2 : DA A)
attribute [local instance_reducible] DA.Concat
namespace Automata
theorem _root_.solution (as : Stream' A) (n : ℕ) (i : Fin (Nat.card M2.State + 2))
    (h : ∀ k ≥ n, (((M1.Concat acc1 M2).DetRun as k).2 i).isSome) :
    ∃ m < n, M1.DetRun as m ∈ acc1 ∧
      ∀ k > m, ((M1.Concat acc1 M2).DetRun as k).2 i = some (M2.DetRun (as.drop m) (k - m)) := by
  let P := (fun k ↦ ((M1.Concat acc1 M2).DetRun as k).2 i = none)
  let m := Nat.findGreatest P n
  have h_m : P m := by
    unfold m
    apply Nat.findGreatest_spec (P := P) (show 0 ≤ n by omega)
    simp +instances [P, DA.DetRun, DA.Concat]
  have h_n : m < n := by
    have : m ≤ n := by apply Nat.findGreatest_le
    suffices h_eq : m ≠ n by omega
    by_contra h_contra
    simp +instances [h_contra, P] at h_m
    specialize h n (by omega)
    simp +instances [h_m] at h
  have h_gt_m : ∀ k > m, ∃ s2, ((M1.Concat acc1 M2).DetRun as k).2 i = some s2 := by
    intro k h_k
    rcases (show k ≤ n ∨ k ≥ n by omega) with h_k' | h_k'
    · exact ne_none_iff_exists'.mp <| Nat.findGreatest_is_greatest (P := P) (n := n) (k := k) h_k h_k'
    · exact isSome_iff_exists.mp <| h k h_k'
  obtain ⟨s2, h_s2⟩ := h_gt_m (m + 1) (by omega)
  unfold P at h_m
  obtain ⟨h_acc1, rfl⟩ : M1.DetRun as m ∈ acc1 ∧ DA.next DA.init (as m) = s2 := by
    have h_next := da_concat_next_2 M1 acc1 M2 ((M1.Concat acc1 M2).DetRun as m) (as m) i
    simp +instances [DA.DetRun, h_next, h_m, da_concat_det_run_1] at h_s2
    tauto
  use m ; simp +instances [h_n, h_acc1]
  intro k h_k
  obtain ⟨j, rfl⟩ := show ∃ j, k = m + 1 + j by use k - m - 1 ; omega
  induction' j with j h_ind
  · simp +instances [DA.DetRun] at h_s2 ⊢
    simp +instances [h_s2, get_drop']
  specialize h_ind (by omega)
  have h_next := da_concat_next_2 M1 acc1 M2 ((M1.Concat acc1 M2).DetRun as (m + 1 + j)) (as (m + 1 + j)) i
  simp +instances [h_ind, eq_ite_iff] at h_next
  rcases h_next with ⟨_, h_some⟩ | ⟨_, h_none⟩
  · simp +instances [DA.DetRun, h_some, get_drop',
      (show m + (1 + j) = m + 1 + j by omega), (show m + 1 + j - m = 1 + j by omega),
      (show m + 1 + (j + 1) - m = 1 + j + 1 by omega)]
  · obtain ⟨s2', h_s2'⟩ := h_gt_m (m + 1 + j + 1) (by omega)
    simp +instances [DA.DetRun, h_none] at h_s2'
end Automata
