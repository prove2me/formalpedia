-- Prove2me | solution 1 for Automata.da_concat_to_muller_accept
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T04:41:40.390084+00:00
-- url     : https://prove2.me/submissions/287090bb-1d23-4cf8-bcf1-158704af915d

import Definitions.Def_AutomataTheory_Automata_Det
import Definitions.Def_AutomataTheory_Automata_DetConcat
import Theorems.Thm_Automata_da_concat_ptr2_det_run
import Theorems.Thm_Automata_da_concat_ptr2_eventually
import Theorems.Thm_Automata_da_fin_run_unique
import Theorems.Thm_inf_occ_eventually


set_option autoImplicit true
open Function Set Prod Option Filter Stream'
open Classical
attribute [local instance_reducible] Stream'
open Automata
variable {A : Type} (M1 : DA A) (acc1 : Set M1.State) (M2 : DA A)
attribute [local instance_reducible] DA.Concat
variable [Finite M2.State]
variable [Finite M1.State]
variable (accSet2 : Set (Set M2.State))
namespace Automata
theorem _root_.solution (as : Stream' A) (n : ℕ)
    (h1 : M1.toNA.FinAccept acc1 n as) (h2 : M2.MullerAccept accSet2 (as.drop n)) :
    (M1.Concat acc1 M2).MullerAccept (DA.MullerAcc_Concat M1 acc1 M2 accSet2) as := by
  obtain ⟨ss, h_run1, h_acc1⟩ := h1
  rw [da_fin_run_unique h_run1 n (by omega)] at h_acc1
  obtain ⟨i, m, h_m, h_i⟩ := da_concat_ptr2_eventually M1 acc1 M2 as n h_acc1
  have h_suffix : ∀ k ≥ m, ((M1.Concat acc1 M2).DetRun as k).2 i = some (M2.DetRun (as.drop n) (k - n)) := by
    intro k h_k
    have h_p := da_concat_ptr2_det_run M1 acc1 M2 as n h_acc1 (k - n - 1)
    simp +instances [h_i k h_k, (show n + (k - n - 1) + 1 = k by omega), (show k - n - 1 + 1 = k - n by omega)] at h_p
    exact h_p
  use i ; constructor
  · suffices h_inf : {s2 | ∃ s ∈ InfOcc ((M1.Concat acc1 M2).DetRun as), s.2 i = some s2} = InfOcc (M2.DetRun (as.drop n)) by
      simpa +instances [h_inf]
    ext s2 ; constructor
    · rintro ⟨s, h_inf, h_s⟩
      apply frequently_atTop.mpr ; intro l
      obtain ⟨k, h_k, rfl⟩ := frequently_atTop.mp h_inf (m + l)
      simp +instances [h_suffix k (by omega)] at h_s
      use (k - n) ; simp +instances [h_s] ; omega
    · intro h_inf
      obtain ⟨l, h_l⟩ := eventually_atTop.mp <| inf_occ_eventually ((M1.Concat acc1 M2).DetRun as)
      obtain ⟨k, h_k, rfl⟩ := frequently_atTop.mp h_inf (l + m - n)
      use ((M1.Concat acc1 M2).DetRun as (k + n)) ; constructor
      · exact h_l (k + n) (by omega)
      · simp +instances [h_suffix (k + n) (by omega)]
  · intro s h_s
    obtain ⟨k, h_k, rfl⟩ := frequently_atTop.mp h_s m
    simp +instances [h_suffix k h_k]
end Automata
