-- Prove2me | solution 1 for Automata.da_concat_of_muller_accept
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T04:40:33.341621+00:00
-- url     : https://prove2.me/submissions/52ca67f8-a8e1-44bf-890a-c59fbb2c0ade

import Definitions.Def_AutomataTheory_Automata_Det
import Definitions.Def_AutomataTheory_Automata_DetConcat
import Theorems.Thm_Automata_da_concat_det_run_2
import Theorems.Thm_Automata_da_fin_run_exists
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
theorem _root_.solution (as : Stream' A)
    (h : (M1.Concat acc1 M2).MullerAccept (DA.MullerAcc_Concat M1 acc1 M2 accSet2) as) :
    ∃ n, M1.toNA.FinAccept acc1 n as ∧ M2.MullerAccept accSet2 (as.drop n) := by
  obtain ⟨i, h_acc2, h_some⟩ := h
  obtain ⟨n, h_n⟩ := eventually_atTop.mp <| inf_occ_eventually ((M1.Concat acc1 M2).DetRun as)
  have h_eventl : ∀ k ≥ n, (((M1.Concat acc1 M2).DetRun as k).2 i).isSome := by
    intro k h_k ; exact h_some ((M1.Concat acc1 M2).DetRun as k) <| h_n k h_k
  obtain ⟨m, h_m, h_acc1, h_suffix⟩ := da_concat_det_run_2 M1 acc1 M2 as n i h_eventl
  suffices h_inf : {s2 | ∃ s ∈ InfOcc ((M1.Concat acc1 M2).DetRun as), s.2 i = some s2} = InfOcc (M2.DetRun (as.drop m)) by
    use m ; constructor
    · exact ⟨M1.DetRun as, da_fin_run_exists m as, h_acc1⟩
    · rw [h_inf] at h_acc2
      exact h_acc2
  ext s2 ; constructor
  · rintro ⟨s, h_inf, h_s⟩
    apply frequently_atTop.mpr ; intro l
    obtain ⟨k, h_k, rfl⟩ := frequently_atTop.mp h_inf (m + l + 1)
    simp +instances [h_suffix k (by omega)] at h_s
    use (k - m) ; simp +instances [h_s] ; omega
  · intro h_inf
    obtain ⟨k, h_k, rfl⟩ := frequently_atTop.mp h_inf (n - m)
    use ((M1.Concat acc1 M2).DetRun as (k + m)) ; constructor
    · exact h_n (k + m) (by omega)
    · simp +instances [h_suffix (k + m) (by omega)]
end Automata
