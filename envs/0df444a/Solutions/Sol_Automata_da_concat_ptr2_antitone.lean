-- Prove2me | solution 1 for Automata.da_concat_ptr2_antitone
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T04:38:17.634222+00:00
-- url     : https://prove2.me/submissions/6487405b-a426-4892-ae7c-0973756bbdc4

import Definitions.Def_AutomataTheory_Automata_Det
import Definitions.Def_AutomataTheory_Automata_DetConcat
import Theorems.Thm_Automata_da_concat_ptr2_det_run

set_option autoImplicit true
open Function Set Prod Option Filter Stream'
open Classical
attribute [local instance_reducible] Stream'
open Automata
variable {A : Type} (M1 : DA A) (acc1 : Set M1.State) (M2 : DA A)
attribute [local instance_reducible] DA.Concat
variable [Finite M2.State]
namespace Automata
theorem _root_.solution (as : Stream' A) (n : ℕ) (h_n : M1.DetRun as n ∈ acc1):
    Antitone (DA.ConcatPtr2 M1 acc1 M2 as n h_n) := by
  apply antitone_nat_of_succ_le ; intro k
  have h_spec_k1 := choose_spec (da_concat_ptr2_exists M1 acc1 M2 as n h_n (k + 1))
  have h_def_k1 : M1.ConcatPtr2 acc1 M2 as n h_n (k + 1) = choose (da_concat_ptr2_exists M1 acc1 M2 as n h_n (k + 1)) := rfl
  simp +instances [← h_def_k1, ← add_assoc] at h_spec_k1
  obtain ⟨_, h_eq1, h_min⟩ := h_spec_k1
  by_contra! h_contra
  have h_eq2 := h_min (M1.ConcatPtr2 acc1 M2 as n h_n k) h_contra
  simp +instances [da_concat_ptr2_det_run, h_eq1] at h_eq2
end Automata
