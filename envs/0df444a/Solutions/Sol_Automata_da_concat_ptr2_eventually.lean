-- Prove2me | solution 1 for Automata.da_concat_ptr2_eventually
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T04:40:32.681963+00:00
-- url     : https://prove2.me/submissions/89bd9280-e8de-494f-8acb-3d10173ec317

import Definitions.Def_AutomataTheory_Automata_Det
import Definitions.Def_AutomataTheory_Automata_DetConcat
import Theorems.Thm_Automata_da_concat_ptr2_antitone
import Theorems.Thm_antitone_fin_eventually


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
    ∃ i : Fin (Nat.card M2.State + 2), ∃ m > n, ∀ k ≥ m, DA.ConcatPtr2 M1 acc1 M2 as n h_n (k - n - 1) = i := by
  obtain ⟨i, m, h_i⟩ := antitone_fin_eventually <| da_concat_ptr2_antitone M1 acc1 M2 as n h_n
  use i, (m + n + 1) ; simp +instances [show m + n + 1 > n by omega]
  intro k h_k ; exact h_i (k - n - 1) (by omega)
end Automata
