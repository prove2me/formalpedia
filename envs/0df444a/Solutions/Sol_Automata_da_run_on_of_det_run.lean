-- Prove2me | solution 1 for Automata.da_run_on_of_det_run
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T04:33:26.934972+00:00
-- url     : https://prove2.me/submissions/f13d99e2-bc12-405c-9045-d136e4b2019c

import Definitions.Def_AutomataTheory_Automata_Basic
import Definitions.Def_AutomataTheory_Languages_Basic
import Definitions.Def_AutomataTheory_Sequences_InfOcc
import Definitions.Def_AutomataTheory_Automata_Det
import Theorems.Thm_Automata_da_run_from_on_append
import Theorems.Thm_P2M_Stream__extract_eq_nil_7f26d60de260
import Theorems.Thm_P2M_Stream__extract_succ_right__dce2e16ca09b


set_option autoImplicit true
open Function Set Filter Stream'
attribute [local instance_reducible] Stream'
open Automata
variable {A : Type}
attribute [local instance_reducible] DA.toNA
variable {M : DA A}
namespace Automata
theorem _root_.solution (M : DA A) (as : Stream' A) (n : ℕ) :
    M.RunOn (as.extract 0 n) = M.DetRun as n := by
  induction' n with n h_ind
  · simp +instances [extract_eq_nil, DA.DetRun, DA.RunOn, DA.RunFromOn]
  have h1 := extract_succ_right' (xs := as) (show 0 ≤ n by omega)
  rw [DA.RunOn, DA.DetRun, ← h_ind, h1, da_run_from_on_append] ; rfl
end Automata
