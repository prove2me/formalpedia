-- Prove2me | solution 1 for Automata.da_concat_ptr2_det_run
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T04:33:29.828962+00:00
-- url     : https://prove2.me/submissions/85d5aeec-79a4-42f0-b347-3d37cefbf1bb

import Definitions.Def_AutomataTheory_Automata_Det
import Definitions.Def_AutomataTheory_Automata_DetConcat

set_option autoImplicit true
open Function Set Prod Option Filter Stream'
open Classical
attribute [local instance_reducible] Stream'
open Automata
variable {A : Type} (M1 : DA A) (acc1 : Set M1.State) (M2 : DA A)
attribute [local instance_reducible] DA.Concat
variable [Finite M2.State]
namespace Automata
theorem _root_.solution (as : Stream' A) (n : ℕ) (h_n : M1.DetRun as n ∈ acc1) (k : ℕ) :
    ((M1.Concat acc1 M2).DetRun as (n + k + 1)).2 (DA.ConcatPtr2 M1 acc1 M2 as n h_n k) =
    some (M2.DetRun (as.drop n) (k + 1)) := by
  exact (choose_spec (da_concat_ptr2_exists M1 acc1 M2 as n h_n k)).1
end Automata
