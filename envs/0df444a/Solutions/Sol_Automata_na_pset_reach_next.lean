-- Prove2me | solution 1 for Automata.na_pset_reach_next
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T04:43:31.582819+00:00
-- url     : https://prove2.me/submissions/4a9da2ec-c0f9-4623-b7ad-2b568c240740

import Definitions.Def_AutomataTheory_Automata_Det
import Definitions.Def_AutomataTheory_Automata_PSet

set_option autoImplicit true
open Function Set Filter Stream'
attribute [local instance_reducible] Stream'
open Automata
variable {A : Type}
attribute [local instance_reducible] NA.PSet
variable {M : NA A}
namespace Automata
theorem _root_.solution (as : Stream' A) (k : ℕ) :
    M.PSet.DetRun as (k + 1) = ⋃ s ∈ M.PSet.DetRun as k, M.next s (as k) := by
  simp +instances [DA.DetRun, NA.PSet]
end Automata
