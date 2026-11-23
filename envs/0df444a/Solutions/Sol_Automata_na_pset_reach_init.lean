-- Prove2me | solution 1 for Automata.na_pset_reach_init
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T04:43:17.140796+00:00
-- url     : https://prove2.me/submissions/83d18c66-8a6d-418a-9186-cd6ac990e3d2

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
theorem _root_.solution (as : Stream' A) :
    M.PSet.DetRun as 0 = M.init := by
  simp +instances [DA.DetRun, NA.PSet]
end Automata
