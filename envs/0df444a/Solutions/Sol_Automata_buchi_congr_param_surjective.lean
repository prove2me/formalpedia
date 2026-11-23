-- Prove2me | solution 1 for Automata.buchi_congr_param_surjective
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T04:49:55.120137+00:00
-- url     : https://prove2.me/submissions/abf571ce-ad03-4cbc-9d56-a02792bf7c80

import Definitions.Def_AutomataTheory_Automata_Pair
import Definitions.Def_AutomataTheory_Mathlib_InfGraphRamsey
import Definitions.Def_AutomataTheory_Congruences_BuchiCongr

set_option autoImplicit true
open Function Set Filter Stream'
open Automata
attribute [local instance_reducible] NA.BuchiCongr
open Classical
variable {A : Type}
variable {M : NA A} {acc : Set M.State}
namespace Automata
theorem _root_.solution : Surjective (M.BuchiCongrParam acc) := by
  intro q
  let π s s' := (q.out ∈ M.PairLang s s', q.out ∈ M.PairAccLang acc s s')
  have h : ∃ u, ∀ s s', ((π s s').1 ↔ u ∈ M.PairLang s s') ∧ ((π s s').2 ↔ u ∈ M.PairAccLang acc s s') := by
    use q.out ; intro s s' ; simp [π]
  use π
  simp [NA.BuchiCongrParam, h]
  rw [← Quotient.out_eq q]
  apply Quotient.sound
  intro s s'
  have h1 := choose_spec h s s'
  simp [π] at h1
  simp [h1]
end Automata
