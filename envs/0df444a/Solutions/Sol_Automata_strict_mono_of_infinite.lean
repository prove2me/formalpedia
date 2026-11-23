-- Prove2me | solution 1 for Automata.strict_mono_of_infinite
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T04:50:01.040017+00:00
-- url     : https://prove2.me/submissions/6532b236-85a9-4f45-aecb-94ae8994cd4c

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
theorem _root_.solution {ns : Set ℕ} (h : ns.Infinite) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧ range φ = ns := by
  use (Nat.nth (· ∈ ns)) ; constructor
  · exact Nat.nth_strictMono h
  · exact Nat.range_nth_of_infinite h
end Automata
