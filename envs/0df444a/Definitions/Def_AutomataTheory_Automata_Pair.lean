-- Prove2me | Definitions.Def_AutomataTheory_Automata_Pair
-- name    : AutomataTheory_Automata_Pair
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-23T04:16:58.787461+00:00
-- url     : https://prove2.me/theorems/7fb0ca94-0e13-4f07-9fc0-2223ec04e262
-- title:
--   Pair
-- statement:
--   Definitions and structural lemmas for Pair, from Ching-Tsun Chou's pinned Omega-regular languages and deterministic Muller automata development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/ctchou/AutomataTheory/blob/f196548710ce1ba8e7d4aa73b1cf846248ecfcb8/AutomataTheory/Automata/Pair.lean

import Definitions.Def_AutomataTheory_Automata_Hist
import Definitions.Def_AutomataTheory_Languages_RegLang
import Definitions.Def_AutomataTheory_Sequences_InfOcc
set_option autoImplicit true
open Function Set Filter Stream'
attribute [local implicit_reducible] Stream'
namespace Automata
attribute [local instance_reducible] NA.addHist
section PairLang
variable {A : Type}
def NA.PairPath (M : NA A) (s s' : M.State) (al : List A) (ss : Stream' M.State) :=
  ss 0 = s ∧ ss al.length = s' ∧ ∀ k, (h : k < al.length) → ss (k + 1) ∈ M.next (ss k) (al[k]'h)
def NA.PairAccPath (M : NA A) (acc : Set M.State) (s s' : M.State) (al : List A) (ss : Stream' M.State) :=
  M.PairPath s s' al ss ∧ ∃ k < al.length + 1, ss k ∈ acc
def NA.PairLang (M : NA A) (s s' : M.State) : Set (List A) :=
  { al | ∃ ss, M.PairPath s s' al ss }
def NA.PairAccLang (M : NA A) (acc : Set M.State) (s s' : M.State) : Set (List A) :=
  { al | ∃ ss, M.PairAccPath acc s s' al ss }
variable {M : NA A} {acc : Set M.State}
def NA.SingleInit (s : M.State) : NA A where
  State := M.State
  init := {s}
  next := M.next
attribute [local instance_reducible] NA.SingleInit
end PairLang


