-- Prove2me | Definitions.Def_FongoSync_State
-- name    : FongoSync_State
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-24T07:57:51.132987+00:00
-- url     : https://prove2.me/theorems/a4b27dca-fb80-4d7d-95a8-c436d0f492cf
-- title:
--   State
-- statement:
--   Definitions and structural lemmas for State, from bongofongo (bongofongo/fongo-sync; see pinned Apache-2.0 LICENSE-APACHE)'s pinned FongoSync local-first CRDT replication convergence laws development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/bongofongo/fongo-sync/blob/7e3f771e7c150a69dbbd87827b7ffe4525f219a7/FongoSync/State.lean

import Definitions.Def_FongoSync_Register
set_option autoImplicit false
namespace FongoSync
open Std
set_option linter.unusedSectionVars false
def DELETED : String := ("$deleted")
structure Change (V : Type) where
  collection : String
  gid : Gid
  field : String
  value : V
  clock : Hlc
  deriving DecidableEq, Repr
variable {V : Type}
abbrev Key := String × Gid × String
def Change.key (c : Change V) : Key := (c.collection, c.gid, c.field)
def Change.entry (c : Change V) : Entry V := ⟨c.value, c.clock⟩
def Compatible (a b : Change V) : Prop :=
  a.key = b.key → a.clock = b.clock → a.value = b.value
def ClockDetermines (cs : List (Change V)) : Prop :=
  ∀ a ∈ cs, ∀ b ∈ cs, Compatible a b
def strategyAt (strategyOf : String → String → Strategy) (k : Key) : Strategy :=
  if k.2.2 = DELETED then .lww else strategyOf k.1 k.2.2
abbrev State (V : Type) := Key → Option (Entry V)
def State.empty : State V := fun _ => none
variable [Ord V]
def State.apply (strategyOf : String → String → Strategy) (st : State V) (c : Change V) : State V :=
  fun k => if k = c.key then FongoSync.apply (strategyAt strategyOf c.key) (st k) c.entry else st k
def merged (strategyOf : String → String → Strategy) (cs : List (Change V)) : State V :=
  cs.foldl (State.apply strategyOf) State.empty
def entriesAt (cs : List (Change V)) (k : Key) : List (Entry V) :=
  (cs.filter (·.key = k)).map Change.entry
variable [TransOrd V] [LawfulEqOrd V]
end FongoSync


