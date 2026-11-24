-- Prove2me | Definitions.Def_FongoSync_Register
-- name    : FongoSync_Register
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-24T07:57:04.261843+00:00
-- url     : https://prove2.me/theorems/e031c26d-09f7-49bd-8caa-9ee9c3d8bd4a
-- title:
--   Register
-- statement:
--   Definitions and structural lemmas for Register, from bongofongo (bongofongo/fongo-sync; see pinned Apache-2.0 LICENSE-APACHE)'s pinned FongoSync local-first CRDT replication convergence laws development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/bongofongo/fongo-sync/blob/7e3f771e7c150a69dbbd87827b7ffe4525f219a7/FongoSync/Register.lean

import Definitions.Def_FongoSync_Clock
import Batteries.Tactic.Alias
set_option autoImplicit false
namespace FongoSync
open Std
set_option linter.unusedSectionVars false
section Keep
variable {E K : Type} (cmp : K → K → Ordering) (key : E → K)
def keep : Option E → E → Option E
  | none, e => some e
  | some s, e => if cmp (key s) (key e) = .lt then some e else some s
def join : Option E → Option E → Option E
  | a, none => a
  | a, some e => keep cmp key a e
def KeyInj (l : List E) : Prop := ∀ a ∈ l, ∀ b ∈ l, key a = key b → a = b
variable [TransCmp cmp] [LawfulEqCmp cmp]
variable {cmp key}
@[simp] theorem keep_none (e : E) : keep cmp key none e = some e := rfl
@[simp] theorem keep_held (s e : E) :
    keep cmp key (some s) e = if cmp (key s) (key e) = .lt then some e else some s := rfl
end Keep
inductive Strategy where
  | lww
  | max
  deriving DecidableEq, Repr
structure Entry (V : Type) where
  value : V
  clock : Hlc
  deriving DecidableEq, Repr
section Wins
variable {V : Type} [Ord V]
def wins (strategy : Strategy) (stored : Option (Entry V)) (value : V) (clock : Hlc) : Bool :=
  match stored with
  | none => true
  | some s =>
    match strategy with
    | .lww => compare clock s.clock == .gt
    | .max =>
      match compare value s.value with
      | .gt => true
      | .eq => compare clock s.clock == .gt
      | .lt => false
def apply (strategy : Strategy) (held : Option (Entry V)) (e : Entry V) : Option (Entry V) :=
  if wins strategy held e.value e.clock then some e else held
def maxCmp (a b : V × Hlc) : Ordering := compareLex (compareOn (·.1)) (compareOn (·.2)) a b
def Entry.pair (e : Entry V) : V × Hlc := (e.value, e.clock)
variable [TransOrd V] [LawfulEqOrd V]
instance : TransCmp (maxCmp (V := V)) :=
  inferInstanceAs (TransCmp (compareLex (compareOn (fun p : V × Hlc => p.1))
    (compareOn (fun p : V × Hlc => p.2))))
instance : LawfulEqCmp (maxCmp (V := V)) where
  eq_of_compare {a b} h := by
    simp only [maxCmp, compareLex_eq_eq, compareOn] at h
    exact Prod.ext (LawfulEqOrd.eq_of_compare h.1) (LawfulEqOrd.eq_of_compare h.2)
def UniqueClocks (l : List (Entry V)) : Prop := KeyInj Entry.clock l
def merge (s : Strategy) : Option (Entry V) → Option (Entry V) → Option (Entry V)
  | a, none => a
  | a, some e => apply s a e
end Wins
end FongoSync


