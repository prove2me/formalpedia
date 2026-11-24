-- Prove2me | Definitions.Def_FongoSync_View
-- name    : FongoSync_View
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-24T07:58:14.255314+00:00
-- url     : https://prove2.me/theorems/734f707b-9c73-4690-b6d8-b39fa9837736
-- title:
--   View
-- statement:
--   Definitions and structural lemmas for View, from bongofongo (bongofongo/fongo-sync; see pinned Apache-2.0 LICENSE-APACHE)'s pinned FongoSync local-first CRDT replication convergence laws development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/bongofongo/fongo-sync/blob/7e3f771e7c150a69dbbd87827b7ffe4525f219a7/FongoSync/View.lean

import Definitions.Def_FongoSync_State
import Definitions.Def_FongoSync_Alias
import Definitions.Def_FongoSync_GidSet
set_option autoImplicit false
namespace FongoSync
open Std Classical
set_option linter.unusedSectionVars false
inductive Value where
  | null
  | int (i : Int)
  | text (s : String)
  | blob (b : List UInt8)
  | ref (g : Gid)
  deriving DecidableEq, Repr
def Value.rank : Value → Nat
  | .null => 0
  | .int _ => 1
  | .text _ => 2
  | .blob _ => 3
  | .ref _ => 4
def Value.cmp : Value → Value → Ordering
  | .int a, .int b => compare a b
  | .text a, .text b => compare a b
  | .blob a, .blob b => compare a b
  | .ref a, .ref b => compare a b
  | a, b => compare a.rank b.rank
instance : Ord Value := ⟨Value.cmp⟩
instance : TransOrd Value where
  eq_swap {a b} := by
    change Value.cmp a b = (Value.cmp b a).swap
    cases a <;> cases b <;> simp only [Value.cmp, Value.rank] <;>
      first | rfl | exact OrientedOrd.eq_swap
  isLE_trans {a b c} hab hbc := by
    change (Value.cmp a b).isLE at hab
    change (Value.cmp b c).isLE at hbc
    change (Value.cmp a c).isLE
    cases a <;> cases b <;> cases c <;> simp only [Value.cmp, Value.rank] at * <;>
      first | rfl | exact TransOrd.isLE_trans hab hbc | contradiction
instance : LawfulEqOrd Value where
  eq_of_compare {a b} h := by
    change Value.cmp a b = .eq at h
    cases a <;> cases b <;> simp only [Value.cmp, Value.rank] at h <;>
      first
        | rfl
        | contradiction
        | rw [LawfulEqOrd.eq_of_compare h]
def ALIAS : String := ("$alias")
inductive FieldKind where
  | plain
  | reference
  | owner
  deriving DecidableEq, Repr
structure Field where
  name : String
  kind : FieldKind
  strategy : Strategy
structure Schema where
  collection : String
  fields : List Field
def Schema.strategyOf (sc : Schema) (_collection field : String) : Strategy :=
  ((sc.fields.find? (·.name = field)).map (·.strategy)).getD .lww
def aliasOk (c : Change Value) : Bool :=
  if c.field = ALIAS then
    match c.value with
    | .ref t => t ≠ c.gid
    | _ => false
  else true
section Inputs
variable (sc : Schema) (cs : List (Change Value))
def step (st : State Value) (c : Change Value) : State Value :=
  if c.field = ALIAS then st else State.apply sc.strategyOf st c
def registers : State Value := cs.foldl (step sc) State.empty
def ours : List (Change Value) := cs.filter fun c => c.collection = sc.collection ∧ aliasOk c
def known : List Gid := gidSet ((ours sc cs).map (·.gid))
def aliasTarget (c : Change Value) : Option Gid :=
  if c.field = ALIAS then
    match c.value with
    | .ref t => if t ≠ c.gid then some t else none
    | _ => none
  else none
def edges : List Edge :=
  (ours sc cs).filterMap fun c =>
    match aliasTarget c with
    | some t => if t ∈ known sc cs then some (c.gid, t) else none
    | none => none
structure Inputs where
  registers : State Value
  gids : List Gid
  canon : Gid → Gid
def inputs : Inputs := ⟨registers sc cs, known sc cs, canonical (edges sc cs)⟩
end Inputs
section Present
variable (sc : Schema) (inp : Inputs)
def register (g : Gid) (field : String) : Option (Entry Value) :=
  inp.registers (sc.collection, g, field)
def deleted (g : Gid) : Prop :=
  ∃ e, register sc inp g DELETED = some e ∧ e.value = .int 1
def namesLive (live : Gid → Prop) (o : Gid) : Prop :=
  o ∈ inp.gids ∧ ∃ m ∈ inp.gids, inp.canon m = inp.canon o ∧ live m
def ownerAllows (live : Gid → Prop) : Option (Entry Value) → Prop
  | none => True
  | some e =>
    match e.value with
    | .null => True
    | .ref o => namesLive inp live o
    | _ => False
def liveAt : Nat → Gid → Prop
  | 0, _ => False
  | k + 1, g =>
    liveAt k g ∨
      (g ∈ inp.gids ∧ ¬ deleted sc inp g ∧
        ∀ f ∈ sc.fields, f.kind = .owner → ownerAllows inp (liveAt k) (register sc inp g f.name))
def Live (g : Gid) : Prop := ∃ k, liveAt sc inp k g
noncomputable def liveMembers (r : Gid) : List Gid :=
  inp.gids.filter fun m => decide (inp.canon m = r ∧ Live sc inp m)
noncomputable def groupEntry (f : Field) (r : Gid) : Option (Entry Value) :=
  ((liveMembers sc inp r).filterMap fun m => register sc inp m f.name).foldl (apply f.strategy) none
noncomputable def read (f : Field) : Option (Entry Value) → Value
  | none => .null
  | some e =>
    match f.kind with
    | .plain => e.value
    | .reference | .owner =>
      match e.value with
      | .ref o => if namesLive inp (Live sc inp) o then .ref (inp.canon o) else .null
      | _ => .null
abbrev Row := List (String × Value)
noncomputable def present (r : Gid) : Option Row :=
  if ∃ m ∈ inp.gids, inp.canon m = r ∧ Live sc inp m then
    some (sc.fields.map fun f => (f.name, read sc inp f (groupEntry sc inp f r)))
  else none
end Present
noncomputable def view (sc : Schema) (cs : List (Change Value)) : Gid → Option Row :=
  present sc (inputs sc cs)
end FongoSync


