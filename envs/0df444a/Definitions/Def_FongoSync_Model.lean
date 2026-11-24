-- Prove2me | Definitions.Def_FongoSync_Model
-- name    : FongoSync_Model
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-24T07:58:34.305955+00:00
-- url     : https://prove2.me/theorems/ae712b72-2466-4365-9e0a-1c4a12008ab2
-- title:
--   Model
-- statement:
--   Definitions and structural lemmas for Model, from bongofongo (bongofongo/fongo-sync; see pinned Apache-2.0 LICENSE-APACHE)'s pinned FongoSync local-first CRDT replication convergence laws development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/bongofongo/fongo-sync/blob/7e3f771e7c150a69dbbd87827b7ffe4525f219a7/FongoSync/Model.lean

import Definitions.Def_FongoSync_View
set_option autoImplicit false
namespace FongoSync.Full
open Std Classical FongoSync
set_option linter.unusedSectionVars false
inductive Kind where
  | plain
  | reference (target : String)
  | owner (target : String)
  deriving DecidableEq, Repr
structure Field where
  name : String
  kind : Kind
  strategy : Strategy
structure Collection where
  name : String
  fields : List Field
  together : List (List String)
  /-- The key fields of a natural collection; `none` for a collection of minted gids. -/
  natural : Option (List String)
structure Schema where
  collections : List Collection
  derive : String → List Value → Gid
def Schema.find (sc : Schema) (name : String) : Option Collection :=
  sc.collections.find? (·.name = name)
def Collection.declared (c : Collection) (field : String) : Option Field :=
  c.fields.find? (·.name = field)
def Collection.inTogether (c : Collection) (field : String) : Bool :=
  c.together.any (·.contains field)
def Schema.strategyOf (sc : Schema) (collection field : String) : Strategy :=
  match sc.find collection with
  | some c => ((c.declared field).map (·.strategy)).getD .lww
  | none => .lww
def Schema.Restricted (sc : Schema) : Prop :=
  (∀ c ∈ sc.collections, ∀ f ∈ c.fields, f.kind ≠ .owner c.name) ∧
  (∀ c ∈ sc.collections, ∀ set ∈ c.together, ∀ name ∈ set, ∀ f ∈ c.fields, f.name = name →
    f.strategy = .lww ∧ ∀ t, f.kind ≠ .owner t)
def candidates (sc : Schema) (cs : List (Change Value)) : List (Change Value) :=
  cs.filter fun c => decide c.clock.encodable && aliasOk c && (sc.find c.collection).isSome
def claimCmp (a b : Hlc × String) : Ordering :=
  compareLex (compareOn (·.1)) (compareOn (·.2)) a b
def claimFirst (a b : Hlc × String) : Ordering := claimCmp b a
def home (_sc : Schema) (cs : List (Change Value)) (g : Gid) : Option String :=
  (((cs.filter (·.gid = g)).map fun c => (c.clock, c.collection)).foldl
    (keep claimFirst id) none).map (·.2)
section Inputs
variable (sc : Schema) (cs : List (Change Value))
def claimed : List (Change Value) :=
  cs.filter fun c => home sc cs c.gid = some c.collection
def homeCollection (g : Gid) : Option Collection := (home sc cs g).bind sc.find
def Derives (g : Gid) (c : Collection) (fields : List String) (k : List Value) : Prop :=
  k.length = fields.length ∧
    (∀ p ∈ fields.zip k, ∃ x ∈ claimed sc cs, x.gid = g ∧ x.field = p.1 ∧ x.value = p.2) ∧
    sc.derive c.name k = g
noncomputable def key (g : Gid) : Option (List Value) :=
  match homeCollection sc cs g with
  | some c =>
    match c.natural with
    | some fields => if h : ∃ k, Derives sc cs g c fields k then some (Classical.choose h) else none
    | none => none
  | none => none
def Unverified (g : Gid) : Prop :=
  ∃ c fields, homeCollection sc cs g = some c ∧ c.natural = some fields ∧ key sc cs g = none
noncomputable def keyFieldOk (x : Change Value) : Prop :=
  match homeCollection sc cs x.gid with
  | some c =>
    match c.natural with
    | some fields =>
      match fields.findIdx? (· = x.field) with
      | some i => ∃ k, key sc cs x.gid = some k ∧ k[i]? = some x.value
      | none => True
    | none => True
  | none => True
noncomputable def accepted : List (Change Value) :=
  (claimed sc cs).filter fun x => decide (keyFieldOk sc cs x)
noncomputable def registers : State Value :=
  merged sc.strategyOf ((accepted sc cs).filter fun c => c.field ≠ ALIAS)
def gids : List Gid := gidSet ((claimed sc cs).map (·.gid))
noncomputable def edges : List Edge :=
  (accepted sc cs).filterMap fun c =>
    if c.field = ALIAS then
      match c.value with
      | .ref t =>
        if home sc cs t = some c.collection ∧ ¬ Unverified sc cs c.gid ∧ ¬ Unverified sc cs t then
          some (c.gid, t)
        else none
      | _ => none
    else none
def SameUnder (R : Gid → Gid → Prop) (v w : Value) : Prop :=
  v = w ∨ ∃ x y, v = .ref x ∧ w = .ref y ∧ R x y
def KeyPair (R : Gid → Gid → Prop) (a b : Gid) : Prop :=
  ∃ c fields, homeCollection sc cs a = some c ∧ c.natural = some fields ∧
    home sc cs b = home sc cs a ∧ ¬ Unverified sc cs a ∧ ¬ Unverified sc cs b ∧
    ∀ f ∈ fields, ∃ ea eb, registers sc cs (c.name, a, f) = some ea ∧
      registers sc cs (c.name, b, f) = some eb ∧ SameUnder R ea.value eb.value
inductive Joined (E : Gid → Gid → Prop) : Gid → Gid → Prop
  | refl (a : Gid) : Joined E a a
  | edge {a b : Gid} : E a b → Joined E a b
  | symm {a b : Gid} : Joined E a b → Joined E b a
  | trans {a b c : Gid} : Joined E a b → Joined E b c → Joined E a c
noncomputable def groupedAt : Nat → Gid → Gid → Prop
  | 0 => Joined fun a b => (a, b) ∈ edges sc cs
  | k + 1 => Joined fun a b => (a, b) ∈ edges sc cs ∨ KeyPair sc cs (groupedAt k) a b
def Grouped (a b : Gid) : Prop := ∃ k, groupedAt sc cs k a b
noncomputable def canon (g : Gid) : Gid :=
  ((List.range (g + 1)).find? fun h => decide (Grouped sc cs g h)).getD g
structure Inputs where
  registers : State Value
  home : Gid → Option String
  gids : List Gid
  canon : Gid → Gid
  unverified : Gid → Prop
noncomputable def inputs : Inputs :=
  ⟨registers sc cs, home sc cs, gids sc cs, canon sc cs, Unverified sc cs⟩
end Inputs
section Present
variable (sc : Schema) (inp : Inputs)
def register (g : Gid) (field : String) : Option (Entry Value) :=
  match inp.home g with
  | some c => inp.registers (c, g, field)
  | none => none
def deleted (g : Gid) : Prop :=
  ∃ e, register inp g DELETED = some e ∧ e.value = .int 1
def namesLive (live : Gid → Prop) (target : String) (o : Gid) : Prop :=
  inp.home o = some target ∧ ∃ m ∈ inp.gids, inp.canon m = inp.canon o ∧ live m
def ownerAllows (live : Gid → Prop) (target : String) : Option (Entry Value) → Prop
  | none => True
  | some e =>
    match e.value with
    | .null => True
    | .ref o => namesLive inp live target o
    | _ => False
def liveAt : Nat → Gid → Prop
  | 0, _ => False
  | k + 1, g =>
    liveAt k g ∨
      (g ∈ inp.gids ∧ ¬ inp.unverified g ∧ ¬ deleted inp g ∧
        ∃ c, (inp.home g).bind sc.find = some c ∧
          ∀ f ∈ c.fields, ∀ t, f.kind = .owner t →
            ownerAllows inp (liveAt k) t (register inp g f.name))
def Live (g : Gid) : Prop := ∃ k, liveAt sc inp k g
noncomputable def liveMembers (r : Gid) : List Gid :=
  inp.gids.filter fun m => decide (inp.canon m = r ∧ Live sc inp m)
noncomputable def read (f : Field) (v : Value) : Value :=
  match f.kind with
  | .plain => v
  | .reference t | .owner t =>
    match v with
    | .ref o => if namesLive inp (Live sc inp) t o then .ref (inp.canon o) else .null
    | _ => .null
noncomputable def plainValue (f : Field) (r : Gid) : Value :=
  match ((liveMembers sc inp r).filterMap fun m => register inp m f.name).foldl
      (apply f.strategy) none with
  | some e => read sc inp f e.value
  | none => .null
def latest (set : List String) (m : Gid) : Option Hlc :=
  (set.filterMap fun name => (register inp m name).map (·.clock)).foldl
    (fun best k => match best with
      | none => some k
      | some b => if b < k then some k else some b) none
noncomputable def setHolder (set : List String) (r : Gid) : Option (Hlc × Gid) :=
  (liveMembers sc inp r).foldl (fun best m =>
    match latest inp set m with
    | none => best
    | some at_ =>
      match best with
      | none => some (at_, m)
      | some (held, _) => if held < at_ then some (at_, m) else best) none
noncomputable def setValue (c : Collection) (set : List String) (name : String) (r : Gid) : Value :=
  match setHolder sc inp set r, c.declared name with
  | some (at_, m), some f =>
    match register inp m name with
    | some e => if e.clock = at_ then read sc inp f e.value else .null
    | none => .null
  | _, _ => .null
abbrev Row := List (String × Value)
noncomputable def row (c : Collection) (r : Gid) : Row :=
  (c.fields.filter fun f => !c.inTogether f.name).map (fun f => (f.name, plainValue sc inp f r)) ++
    c.together.flatMap fun set => set.map fun name => (name, setValue sc inp c set name r)
noncomputable def present (collection : String) (r : Gid) : Option Row :=
  match sc.find collection with
  | none => none
  | some c =>
    if inp.home r = some collection ∧ ∃ m ∈ inp.gids, inp.canon m = r ∧ Live sc inp m then
      some (row sc inp c r)
    else none
end Present
noncomputable def view (sc : Schema) (cs : List (Change Value)) : String → Gid → Option Row :=
  present sc (inputs sc (candidates sc cs))
instance : TransCmp claimCmp :=
  inferInstanceAs (TransCmp (compareLex (compareOn (fun p : Hlc × String => p.1))
    (compareOn (fun p : Hlc × String => p.2))))
instance : LawfulEqCmp claimCmp where
  eq_of_compare {a b} h := by
    simp only [claimCmp, compareLex_eq_eq, compareOn] at h
    exact Prod.ext (LawfulEqOrd.eq_of_compare h.1) (LawfulEqOrd.eq_of_compare h.2)
instance : TransCmp claimFirst := inferInstanceAs (TransCmp fun a b => claimCmp b a)
instance : LawfulEqCmp claimFirst := inferInstanceAs (LawfulEqCmp fun a b => claimCmp b a)
section Invariance
variable (sc : Full.Schema) {cs₁ cs₂ : List (Change Value)} (same : ∀ c, c ∈ cs₁ ↔ c ∈ cs₂)
include same
end Invariance
end FongoSync.Full


