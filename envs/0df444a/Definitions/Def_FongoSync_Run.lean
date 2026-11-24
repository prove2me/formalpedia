-- Prove2me | Definitions.Def_FongoSync_Run
-- name    : FongoSync_Run
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-24T07:58:33.845763+00:00
-- url     : https://prove2.me/theorems/f22cfe29-cd2f-4496-b17a-d8ea4b3fd042
-- title:
--   Run
-- statement:
--   Definitions and structural lemmas for Run, from bongofongo (bongofongo/fongo-sync; see pinned Apache-2.0 LICENSE-APACHE)'s pinned FongoSync local-first CRDT replication convergence laws development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/bongofongo/fongo-sync/blob/7e3f771e7c150a69dbbd87827b7ffe4525f219a7/FongoSync/Run.lean

import Definitions.Def_FongoSync_View
set_option autoImplicit false
namespace FongoSync
open Classical
section Run
variable (sc : Schema) (inp : Inputs)
def rule (live : Gid → Prop) (g : Gid) : Prop :=
  g ∈ inp.gids ∧ ¬ deleted sc inp g ∧
    ∀ f ∈ sc.fields, f.kind = .owner → ownerAllows inp live (register sc inp g f.name)
noncomputable def liveCount (k : Nat) : Nat :=
  (inp.gids.filter fun g => decide (liveAt sc inp k g)).length
def deletedB (g : Gid) : Bool :=
  match register sc inp g DELETED with
  | some e => e.value == .int 1
  | none => false
def namesLiveB (live : Gid → Bool) (o : Gid) : Bool :=
  inp.gids.contains o && inp.gids.any fun m => inp.canon m == inp.canon o && live m
def ownerAllowsB (live : Gid → Bool) : Option (Entry Value) → Bool
  | none => true
  | some e =>
    match e.value with
    | .null => true
    | .ref o => namesLiveB inp live o
    | _ => false
def liveB : Nat → Gid → Bool
  | 0, _ => false
  | k + 1, g =>
    liveB k g ||
      (inp.gids.contains g && !deletedB sc inp g &&
        sc.fields.all fun f => f.kind != .owner || ownerAllowsB inp (liveB k) (register sc inp g f.name))
def liveNow (g : Gid) : Bool := liveB sc inp inp.gids.length g
def liveMembersR (r : Gid) : List Gid :=
  inp.gids.filter fun m => inp.canon m == r && liveNow sc inp m
def groupEntryR (f : Field) (r : Gid) : Option (Entry Value) :=
  ((liveMembersR sc inp r).filterMap fun m => register sc inp m f.name).foldl (apply f.strategy) none
def readR (f : Field) : Option (Entry Value) → Value
  | none => .null
  | some e =>
    match f.kind with
    | .plain => e.value
    | .reference | .owner =>
      match e.value with
      | .ref o => if namesLiveB inp (liveNow sc inp) o then .ref (inp.canon o) else .null
      | _ => .null
def presentR (r : Gid) : Option Row :=
  if inp.gids.any fun m => inp.canon m == r && liveNow sc inp m then
    some (sc.fields.map fun f => (f.name, readR sc inp f (groupEntryR sc inp f r)))
  else none
end Run
def runView (sc : Schema) (cs : List (Change Value)) : Gid → Option Row :=
  presentR sc (inputs sc cs)
example :
    let sc : Schema := ⟨"things", [⟨"title", .plain, .lww⟩]⟩
    let cs : List (Change Value) :=
      [⟨"things", 1, "title", .text "a", ⟨1, 0, 9⟩⟩,
       ⟨"things", 2, "title", .text "b", ⟨2, 0, 9⟩⟩,
       ⟨"things", 2, ALIAS, .ref 1, ⟨3, 0, 9⟩⟩]
    runView sc cs 1 = some [("title", .text "b")] ∧ runView sc cs 2 = none := by
  decide
end FongoSync


