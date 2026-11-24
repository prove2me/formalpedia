-- Prove2me | Definitions.Def_FongoSync_Alias
-- name    : FongoSync_Alias
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-24T07:57:07.447498+00:00
-- url     : https://prove2.me/theorems/b49c967b-cecb-439e-a7da-5bd61dc5e971
-- title:
--   Alias
-- statement:
--   Definitions and structural lemmas for Alias, from bongofongo (bongofongo/fongo-sync; see pinned Apache-2.0 LICENSE-APACHE)'s pinned FongoSync local-first CRDT replication convergence laws development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/bongofongo/fongo-sync/blob/7e3f771e7c150a69dbbd87827b7ffe4525f219a7/FongoSync/Alias.lean

import Definitions.Def_FongoSync_Clock
set_option autoImplicit false
namespace FongoSync
abbrev Edge := Gid × Gid
inductive Connected (E : List Edge) : Gid → Gid → Prop
  | refl (a : Gid) : Connected E a a
  | edge {a b : Gid} : (a, b) ∈ E → Connected E a b
  | symm {a b : Gid} : Connected E a b → Connected E b a
  | trans {a b c : Gid} : Connected E a b → Connected E b c → Connected E a c
def IsCanonical (E : List Edge) (g r : Gid) : Prop :=
  Connected E g r ∧ ∀ h, Connected E g h → r ≤ h
def union (label : Gid → Gid) (e : Edge) : Gid → Gid :=
  let ra := label e.1
  let rb := label e.2
  fun g => if label g = ra ∨ label g = rb then min ra rb else label g
def canonical (E : List Edge) : Gid → Gid :=
  E.foldl union id
section Step
variable {P : List Edge} {L : Gid → Gid} (inv : ∀ g, IsCanonical P g (L g))
include inv
end Step
end FongoSync


