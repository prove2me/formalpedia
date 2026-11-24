-- Prove2me | Definitions.Def_FongoSync_Clock
-- name    : FongoSync_Clock
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-24T07:56:41.96647+00:00
-- url     : https://prove2.me/theorems/7302cfd6-6a39-4e66-bc09-2af2f2c2d275
-- title:
--   Clock
-- statement:
--   Definitions and structural lemmas for Clock, from bongofongo (bongofongo/fongo-sync; see pinned Apache-2.0 LICENSE-APACHE)'s pinned FongoSync local-first CRDT replication convergence laws development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/bongofongo/fongo-sync/blob/7e3f771e7c150a69dbbd87827b7ffe4525f219a7/FongoSync/Clock.lean

set_option autoImplicit false
namespace FongoSync
abbrev Gid := Nat
structure Hlc where
  wall : Nat
  counter : Nat
  node : Gid
  deriving DecidableEq, Repr
def Hlc.cmp (a b : Hlc) : Ordering :=
  (compare a.wall b.wall).then ((compare a.counter b.counter).then (compare a.node b.node))
instance : Ord Hlc := ⟨Hlc.cmp⟩
instance : LT Hlc := ltOfOrd
instance : LE Hlc := leOfOrd
instance : Std.TransOrd Hlc :=
  inferInstanceAs <| Std.TransCmp
    (compareLex (compareOn Hlc.wall) (compareLex (compareOn Hlc.counter) (compareOn Hlc.node)))
instance : Std.LawfulEqOrd Hlc where
  eq_of_compare {a b} h := by
    change Hlc.cmp a b = .eq at h
    simp only [Hlc.cmp, Ordering.then_eq_eq, Nat.compare_eq_eq] at h
    cases a; cases b
    simp_all
theorem Hlc.lt_iff {a b : Hlc} :
    a < b ↔ a.wall < b.wall ∨ a.wall = b.wall ∧
      (a.counter < b.counter ∨ a.counter = b.counter ∧ a.node < b.node) := by
  change Hlc.cmp a b = .lt ↔ _
  simp only [Hlc.cmp, Ordering.then_eq_lt, Nat.compare_eq_lt, Nat.compare_eq_eq]
instance : DecidableRel (α := Hlc) (· < ·) := fun _ _ =>
  decidable_of_iff _ Hlc.lt_iff.symm
def WALL_MAX : Nat := 0xFFFF_FFFF_FFFF
def COUNTER_MAX : Nat := 0xFFFF_FFFF
structure Clock where
  last : Hlc
  deriving DecidableEq, Repr
def Clock.tick (c : Clock) (wall : Nat) : Hlc × Clock :=
  let wall := min wall WALL_MAX
  let last :=
    if wall > c.last.wall then
      { c.last with wall := wall, counter := 0 }
    else if c.last.counter + 1 ≤ COUNTER_MAX then
      { c.last with counter := c.last.counter + 1 }
    else
      { c.last with wall := c.last.wall + 1, counter := 0 }
  (last, ⟨last⟩)
def Hlc.encodable (h : Hlc) : Prop := h.wall ≤ WALL_MAX
instance (h : Hlc) : Decidable h.encodable := inferInstanceAs (Decidable (h.wall ≤ WALL_MAX))
def Clock.observe (c : Clock) (remote : Hlc) : Clock :=
  if remote.encodable ∧
      (remote.wall > c.last.wall ∨ remote.wall = c.last.wall ∧ remote.counter > c.last.counter) then
    ⟨{ c.last with wall := remote.wall, counter := remote.counter }⟩
  else
    c
def Hlc.Before (a b : Hlc) : Prop :=
  a.wall < b.wall ∨ a.wall = b.wall ∧ a.counter < b.counter
def Hlc.NotAfter (a b : Hlc) : Prop :=
  a.wall < b.wall ∨ a.wall = b.wall ∧ a.counter ≤ b.counter
inductive Event where
  | tick (wall : Nat)
  | observe (remote : Hlc)
def Clock.run (c : Clock) : List Event → Clock × List Hlc
  | [] => (c, [])
  | .tick wall :: rest =>
    let (reading, c') := c.tick wall
    let (final, seen) := c'.run rest
    (final, reading :: seen)
  | .observe remote :: rest =>
    let (final, seen) := (c.observe remote).run rest
    (final, if remote.encodable then remote :: seen else seen)
end FongoSync


