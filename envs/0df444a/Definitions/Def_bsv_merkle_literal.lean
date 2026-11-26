-- Prove2me | Definitions.Def_bsv_merkle_literal
-- name    : bsv_merkle_literal
-- status  : Definition
-- author  : @GregoryJWard
-- created : 2026-11-26T14:29:19.913015+00:00
-- url     : https://prove2.me/theorems/6c5ee567-c199-4be5-adcb-8622d574d19b
-- title:
--   Merkle computation with an array of pending hashes and a leaf counter
-- statement:
--   The Merkle computation using an array `inner`, modelled as a map from levels to hashes whose entries are never cleared, and a leaf counter `count`, here an unbounded natural number.
--
--   1. `bitClear` tests that bit `level` of the counter is zero.
--   2. Adding a leaf increments the counter, then, starting at level $0$ with the new leaf and while the bit at the current level is clear, combines the stored hash with the current one (recording whether they were equal) and moves up; the result is stored at the level reached.
--   3. The final sweep starts with the hash stored at the lowest set bit of the counter. While the counter is not $2^{\mathrm{level}}$, it combines the hash with itself, adds $2^{\mathrm{level}}$ to the counter, moves up, and combines with stored hashes while the bit is clear.
--   4. `rootLit` returns `none` for an empty list and otherwise the result of the sweep; `mutatedLit` returns the recorded flag.
--
--   `absFrom` is the list of slots that a pair (array, counter) stands for. The loops carry a step budget because Lean functions must terminate.
--
--   **Formalization Note** This is a Lean model written for reasoning; nothing is claimed about any particular program.
-- source:
--   Gregory J. Ward, Bryan W. Daugherty, Shawn M. Ryan, BSV Lean proofs (Apache-2.0). https://github.com/codenlighten/bsv-lean-proofs

import Definitions.Def_bsv_merkle_mutation
/-!
Authors: Gregory J. Ward, Bryan W. Daugherty, Shawn M. Ryan.
Source: https://github.com/codenlighten/bsv-lean-proofs (41c4bfd), Apache-2.0.
-/

namespace Bsv.Merkle

section

variable {α : Type} (H : α → α → α)

/-- `!(count & (1 << level))`. -/
def bitClear (count level : Nat) : Bool := count &&& (1 <<< level) == 0

/-- Slots from level `lvl` upward, where `q` is the count with its low `lvl`
bits dropped: slot `lvl + j` is `some (inner (lvl + j))` exactly when bit `j`
of `q` is set. -/
def absFrom (inner : Nat → α) (lvl q : Nat) : List (Option α) :=
  if h : q = 0 then []
  else (if q % 2 = 1 then some (inner lvl) else none) :: absFrom inner (lvl + 1) (q / 2)
termination_by q
decreasing_by omega

/-- `inner[level] = hash`. -/
def upd (inner : Nat → α) (level : Nat) (hash : α) : Nat → α :=
  fun k => if k = level then hash else inner k

section leaf

variable [DecidableEq α]

/-- The `while (!(count & (1 << level)))` loop of the leaf phase: returns the
level reached, the hash, and the mutation flag. -/
def leafCarry (inner : Nat → α) (count : Nat) : Nat → Nat → α → Bool → Nat × α × Bool
  | 0, level, h, m => (level, h, m)
  | fuel + 1, level, h, m =>
    if bitClear count level then
      leafCarry inner count fuel (level + 1) (H (inner level) h) (m || inner level == h)
    else (level, h, m)

/-- The state of the leaf phase. -/
structure Lit (α : Type) where
  inner : Nat → α
  count : Nat
  mutated : Bool

/-- One round of the leaf loop, with step budget `count + 1`. -/
def addLeaf (s : Lit α) (leaf : α) : Lit α :=
  let c := s.count + 1
  let r := leafCarry H s.inner c c 0 leaf s.mutated
  { inner := upd s.inner r.1 r.2.1, count := c, mutated := r.2.2 }

/-- The leaf phase over a whole list. -/
def runLeaves (s : Lit α) (l : List α) : Lit α := l.foldl (addLeaf H) s

end leaf

/-- `while (!(count & (1 << level))) level++`. -/
def skipLow (count : Nat) : Nat → Nat → Nat
  | 0, level => level
  | fuel + 1, level => if bitClear count level then skipLow count fuel (level + 1) else level

/-- The inner `while` of the sweep: combine with pending hashes while the bit
is clear. -/
def sweepInner (inner : Nat → α) (count : Nat) : Nat → Nat → α → Nat × α
  | 0, level, h => (level, h)
  | fuel + 1, level, h =>
    if bitClear count level then sweepInner inner count fuel (level + 1) (H (inner level) h)
    else (level, h)

/-- The outer `while (count != (1 << level))` of the sweep. `F` is the budget
handed to each run of the inner loop. -/
def sweepOuter (inner : Nat → α) (F : Nat) : Nat → Nat → Nat → α → α
  | 0, _, _, h => h
  | fuel + 1, count, level, h =>
    if count != 1 <<< level then
      let count' := count + 1 <<< level
      let r := sweepInner H inner count' F (level + 1) (H h h)
      sweepOuter inner F fuel count' r.1 r.2
    else h

section whole

variable [DecidableEq α] [Inhabited α]

/-- The state before any leaf: `count = 0`; the array's contents do not matter. -/
def start : Lit α := { inner := fun _ => default, count := 0, mutated := false }

/-- The root as the array-and-counter computation returns it (`none` for no
leaves). -/
def rootLit (l : List α) : Option α :=
  match l with
  | [] => none
  | _ =>
    let s := runLeaves H start l
    let F := s.count + 1
    let level := skipLow s.count F 0
    some (sweepOuter H s.inner F F s.count level (s.inner level))

/-- The flag of the array-and-counter computation. -/
def mutatedLit (l : List α) : Bool := (runLeaves H start l).mutated

end whole

end

end Bsv.Merkle


