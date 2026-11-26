-- Prove2me | Definitions.Def_bsv_merkle_counter
-- name    : bsv_merkle_counter
-- status  : Definition
-- author  : @GregoryJWard
-- created : 2026-11-26T14:27:49.30315+00:00
-- url     : https://prove2.me/theorems/1bb2d095-361d-563a-ad43-863f48fd4281
-- title:
--   Merkle root computation with one pending hash per level (slot model)
-- statement:
--   A model of the computation of a Merkle root that keeps one pending subtree hash per level, over an arbitrary combining function $H$.
--
--   The pending hashes form a list of *slots*, lowest level first; each slot is empty or holds a hash.
--
--   1. `insert` adds a hash at the lowest level: it fills the first slot if that is empty; if it holds $x$, it empties it and inserts $H(x, h)$ one level up (a binary increment with carries).
--   2. `counter` inserts the leaves of a list in order.
--   3. `carry`, started on the slots above a hash $h$: if no slot remains it returns $h$; at an occupied slot $x$ it replaces $h$ by $H(x,h)$ and moves up; at an empty slot it stops with $h$ if all higher slots are empty, and otherwise replaces $h$ by $H(h,h)$ and moves up.
--   4. `top` returns $h$ if all higher slots are empty, and otherwise carries $H(h,h)$.
--   5. `finish` skips the empty lowest slots and applies `top` at the first occupied one; it returns `none` if there is none.
--   6. `rootCS` is `finish` applied to the slots after all leaves have been inserted.
--
--   `pairs` combines the complete adjacent pairs of a list and drops an unpaired last element; `odd` returns that unpaired element if the length is odd.
--
--   **Formalization Note** This is a Lean model written for reasoning; nothing is claimed about any particular program.
-- source:
--   Gregory J. Ward, Bryan W. Daugherty, Shawn M. Ryan, BSV Lean proofs (Apache-2.0). https://github.com/codenlighten/bsv-lean-proofs

import Definitions.Def_bsv_merkle_tree
/-!
Authors: Gregory J. Ward, Bryan W. Daugherty, Shawn M. Ryan.
Source: https://github.com/codenlighten/bsv-lean-proofs (41c4bfd), Apache-2.0.
-/

namespace Bsv.Merkle

section

variable {α : Type} (H : α → α → α)

/-- Add one leaf (or a carried subtree hash) at the lowest level. -/
def insert (h : α) : List (Option α) → List (Option α)
  | [] => [some h]
  | none :: s => some h :: s
  | some x :: s => none :: insert (H x h) s

/-- The slots after all leaves of `l` have been added to `s`. -/
def counter (l : List α) (s : List (Option α)) : List (Option α) :=
  l.foldl (fun s h => insert H h s) s

/-- The inner loop of the sweep: `h` has just been combined with itself and is
carried up through occupied levels; at a free level it stops, and is combined
with itself again unless nothing is pending above. -/
def carry (h : α) : List (Option α) → α
  | [] => h
  | some x :: s => carry (H x h) s
  | none :: s => if s.all Option.isNone then h else carry (H h h) s

/-- The outer loop of the sweep, from a hash `h` at an occupied level. -/
def top (h : α) (s : List (Option α)) : α :=
  if s.all Option.isNone then h else carry H (H h h) s

/-- The sweep: start from the lowest occupied level. -/
def finish : List (Option α) → Option α
  | [] => none
  | none :: s => finish s
  | some h :: s => some (top H h s)

/-- The root as the computation with one pending hash per level produces it. -/
def rootCS (l : List α) : Option α := finish H (counter H l [])

/-- The complete pairs of a level. -/
def pairs : List α → List α
  | a :: b :: t => H a b :: pairs t
  | _ => []

/-- The unpaired last node of a level, if its length is odd. -/
def odd : List α → Option α
  | [] => none
  | [a] => some a
  | _ :: _ :: t => odd t

theorem length_pairs : ∀ l : List α, (pairs H l).length = l.length / 2
  | [] => by simp [pairs]
  | [_] => by simp [pairs]
  | _ :: _ :: t => by simp only [pairs, List.length_cons, length_pairs t]; omega

end

end Bsv.Merkle


