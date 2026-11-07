-- Prove2me | Definitions.Def_DynSort_insertMax
-- name    : DynSort_insertMax
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T21:34:37.134703+00:00
-- url     : https://prove2.me/theorems/6d66071f-2709-4224-8af9-13c56f941d66
-- title:
--   Elementary moves: InsertMax, level-1 shifts, truncation
-- statement:
--   This module defines the elementary steps of the hole-routing operations.
--
--   1. **InsertMax of $\min X$ into $Y$.** The element in the first cell of the section $X$ (its minimum, by Claim 6) moves into the hole in the last cell of the section $Y$; the vacated cell becomes the hole. This is one element movement.
--   2. **Shift.** In a level-$1$ section, the elements following the hole move one position to the left, so that the hole reaches the last cell; each shifted element is one movement.
--   3. **Truncation.** By the Remark of p.15, an operation stops as soon as the hole has reached the last cell of the section it was called on, or of a section enclosing it.
--
--   **Formalization Note** If the first cell of $X$ holds no element or the last cell of $Y$ is not the hole, InsertMax does nothing; this never happens in the states of the claims.
-- source:
--   Azar, Bhore, Dey, Panigrahi, Vardi, Zhang, Online and Fully-Dynamic Sorting, STOC 2027 submission (manuscript sha256 da7f0d5ef6191ccaa6c70faec62234592c6d108cd2357bda3e5b6dac010acf6c), §4.4, p.14 (PDF p.16); Remark, p.15 (PDF p.17)

import Mathlib
import Definitions.Def_DynSort_rebuild

namespace DynSort

/-! # Elementary moves: InsertMax, shifting a level-1 section, and truncation

Y. Azar, S. Bhore, D. Dey, D. Panigrahi, O. Vardi, I. Zhang, *Online and Fully-Dynamic Sorting*,
STOC 2027 submission (manuscript sha256 da7f0d5e…), §4.4, p.14 (PDF p.16); Remark, p.15
(PDF p.17); §4.5, pp.16–21.

InsertMax (p.14): "Given a DST whose last position is a hole, and an element y larger than every
element currently stored in the DST, this operation places y in the hole." The operations of §4.5
use it as "move min X into the hole in Y using InsertMax". A level-1 step "shifts the elements" to
move the hole to the last position. Remark (p.15): "all the operation calls for which the hole has
already moved to the end of its DST are truncated".

**Formalization Note.**
* `insertMax src dst` moves the element in the first cell of the section at address `src` (its
  minimum, by Claim 6) into the last cell of the section at address `dst`, which must be the hole;
  the vacated cell becomes the hole. It counts one move (Claim 10). If the first cell of `src` is
  not an element or the last cell of `dst` is not the hole, nothing happens.
* `shiftToEnd a` moves the hole of the level-1 section at `a` to its last cell, shifting the
  elements after it one position to the left; it counts one move per shifted element.
* `done R a` holds when the section at `a` or one of its ancestors ends with the hole: the
  truncation rule of the Remark, read on the sections enclosing the current call.
-/

variable {α : Type}

namespace Sec

/-- Apply `f` to the cells of the first level-1 section with at least one cell. -/
def modFirst (f : List (Option α) → List (Option α)) : Sec α → Sec α
  | .leaf c => if c.isEmpty then .leaf c else .leaf (f c)
  | .single O => .single (O.modFirst f)
  | .three O1 T2 O2 O3 =>
    if O1.size ≠ 0 then .three (O1.modFirst f) T2 O2 O3
    else if T2.size ≠ 0 then .three O1 (T2.modFirst f) O2 O3
    else if O2.size ≠ 0 then .three O1 T2 (O2.modFirst f) O3
    else .three O1 T2 O2 (O3.modFirst f)

/-- Apply `f` to the cells of the last level-1 section with at least one cell. -/
def modLast (f : List (Option α) → List (Option α)) : Sec α → Sec α
  | .leaf c => if c.isEmpty then .leaf c else .leaf (f c)
  | .single O => .single (O.modLast f)
  | .three O1 T2 O2 O3 =>
    if O3.size ≠ 0 then .three O1 T2 O2 (O3.modLast f)
    else if O2.size ≠ 0 then .three O1 T2 (O2.modLast f) O3
    else if T2.size ≠ 0 then .three O1 (T2.modLast f) O2 O3
    else .three (O1.modLast f) T2 O2 O3

/-- The section ends with the hole. -/
def endsInHole (S : Sec α) : Bool :=
  match S.flat.getLast? with
  | some none => true
  | _ => false

end Sec

/-- **InsertMax of `min src`** (p.14): move the element in the first cell of the section at `src`
into the hole in the last cell of the section at `dst`; one move. -/
def insertMax (src dst : List ℕ) (st : St α) : St α :=
  match st.root.get src, st.root.get dst with
  | some S, some D =>
    match S.flat.head?, D.flat.getLast? with
    | some (some y), some none =>
      let r1 := st.root.modify (Sec.modFirst (fun c => none :: c.tail)) src
      let r2 := r1.modify (Sec.modLast (fun c => c.dropLast ++ [some y])) dst
      { root := r2, ctr := { st.ctr with moves := st.ctr.moves + 1 } }
    | _, _ => st
  | _, _ => st

/-- Shift the elements following the hole of the level-1 section at `a` one position to the left,
moving the hole to its last cell; one move per shifted element. -/
def shiftToEnd (a : List ℕ) (st : St α) : St α :=
  match st.root.get a with
  | some (.leaf c) =>
    match c.findIdx? Option.isNone with
    | some k =>
      { root := st.root.modify (fun _ => .leaf (c.eraseIdx k ++ [none])) a,
        ctr := { st.ctr with moves := st.ctr.moves + (c.length - k - 1) } }
    | none => st
  | _ => st

/-- The truncation test (Remark, p.15): the section at `a`, or a section enclosing it, ends with
the hole. -/
def done (R : Sec α) (a : List ℕ) : Bool :=
  (List.range (a.length + 1)).any (fun k =>
    match R.get (a.take k) with
    | some S => S.endsInHole
    | none => false)

end DynSort


