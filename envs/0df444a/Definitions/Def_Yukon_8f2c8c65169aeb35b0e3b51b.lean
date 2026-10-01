-- Prove2me | Definitions.Def_Yukon_8f2c8c65169aeb35b0e3b51b
-- name    : Yukon_8f2c8c65169aeb35b0e3b51b
-- status  : Definition
-- author  : @yukon
-- created : 2026-09-30T15:43:19.810427+00:00
-- url     : https://prove2.me/theorems/80a4a315-1545-4898-a75d-cc22401f7726
-- title:
--   Generic collection slices
-- statement:
--   Slice classes and Array/List instances from the pinned ArkLib source. Equivalent declarative notation replaces custom parser rules; display-only unexpanders are omitted. Mathematical definitions are unchanged.
-- source:
--   https://github.com/Verified-zkEVM/ArkLib/blob/e65197892890b8fd9b0dc05b8980273cf1d595cc/ArkLib/Data/Classes/Slice.lean
--
--   yukon-proof-operation:8f2c8c65169aeb35b0e3b51b64c75b3b37cb6541c5db4a0861ba9cbe1b5ceb72
--   [yukon-proof-receipt:eyJ2IjoxLCJtYXJrZXIiOiJ5dWtvbi1wcm9vZi1vcGVyYXRpb246OGYyYzhjNjUxNjlhZWIzNWIwZTNiNTFiNjRjNzViM2IzN2NiNjU0MWM1ZGI0YTA4NjFiYTljYmUxYjVjZWI3MiIsImhhc2giOiI1NGQyMzQ0ZTkyOWVlZGYxNDBhMGRlNGFhMTBkMzUwMWNjYThjN2M1ZDZhYjVmZmZlNzM2NjI4NjUxZWI5Y2U4Iiwia2luZCI6ImRlZmluaXRpb24iLCJ0YXJnZXQiOiJZdWtvbl84ZjJjOGM2NTE2OWFlYjM1YjBlM2I1MWIiLCJlbnZpcm9ubWVudCI6eyJtYXRobGliUmV2IjoiMGRmNDQ0YTM2MGVhYTYwYWI4YzExZGNhNTFhODZhZjY5Mjk1NTQ3NCIsInRvb2xjaGFpbiI6ImxlYW5wcm92ZXIvbGVhbjQ6djQuMzMuMSJ9LCJ0YWciOiJiZXR0ZXItY29kZXMifQ]

/-
Copyright (c) 2024-2025 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/


import Init
set_option backward.isDefEq.respectTransparency.types false
/-!
# Generic Slice Type Classes

This file defines type classes for slicing operations on collections, inspired by
Python's slice notation.
The notation provides three operations:
- `v⟦:m⟧` takes the first `m` elements (via `SliceLT`)
- `v⟦m:⟧` drops the first `m` elements (via `SliceGE`)
- `v⟦m₁:m₂⟧` takes elements from index `m₁` to `m₂ - 1` (via `Slice`)

Each notation also supports manual proof syntax with `'h`:
- `v⟦:m⟧'h` for explicit proof in `SliceLT`
- `v⟦m:⟧'h` for explicit proof in `SliceGE`
- `v⟦m₁:m₂⟧'h` for explicit proof in `Slice`

The design follows the pattern of `GetElem` from the standard library, with:
- `outParam` annotations for better type inference
- Validity predicates that can be automatically proven by tactics like `omega`
- Dependent types where the result collection type can depend on all parameters

## Type Classes

- `SliceLT`: For "take first n elements" operations
- `SliceGE`: For "drop first n elements" operations
- `Slice`: For "range slice" operations

The type classes are generic and can be implemented for any collection type. This file provides
instances for:
- **Fin tuples**: Available in `ArkLib.Data.Fin.Tuple.Notation` (with proof obligations)
- **Array**: With `True` validity (no proof obligations needed)
- **List**: With `True` validity (no proof obligations needed)
-/

universe u v v' w

/-! ## Sliceable type classes -/

/-- Type class for "take first n elements" operations: `v⟦:m⟧`

We allow for the final subcollection type `subcoll` to depend on all prior parameters: the
collection type `coll`, the stop index type `stop`, the validity predicate `valid`. -/
class SliceLT (coll : Type u) (stop : Type v) (valid : outParam (coll → stop → Prop))
    (subcoll : outParam ((xs : coll) → (stop : stop) → (h : valid xs stop) → Type w)) where
  sliceLT : (xs : coll) → (stop : stop) → (h : valid xs stop) → subcoll xs stop h

/-- Type class for "drop first n elements" operations: `v⟦m:⟧`

We allow for the final subcollection type `subcoll` to depend on all prior parameters: the
collection type `coll`, the start index type `start`, the validity predicate `valid`. -/
class SliceGE (coll : Type u) (start : Type v) (valid : outParam (coll → start → Prop))
    (subcoll : outParam ((xs : coll) → (start : start) → (h : valid xs start) → Type w)) where
  sliceGE : (xs : coll) → (start : start) → (h : valid xs start) → subcoll xs start h

/-- Type class for "slice range" operations: `v⟦m₁:m₂⟧`

We allow for the final subcollection type `subcoll` to depend on all prior parameters: the
collection type `coll`, the start index type `start`, the stop index type `stop`, the
validity predicate `valid`. -/
class Slice (coll : Type u) (start : Type v) (stop : Type v')
    (valid : outParam (coll → start → stop → Prop))
    (subcoll : outParam ((xs : coll) → (start : start) → (stop : stop) →
        (h : valid xs start stop) → Type w)) where
  slice : (xs : coll) → (start : start) → (stop : stop) →
          (h : valid xs start stop) → subcoll xs start stop h

/-! ## Slice notation

Note: currently we use `get_elem_tactic` to automatically prove the validity of the indices.
We should switch to a more tailored tactic in the future. -/

/-- Notation `v⟦:stop⟧` for taking the first `stop` elements
(indexed from `0` to `stop - 1`) of a collection, assuming the validity for `stop` can be
automatically proven -/
notation:max (name := sliceLTNotation) v "⟦" ":" stop "⟧" => SliceLT.sliceLT v stop (by get_elem_tactic)

/-- Notation `v⟦:stop⟧'h` for taking the first `stop` elements
(indexed from `0` to `stop - 1`) with explicit proof -/
notation (name := sliceLTNotationWithProof) v "⟦" ":" stop "⟧'" h:max => SliceLT.sliceLT v stop h

/-- Notation `v⟦start:⟧` for dropping the first `start` elements of a collection, assuming the
validity for `start` can be automatically proven -/
notation:max (name := sliceGENotation) v "⟦" start ":" "⟧" => SliceGE.sliceGE v start (by get_elem_tactic)

/-- Notation `v⟦start:⟧'h` for dropping the first `start` elements with explicit proof -/
notation (name := sliceGENotationWithProof) v "⟦" start ":" "⟧'" h:max => SliceGE.sliceGE v start h

/-- Notation `v⟦start:stop⟧` for taking elements from index `start` to `stop - 1`
(e.g., `v⟦1:3⟧ = v[1] ++ v[2]`), with range proofs automatically synthesized -/
notation:max (name := sliceNotation) v "⟦" start ":" stop "⟧" => Slice.slice v start stop (by get_elem_tactic)

/-- Notation `v⟦start:stop⟧'h` for taking elements from index `start` to `stop - 1`
(e.g., `v⟦1:3⟧ = ![v 1, v 2]`), with explicit proof -/
notation (name := sliceNotationWithProof) v "⟦" start ":" stop "⟧'" h:max => Slice.slice v start stop h

/-! ## Instances for Array

Arrays support slice notation with no proof obligations since Array operations handle
boundary cases gracefully (e.g., taking more elements than exist returns the whole array).
-/

instance  _root_.instSliceLTArrayNatTrue {α : Type u} : SliceLT (Array α) Nat (fun _ _ => True) (fun _ _ _ => Array α) where
  sliceLT xs stop _ := xs.take stop

instance  _root_.instSliceGEArrayNatTrue {α : Type u} : SliceGE (Array α) Nat (fun _ _ => True) (fun _ _ _ => Array α) where
  sliceGE xs start _ := xs.drop start

instance  _root_.instSliceArrayNatTrue {α : Type u} : Slice (Array α) Nat Nat (fun _ _ _ => True) (fun _ _ _ _ => Array α) where
  slice xs start stop _ := xs.extract start stop

/-! ## Instances for List

Lists support slice notation with no proof obligations since List operations handle
boundary cases gracefully (e.g., taking more elements than exist returns the whole list).
-/

instance  _root_.instSliceLTListNatTrue {α : Type u} : SliceLT (List α) Nat (fun _ _ => True) (fun _ _ _ => List α) where
  sliceLT xs stop _ := List.take stop xs

instance  _root_.instSliceGEListNatTrue {α : Type u} : SliceGE (List α) Nat (fun _ _ => True) (fun _ _ _ => List α) where
  sliceGE xs start _ := List.drop start xs

instance  _root_.instSliceListNatTrue {α : Type u} : Slice (List α) Nat Nat (fun _ _ _ => True) (fun _ _ _ _ => List α) where
  slice xs start stop _ := xs.extract start stop

/-! ## Examples -/

-- #eval #[0, 1, 2, 3, 4]⟦:3⟧        -- #[0, 1, 2]
-- #eval #[0, 1, 2, 3, 4]⟦2:⟧        -- #[2, 3, 4]
-- #eval #[0, 1, 2, 3, 4]⟦1:4⟧       -- #[1, 2, 3]

-- -- List examples
-- #eval [0, 1, 2, 3, 4]⟦:3⟧         -- [0, 1, 2]
-- #eval [0, 1, 2, 3, 4]⟦2:⟧         -- [2, 3, 4]
-- #eval [0, 1, 2, 3, 4]⟦1:4⟧        -- [1, 2, 3]


