-- Prove2me | Definitions.Def_CLRS_Chapter4_Algo2LeanLib_MatrixHeap
-- name    : CLRS_Chapter4_Algo2LeanLib_MatrixHeap
-- status  : Definition
-- author  : @Chutong
-- created : 2026-10-11T05:02:28.372642+00:00
-- url     : https://prove2.me/theorems/a97cd580-2396-48bb-87db-37944aee5189
-- title:
--   Nested-matrix storage, preservation, and fresh-row contracts
-- statement:
--   A matrix value is an integer-indexed function of two integer indices. Stored connects such values to a valid outer-array reference whose row reference is allocated at every integer row index. Extends preserves every previously allocated row, outer array, and object. FreshRows requires fresh allocated rows throughout a specified finite square and distinct references for distinct finite row indices. Inputs may alias consistently; finite output-row distinctness is an additional property and is not implied by equality of matrix values.
--
--   **Formalization Note.** This content is transcribed from Algo2Lean development snapshot `fd33cf959b39f9e4a9fcfda4ef31d5a36b784d41`, with explicit platform import and namespace adaptation. It is not attributed to public compiler v0.1.4. The submitted definition bundle must be checked without unfinished-proof assumptions.
-- source:
--   Algo2Lean Chapter 4 development, module Algo2LeanLib.MatrixHeap, immutable source fd33cf959b39f9e4a9fcfda4ef31d5a36b784d41: https://github.com/chutongyang98/Lean_formalization/blob/fd33cf959b39f9e4a9fcfda4ef31d5a36b784d41/Algo2LeanLib/MatrixHeap.lean

import Definitions.Def_CLRS_Chapter4_Algo2Lean
import Std

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

namespace CLRS

/-! Heap views shared by the array-of-arrays matrix examples. Input rows may
alias. Preservation concerns every allocated input object, not just the two
outer array references. Counter changes are stated separately by each program. -/

namespace Algo2LeanCore.MatrixHeap

open Algo2LeanGenerated

abbrev Values := Int → Int → Int

/-- The canonical element descriptor emitted for `Seq[Seq[Int]]`. -/
def rows : SequenceType SeqRef where
  name := "Seq[Int]"
  encode := ObjectValue.seqValue
  decode := ObjectValue.asSeq
  decode_encode := by intro value; rfl

/-- A well-formed outer array and its mathematical row values. Row references
need not be distinct; this includes shared rows and aliased input matrices. -/
def Stored (h : Heap) (matrix : CollectionRef) (values : Values) : Prop :=
  rows.valid h matrix ∧ ∀ i, ∃ row,
    rows.get h matrix i = some row ∧ row < h.nextRef ∧ h.store row = values i

/-- Observe one nested matrix entry. `Stored` hypotheses guarantee that the
outer and row references are valid, so the decoder fallback is never used. -/
def cell (h : Heap) (matrix : CollectionRef) (i j : Int) : Int :=
  h.read ((rows.get h matrix i).getD 0) j

/-- Old arrays, rows, and objects survive unchanged while fresh arrays/rows may
be allocated. Clocks can change, and are specified independently. -/
structure Extends (before after : Heap) : Prop where
  nextRef : before.nextRef ≤ after.nextRef
  nextCollection : before.nextCollection ≤ after.nextCollection
  store : ∀ r, r < before.nextRef → after.store r = before.store r
  collections : ∀ r, r < before.nextCollection → after.collections r = before.collections r
  nextObject : after.nextObject = before.nextObject
  objects : after.objects = before.objects

theorem Extends.refl (h : Heap) : Extends h h :=
  ⟨Nat.le_refl _, Nat.le_refl _, fun _ _ => rfl, fun _ _ => rfl, rfl, rfl⟩









theorem Stored.row {h : Heap} {matrix : CollectionRef} {values : Values}
    (stored : Stored h matrix values) (i : Int) :
    (rows.get h matrix i).isSome = true := by
  obtain ⟨row, read, _⟩ := stored.2 i
  simp [read]

theorem Stored.row_valid {h : Heap} {matrix : CollectionRef} {values : Values}
    (stored : Stored h matrix values) (i : Int) :
    (rows.get h matrix i).getD 0 < h.nextRef := by
  obtain ⟨row, read, valid, _⟩ := stored.2 i
  simpa [read] using valid

theorem Stored.read {h : Heap} {matrix : CollectionRef} {values : Values}
    (stored : Stored h matrix values) (i j : Int) :
    h.read ((rows.get h matrix i).getD 0) j = values i j := by
  obtain ⟨row, read, _, contents⟩ := stored.2 i
  simp [read, Heap.read, contents]

theorem Stored.unique {h : Heap} {matrix : CollectionRef} {a b : Values}
    (first : Stored h matrix a) (second : Stored h matrix b) : a = b := by
  funext i j
  exact (first.read i j).symm.trans (second.read i j)

theorem Stored.cell {h : Heap} {matrix : CollectionRef} {values : Values}
    (stored : Stored h matrix values) (i j : Int) : cell h matrix i j = values i j :=
  stored.read i j

theorem extends_allocate (h : Heap) (values : Seq) : Extends h (h.allocate values) := by
  refine ⟨by simp, Nat.le_refl _, ?_, fun _ _ => rfl, rfl, rfl⟩
  intro r valid
  simp [Heap.allocate, Nat.ne_of_lt valid]

theorem extends_create (h : Heap) (values : Int → SeqRef) : Extends h (rows.create h values).1 := by
  refine ⟨Nat.le_refl _, by simp [SequenceType.create, Heap.createSequence],
    fun _ _ => rfl, ?_, rfl, rfl⟩
  intro r valid
  simp [SequenceType.create, Heap.createSequence, valid]

theorem extends_const (h : Heap) (row : SeqRef) : Extends h (rows.const h row).1 :=
  extends_create h (fun _ => row)

theorem extends_tick (h : Heap) (clock : String) (amount : Nat) : Extends h (h.tick clock amount) :=
  ⟨Nat.le_refl _, Nat.le_refl _, fun _ _ => rfl, fun _ _ => rfl, rfl, rfl⟩









@[simp] theorem rows_get_tick (h : Heap) (matrix : CollectionRef) (i : Int)
    (clock : String) (amount : Nat) :
    rows.get (h.tick clock amount) matrix i = rows.get h matrix i := rfl

@[simp] theorem rows_valid_tick (h : Heap) (matrix : CollectionRef)
    (clock : String) (amount : Nat) :
    rows.valid (h.tick clock amount) matrix ↔ rows.valid h matrix := Iff.rfl

@[simp] theorem rows_get_allocate (h : Heap) (matrix : CollectionRef) (i : Int) (values : Seq) :
    rows.get (h.allocate values) matrix i = rows.get h matrix i := rfl

@[simp] theorem rows_valid_allocate (h : Heap) (matrix : CollectionRef) (values : Seq) :
    rows.valid (h.allocate values) matrix ↔ rows.valid h matrix := Iff.rfl

@[simp] theorem rows_get_write (h : Heap) (matrix : CollectionRef) (i : Int)
    (row : SeqRef) (j value : Int) :
    rows.get (h.write row j value) matrix i = rows.get h matrix i := rfl

@[simp] theorem rows_valid_write (h : Heap) (matrix : CollectionRef)
    (row : SeqRef) (j value : Int) :
    rows.valid (h.write row j value) matrix ↔ rows.valid h matrix := Iff.rfl

/-- Every finite output row is freshly allocated, valid, and has its own identity. -/
def FreshRows (before after : Heap) (matrix : CollectionRef) (n : Nat) : Prop :=
  (∀ i : Nat, i < n → ∃ row, rows.get after matrix i = some row ∧
    before.nextRef ≤ row ∧ row < after.nextRef) ∧
  (∀ i j : Nat, i < n → j < n → rows.get after matrix i = rows.get after matrix j → i = j)



end Algo2LeanCore.MatrixHeap

end CLRS


