-- Prove2me | Definitions.Def_Algo2LeanLib_HeapFrame
-- name    : Algo2LeanLib_HeapFrame
-- status  : Definition
-- author  : @lunjia
-- created : 2026-10-10T23:39:11.295544+00:00
-- url     : https://prove2.me/theorems/ce36cb88-180f-4c1a-8481-44e241a2e104
-- title:
--   Mutable heap preservation and allocation frames
-- statement:
--   This bundle supplies common descriptions of the heap locations preserved by an operation. It separates integer sequence storage, object storage and typed collections, together with their allocation counters. Local frame facts support composing mutable calls while retaining the caller's unrelated data.
--
--   Frame predicates state preservation obligations; the algorithm and data-structure contracts prove that their actual executions satisfy them.
--
--   <!-- algo2lean-provenance-v0.1.4 -->
--   **[Algo2Lean](https://www.algo2lean.com/) provenance and reproduction.** These definitions target [Algo2Lean](https://www.algo2lean.com/) v0.1.4, using the compiler source at [public commit `0f79d5e4242e6477531c9ee4410409f5b1c92f76`](https://github.com/lunjiah/algo2lean/tree/0f79d5e4242e6477531c9ee4410409f5b1c92f76), and Lean 4.33.1. The versioned compiler location is [Algo2Lean v0.1.4](https://www.algo2lean.com/versions/v0.1.4/). Compile all supplied `.algo` files and imports to reproduce the raw generated definitions. Release publication and exact website parity require their separately recorded checks; this metadata alone does not assert them. Prove2Me imports and declaration packaging are mechanically adapted, with original hashes, compiler-reported source ranges, and adaptations recorded in transplant provenance. Exact reproduction does not prove the compiler correct.
-- source:
--   https://github.com/lunjiah/algo2lean/blob/0f79d5e4242e6477531c9ee4410409f5b1c92f76/Algo2LeanLib/HeapFrame.lean

import Definitions.Def_Algo2Lean

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true



set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

namespace Algo2LeanGenerated

/-- A local storage footprint: only the listed sequences and objects may change.
    Allocation, classes, and object collections stay fixed. Clocks are handled by
    a separate cost contract, so the same frame applies to every cost model. -/
structure Heap.Modifies (before after : Heap) (sequences : List SeqRef)
    (objects : List ObjectRef) : Prop where
  nextRef : after.nextRef = before.nextRef
  nextObject : after.nextObject = before.nextObject
  nextCollection : after.nextCollection = before.nextCollection
  collections : after.collections = before.collections
  classes : after.objectClass = before.objectClass
  otherSequences : ∀ ref, ref ∉ sequences → after.store ref = before.store ref
  otherObjects : ∀ ref, ref ∉ objects → after.objects ref = before.objects ref

namespace Heap.Modifies

theorem refl (heap : Heap) (sequences : List SeqRef) (objects : List ObjectRef) :
    heap.Modifies heap sequences objects :=
  ⟨rfl, rfl, rfl, rfl, rfl, fun _ _ => rfl, fun _ _ => rfl⟩

theorem trans {before middle after : Heap} {sequences : List SeqRef} {objects : List ObjectRef}
    (first : before.Modifies middle sequences objects)
    (second : middle.Modifies after sequences objects) : before.Modifies after sequences objects :=
  ⟨second.nextRef.trans first.nextRef, second.nextObject.trans first.nextObject,
    second.nextCollection.trans first.nextCollection, second.collections.trans first.collections,
    second.classes.trans first.classes,
    fun ref outside => (second.otherSequences ref outside).trans (first.otherSequences ref outside),
    fun ref outside => (second.otherObjects ref outside).trans (first.otherObjects ref outside)⟩

theorem tick {before after : Heap} {sequences : List SeqRef} {objects : List ObjectRef}
    (frame : before.Modifies after sequences objects) (clock : String) (amount : Nat := 1) :
    before.Modifies (after.tick clock amount) sequences objects :=
  ⟨frame.nextRef, frame.nextObject, frame.nextCollection, frame.collections,
    frame.classes, frame.otherSequences, frame.otherObjects⟩

theorem write {before after : Heap} {sequences : List SeqRef} {objects : List ObjectRef}
    (frame : before.Modifies after sequences objects) (ref : SeqRef) (index value : Int)
    (allowed : ref ∈ sequences) : before.Modifies (after.write ref index value) sequences objects := by
  refine ⟨frame.nextRef, frame.nextObject, frame.nextCollection, frame.collections,
    frame.classes, ?_, frame.otherObjects⟩
  intro other outside
  have different : other ≠ ref := by intro same; exact outside (same ▸ allowed)
  simpa only [Heap.write, different, false_and, if_false] using frame.otherSequences other outside

theorem writeField {before after : Heap} {sequences : List SeqRef} {objects : List ObjectRef}
    (frame : before.Modifies after sequences objects) (ref : ObjectRef) (field : String)
    (value : ObjectValue) (allowed : ref ∈ objects) :
    before.Modifies (after.writeField ref field value) sequences objects := by
  refine ⟨frame.nextRef, frame.nextObject, frame.nextCollection, frame.collections,
    ?_, frame.otherSequences, ?_⟩
  · funext other
    rw [Heap.objectClass_writeField]
    exact congrFun frame.classes other
  · intro other outside
    have different : other ≠ ref := by intro same; exact outside (same ▸ allowed)
    simpa only [Heap.writeField, if_neg different] using frame.otherObjects other outside

theorem read {before after : Heap} {sequences : List SeqRef} {objects : List ObjectRef}
    (frame : before.Modifies after sequences objects) (ref : SeqRef) (outside : ref ∉ sequences) :
    after.read ref = before.read ref := frame.otherSequences ref outside

theorem readField {before after : Heap} {sequences : List SeqRef} {objects : List ObjectRef}
    (frame : before.Modifies after sequences objects) (ref : ObjectRef) (outside : ref ∉ objects)
    (field : String) : after.readField ref field = before.readField ref field := by
  simp only [Heap.readField, frame.otherObjects ref outside]

end Heap.Modifies
end Algo2LeanGenerated


