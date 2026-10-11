-- Prove2me | Definitions.Def_Algo2LeanLib_FibonacciStorage
-- name    : Algo2LeanLib_FibonacciStorage
-- status  : Definition
-- author  : @lunjia
-- created : 2026-10-10T23:39:36.787928+00:00
-- url     : https://prove2.me/theorems/2f2354ec-f84b-46a3-9564-ce2289f23b93
-- title:
--   Algo2LeanLib.FibonacciStorage definitions
-- statement:
--   Definitions and required structural lemmas from `Algo2LeanLib.FibonacciStorage`. Source declarations are retained by compiler-reported ranges; imports are redirected to the corresponding definition bundles. This bundle contains no theorem stubs.
--
--   <!-- algo2lean-provenance-v0.1.4 -->
--   **[Algo2Lean](https://www.algo2lean.com/) provenance and reproduction.** These definitions target [Algo2Lean](https://www.algo2lean.com/) v0.1.4, using the compiler source at [public commit `0f79d5e4242e6477531c9ee4410409f5b1c92f76`](https://github.com/lunjiah/algo2lean/tree/0f79d5e4242e6477531c9ee4410409f5b1c92f76), and Lean 4.33.1. The versioned compiler location is [Algo2Lean v0.1.4](https://www.algo2lean.com/versions/v0.1.4/). Compile all supplied `.algo` files and imports to reproduce the raw generated definitions. Release publication and exact website parity require their separately recorded checks; this metadata alone does not assert them. Prove2Me imports and declaration packaging are mechanically adapted, with original hashes, compiler-reported source ranges, and adaptations recorded in transplant provenance. Exact reproduction does not prove the compiler correct.
-- source:
--   https://github.com/lunjiah/algo2lean/blob/0f79d5e4242e6477531c9ee4410409f5b1c92f76/Algo2LeanLib/FibonacciStorage.lean

import Definitions.Def_Algo2LeanLib_FibonacciForest
import Definitions.Def_Algo2LeanLib_FibonacciRings

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true



set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

/-!
The representation boundary between Fibonacci forests and mutable indexed storage.
Snapshots contain ordinary array observations, not a compiler configuration or a
transcript. A compiled operation must establish preservation of this relation.
-/

namespace Algo2Lean.Fibonacci

structure Snapshot where
  keys : Int → Int
  parents : Int → Int
  children : Int → Int
  left : Int → Int
  right : Int → Int
  degrees : Int → Int
  marks : Int → Int
  present : Int → Int
  table : Int → Int
  minimum : Int
  size : Int

/-- Every node has the observed key, parent, mark, degree, and child-ring head.
    The finite child list witnesses termination of a ring traversal. -/
inductive Stored (state : Snapshot) : Int → Node → Prop where
  | node {vertex key parent : Int} {marked : Bool} {children : List Node}
      (readKey : state.keys vertex = key)
      (readParent : state.parents vertex = parent)
      (readMark : state.marks vertex = if marked then 1 else 0)
      (readDegree : state.degrees vertex = children.length)
      (readPresent : state.present vertex = 1)
      (readChild : state.children vertex =
        match children with | [] => -1 | first :: _ => first.vertex)
      (childRing : Rings.RingOrEmpty state.left state.right (children.map Node.vertex))
      (subtrees : ∀ child ∈ children, Stored state vertex child) :
      Stored state parent (.make vertex key marked children)









/-- A complete public queue invariant. Sentinel and exact-membership clauses
    are explicit; a class tag or valid forest alone is insufficient. -/
structure Represented (state : Snapshot) (forest : Forest) : Prop where
  valid : forest.Valid
  roots : Rings.RingOrEmpty state.left state.right (forest.map Node.vertex)
  stored : ∀ root ∈ forest, Stored state (-1) root
  nonnegative : ∀ vertex key, (vertex, key) ∈ forest.entries → 0 ≤ vertex
  presence : ∀ vertex, state.present vertex ≠ 0 ↔ ∃ key, (vertex, key) ∈ forest.entries
  size : state.size = forest.entries.length
  minimum : (forest = [] ∧ state.minimum = -1) ∨
    ∃ root ∈ forest, state.minimum = root.vertex ∧ ∀ other ∈ forest, root.key ≤ other.key
  /-- Any negative entry is an empty scratch bucket, exactly as tested by the source. -/
  scratch : ∀ degree, state.table degree < 0















/-- Observable node metadata; sibling pointers are framed separately because
    a subtree's root may move between rings without changing its descendants. -/
structure Snapshot.SameFields (before after : Snapshot) (vertex : Int) : Prop where
  key : after.keys vertex = before.keys vertex
  parent : after.parents vertex = before.parents vertex
  child : after.children vertex = before.children vertex
  degree : after.degrees vertex = before.degrees vertex
  mark : after.marks vertex = before.marks vertex
  present : after.present vertex = before.present vertex

@[simp] theorem Node.root_entry (node : Node) : (node.vertex, node.key) ∈ node.entries := by
  cases node
  simp [Node.vertex, Node.key, Node.entries]


















/-- Exact observable effect of inserting a previously absent singleton through
    `push_or_decrease` and `add_root`; clocks are handled independently. -/
def Snapshot.insertSingleton (state : Snapshot) (vertex key : Int) : Snapshot :=
  { state with
    keys := Rings.write state.keys vertex key
    parents := Rings.write state.parents vertex (-1)
    children := Rings.write state.children vertex (-1)
    degrees := Rings.write state.degrees vertex 0
    marks := Rings.write state.marks vertex 0
    present := Rings.write state.present vertex 1
    size := state.size + 1
    left := if state.minimum < 0 then Rings.write state.left vertex vertex
      else Rings.insertAfterLeft state.left state.right state.minimum vertex
    right := if state.minimum < 0 then Rings.write state.right vertex vertex
      else Rings.insertAfterRight state.right state.minimum vertex
    minimum := if state.minimum < 0 then vertex
      else if key < state.keys state.minimum then vertex else state.minimum }


















/-- Address membership ignores keys while retaining the finite tree witness. -/
def Node.Has (node : Node) (vertex : Int) : Prop := ∃ key, (vertex, key) ∈ node.entries

def Forest.Has (forest : Forest) (vertex : Int) : Prop := ∃ key, (vertex, key) ∈ forest.entries

@[simp] theorem Node.has_iff_map (node : Node) (vertex : Int) :
    node.Has vertex ↔ vertex ∈ node.entries.map Prod.fst := by
  constructor
  · rintro ⟨key, member⟩
    exact List.mem_map.mpr ⟨(vertex, key), member, rfl⟩
  · rintro member
    obtain ⟨⟨value, key⟩, member, same⟩ := List.mem_map.mp member
    change value = vertex at same
    subst value
    exact ⟨key, member⟩

@[simp] theorem Forest.has_iff_map (forest : Forest) (vertex : Int) :
    forest.Has vertex ↔ vertex ∈ forest.entries.map Prod.fst := by
  constructor
  · rintro ⟨key, member⟩
    exact List.mem_map.mpr ⟨(vertex, key), member, rfl⟩
  · rintro member
    obtain ⟨⟨value, key⟩, member, same⟩ := List.mem_map.mp member
    change value = vertex at same
    subst value
    exact ⟨key, member⟩















/-- Exact non-clock effect of linking a detached child under a parent root. -/
def Snapshot.link (state : Snapshot) (child parent : Int) : Snapshot :=
  { state with
    parents := Rings.write state.parents child parent
    marks := Rings.write state.marks child 0
    children := Rings.write state.children parent child
    degrees := Rings.write state.degrees parent (state.degrees parent + 1)
    left := if state.children parent < 0 then Rings.write state.left child child
      else Rings.insertBeforeLeft state.left (state.children parent) child
    right := if state.children parent < 0 then Rings.write state.right child child
      else Rings.insertBeforeRight state.left state.right (state.children parent) child }











/-- A temporary consolidation state separates the untouched pending root ring
    from detached roots held in degree buckets or the current collision. The
    minimum is a traversal cursor and need not be a global minimum yet. -/
structure SplitRepresented (state : Snapshot) (pending detached : Forest) : Prop where
  valid : Forest.Valid (pending ++ detached)
  stored : ∀ root ∈ pending ++ detached, Stored state (-1) root
  pendingRing : Rings.RingOrEmpty state.left state.right (pending.map Node.vertex)
  detachedRings : ∀ root ∈ detached, state.left root.vertex = root.vertex ∧ state.right root.vertex = root.vertex
  nonnegative : ∀ vertex key, (vertex, key) ∈ Forest.entries (pending ++ detached) → 0 ≤ vertex
  presence : ∀ vertex, state.present vertex ≠ 0 ↔ Forest.Has (pending ++ detached) vertex
  size : state.size = (Forest.entries (pending ++ detached)).length
  cursor : (pending = [] ∧ state.minimum = -1) ∨ ∃ root ∈ pending, state.minimum = root.vertex





























/-- Exact child-ring removal before the source's `add_root` call. The child's
    parent and mark are intentionally left for that following operation. -/
def Snapshot.removeChild (state : Snapshot) (child parent : Int) : Snapshot :=
  { state with
    children := Rings.write state.children parent
      (if state.children parent = child then
        if state.right child = child then -1 else state.right child
       else state.children parent)
    degrees := Rings.write state.degrees parent (state.degrees parent - 1)
    left := Rings.removeLeft state.left state.right child
    right := Rings.removeRight state.left state.right child }













/-- A mark update has no effect on allocation, membership, pointers or keys. -/
def Snapshot.setMark (state : Snapshot) (vertex : Int) (marked : Bool) : Snapshot :=
  { state with marks := Rings.write state.marks vertex (if marked then 1 else 0) }







end Algo2Lean.Fibonacci


