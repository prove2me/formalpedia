-- Prove2me | Definitions.Def_Algo2LeanLib_FibonacciForest
-- name    : Algo2LeanLib_FibonacciForest
-- status  : Definition
-- author  : @lunjia
-- created : 2026-10-10T23:39:15.844984+00:00
-- url     : https://prove2.me/theorems/6d0af08f-6071-448e-a96d-33e3f27d5549
-- title:
--   Algo2LeanLib.FibonacciForest definitions
-- statement:
--   Definitions and required structural lemmas from `Algo2LeanLib.FibonacciForest`. Source declarations are retained by compiler-reported ranges; imports are redirected to the corresponding definition bundles. This bundle contains no theorem stubs.
--
--   <!-- algo2lean-provenance-v0.1.4 -->
--   **[Algo2Lean](https://www.algo2lean.com/) provenance and reproduction.** These definitions target [Algo2Lean](https://www.algo2lean.com/) v0.1.4, using the compiler source at [public commit `0f79d5e4242e6477531c9ee4410409f5b1c92f76`](https://github.com/lunjiah/algo2lean/tree/0f79d5e4242e6477531c9ee4410409f5b1c92f76), and Lean 4.33.1. The versioned compiler location is [Algo2Lean v0.1.4](https://www.algo2lean.com/versions/v0.1.4/). Compile all supplied `.algo` files and imports to reproduce the raw generated definitions. Release publication and exact website parity require their separately recorded checks; this metadata alone does not assert them. Prove2Me imports and declaration packaging are mechanically adapted, with original hashes, compiler-reported source ranges, and adaptations recorded in transplant provenance. Exact reproduction does not prove the compiler correct.
-- source:
--   https://github.com/lunjiah/algo2lean/blob/0f79d5e4242e6477531c9ee4410409f5b1c92f76/Algo2LeanLib/FibonacciForest.lean

import Definitions.Def_Algo2LeanLib_Fibonacci

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true



set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

/-!
Finite logical forests for the mutable Fibonacci heap.

Vertex handles and keys are mathematical integers. Child lists are newest-first
in link order, matching insertion before the physical child-ring head. A ring
representation still needs to prove that its traversal realizes this finite
forest, with unique handles and the observable parent/mark/degree fields.
-/

namespace Algo2Lean.Fibonacci

inductive Node where
  | make (vertex key : Int) (marked : Bool) (children : List Node) : Node

def Node.vertex : Node → Int
  | .make vertex _ _ _ => vertex

def Node.key : Node → Int
  | .make _ key _ _ => key

def Node.marked : Node → Bool
  | .make _ _ marked _ => marked

def Node.children : Node → List Node
  | .make _ _ _ children => children

def Node.degree (node : Node) : Nat := node.children.length

def Node.entries : Node → List (Int × Int)
  | .make vertex key _ children => (vertex, key) :: children.flatMap Node.entries

def Node.shape : Node → Tree
  | .make _ _ _ children => .node (children.map Node.shape)

def Node.withMark (node : Node) (marked : Bool) : Node :=
  .make node.vertex node.key marked node.children

def Node.withChildren (node : Node) (children : List Node) : Node :=
  .make node.vertex node.key node.marked children

def Node.withKey (node : Node) (key : Int) : Node :=
  .make node.vertex key node.marked node.children

abbrev Forest := List Node

def Forest.entries (forest : Forest) : List (Int × Int) := forest.flatMap Node.entries

def Forest.Unique (forest : Forest) : Prop := (forest.entries.map Prod.fst).Nodup

@[simp] theorem Node.entries_withMark (node : Node) (marked : Bool) :
    (node.withMark marked).entries = node.entries := by cases node; simp [Node.withMark, Node.entries, Node.vertex, Node.key, Node.children]

@[simp] theorem Node.degree_withMark (node : Node) (marked : Bool) :
    (node.withMark marked).degree = node.degree := by cases node; rfl

@[simp] theorem Node.shape_degree (node : Node) : node.shape.degree = node.degree := by
  cases node
  simp [Node.shape, Tree.degree, Node.degree, Node.children]



/-- Heap order is local along parent-child edges, recursively throughout each tree. -/
inductive Node.Ordered : Node → Prop where
  | make {vertex key : Int} {marked : Bool} {children : List Node} :
      (∀ child ∈ children, key ≤ child.key) →
      (∀ child ∈ children, child.Ordered) → Node.Ordered (.make vertex key marked children)

def Forest.Ordered (forest : Forest) : Prop := ∀ root ∈ forest, root.Ordered

def Forest.RootsUnmarked (forest : Forest) : Prop := ∀ root ∈ forest, root.marked = false

/-- Rank capacity is the degree plus one for a marked node. The extra unit
    accounts for the single child loss permitted before a cascading cut. -/
def Node.rankCapacity (node : Node) : Nat := node.degree + if node.marked then 1 else 0

def ChildOrder : List Node → Prop
  | [] => True
  | child :: older => older.length ≤ child.rankCapacity ∧ ChildOrder older

inductive Node.Ranked : Node → Prop where
  | make {vertex key : Int} {marked : Bool} {children : List Node} :
      ChildOrder children → (∀ child ∈ children, child.Ranked) →
      Node.Ranked (.make vertex key marked children)

def Forest.Ranked (forest : Forest) : Prop := ∀ root ∈ forest, root.Ranked

def Forest.Valid (forest : Forest) : Prop :=
  forest.Unique ∧ forest.Ordered ∧ forest.Ranked ∧ forest.RootsUnmarked

























/-- Equal-degree linking puts the losing root first in its parent's child list
    and clears the losing root's mark, exactly as a Fibonacci-heap link does. -/
def Node.link (parent child : Node) : Node :=
  parent.withChildren (child.withMark false :: parent.children)

















def Forest.insertRoot (root : Node) (forest : Forest) : Forest := root.withMark false :: forest

def Forest.linkRoots (parent child : Node) (rest : Forest) : Forest := parent.link child :: rest

def Forest.cutRootChild (parent child : Node) (earlier later : List Node) (rest : Forest) : Forest :=
  parent.withChildren (earlier ++ later) :: child.withMark false :: rest



@[simp] theorem Forest.insertRoot_entries (root : Node) (forest : Forest) :
    (insertRoot root forest).entries = root.entries ++ forest.entries := by
  simp [Forest.insertRoot, Forest.entries]











/-- All marks in a subtree. Valid forests have unmarked roots, so their sum
    counts exactly the marked nonroots used by the potential function. -/
def Node.marks : Node → Nat
  | .make _ _ marked children => (if marked then 1 else 0) + (children.map Node.marks).sum

def Forest.marks (forest : Forest) : Nat := (forest.map Node.marks).sum

def Forest.counts (forest : Forest) : Counts := ⟨forest.length, forest.marks⟩













/-- Removing the minimum root promotes its children without changing their keys. -/
def Forest.promoteChildren (minimum : Node) (rest : Forest) : Forest :=
  minimum.children.map (fun child => child.withMark false) ++ rest











@[simp] theorem Node.withKey_vertices (node : Node) (key : Int) :
    ((node.withKey key).entries.map Prod.fst) = (node.entries.map Prod.fst) := by
  cases node
  simp [Node.withKey, Node.entries, Node.vertex, Node.marked, Node.children]



end Algo2Lean.Fibonacci


