-- Prove2me | Definitions.Def_Algo2LeanLib_FibonacciRings
-- name    : Algo2LeanLib_FibonacciRings
-- status  : Definition
-- author  : @lunjia
-- created : 2026-10-10T23:38:56.718417+00:00
-- url     : https://prove2.me/theorems/24dedfc0-19bf-4714-b7eb-20a6050f2115
-- title:
--   Algo2LeanLib.FibonacciRings definitions
-- statement:
--   Definitions and required structural lemmas from `Algo2LeanLib.FibonacciRings`. Source declarations are retained by compiler-reported ranges; imports are redirected to the corresponding definition bundles. This bundle contains no theorem stubs.
--
--   <!-- algo2lean-provenance-v0.1.4 -->
--   **[Algo2Lean](https://www.algo2lean.com/) provenance and reproduction.** These definitions target [Algo2Lean](https://www.algo2lean.com/) v0.1.4, using the compiler source at [public commit `0f79d5e4242e6477531c9ee4410409f5b1c92f76`](https://github.com/lunjiah/algo2lean/tree/0f79d5e4242e6477531c9ee4410409f5b1c92f76), and Lean 4.33.1. The versioned compiler location is [Algo2Lean v0.1.4](https://www.algo2lean.com/versions/v0.1.4/). Compile all supplied `.algo` files and imports to reproduce the raw generated definitions. Release publication and exact website parity require their separately recorded checks; this metadata alone does not assert them. Prove2Me imports and declaration packaging are mechanically adapted, with original hashes, compiler-reported source ranges, and adaptations recorded in transplant provenance. Exact reproduction does not prove the compiler correct.
-- source:
--   https://github.com/lunjiah/algo2lean/blob/0f79d5e4242e6477531c9ee4410409f5b1c92f76/Algo2LeanLib/FibonacciRings.lean

import Std

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true



set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

/-!
Finite circular doubly linked lists for Fibonacci-heap pointer proofs.

The representation is independent of heaps and sequence references: `left` and
`right` are the integer-indexed pointer arrays observed through an allocated
sequence. Primitive effects below follow the source's precise write order.
-/

namespace Algo2Lean.Fibonacci.Rings

def write (values : Int → Int) (index value : Int) : Int → Int :=
  fun other => if other = index then value else values other

@[simp] theorem write_same (values : Int → Int) (index value : Int) :
    write values index value index = value := by simp [write]

@[simp] theorem write_other (values : Int → Int) (index value other : Int)
    (different : other ≠ index) : write values index value other = values other := by
  simp [write, different]

/-- An open chain records both pointers along every adjacent pair. Its first
    predecessor and last successor are supplied by the enclosing ring. -/
inductive Chain (left right : Int → Int) : Int → List Int → Int → Prop where
  | singleton (vertex : Int) : Chain left right vertex [vertex] vertex
  | cons (first : Int) {next last : Int} {tail : List Int} :
      right first = next → left next = first → Chain left right next tail last →
      Chain left right first (first :: tail) last

/-- A nonempty ring in its chosen traversal order. Rotating the list changes
    the chosen head while describing exactly the same pointer arrays. -/
structure Ring (left right : Int → Int) (vertices : List Int) : Prop where
  unique : vertices.Nodup
  closed : ∃ first last, Chain left right first vertices last ∧ right last = first ∧ left first = last

def RingOrEmpty (left right : Int → Int) (vertices : List Int) : Prop :=
  vertices = [] ∨ Ring left right vertices





















def insertBeforeLeft (left : Int → Int) (head vertex : Int) : Int → Int :=
  write (write left vertex (left head)) head vertex

def insertBeforeRight (left right : Int → Int) (head vertex : Int) : Int → Int :=
  write (write right vertex head) (left head) vertex

def removeLeft (left right : Int → Int) (vertex : Int) : Int → Int :=
  write (write left (right vertex) (left vertex)) vertex vertex

def removeRight (left right : Int → Int) (vertex : Int) : Int → Int :=
  write (write right (left vertex) (right vertex)) vertex vertex



























/-- The root-list helper inserts after its minimum representative. These are
    its exact effects, distinct from the child-list insertion before its head. -/
def insertAfterLeft (left right : Int → Int) (head vertex : Int) : Int → Int :=
  write (write left vertex head) (right head) vertex

def insertAfterRight (right : Int → Int) (head vertex : Int) : Int → Int :=
  write (write right vertex (right head)) head vertex





end Algo2Lean.Fibonacci.Rings


