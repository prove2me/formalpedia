-- Prove2me | Definitions.Def_Algo2LeanLib_FibonacciStoredContext
-- name    : Algo2LeanLib_FibonacciStoredContext
-- status  : Definition
-- author  : @lunjia
-- created : 2026-10-10T23:40:07.80157+00:00
-- url     : https://prove2.me/theorems/2effc8d5-282c-48d0-bf5f-b15bb98fc33d
-- title:
--   Algo2LeanLib.FibonacciStoredContext definitions
-- statement:
--   Definitions and required structural lemmas from `Algo2LeanLib.FibonacciStoredContext`. Source declarations are retained by compiler-reported ranges; imports are redirected to the corresponding definition bundles. This bundle contains no theorem stubs.
--
--   <!-- algo2lean-provenance-v0.1.4 -->
--   **[Algo2Lean](https://www.algo2lean.com/) provenance and reproduction.** These definitions target [Algo2Lean](https://www.algo2lean.com/) v0.1.4, using the compiler source at [public commit `0f79d5e4242e6477531c9ee4410409f5b1c92f76`](https://github.com/lunjiah/algo2lean/tree/0f79d5e4242e6477531c9ee4410409f5b1c92f76), and Lean 4.33.1. The versioned compiler location is [Algo2Lean v0.1.4](https://www.algo2lean.com/versions/v0.1.4/). Compile all supplied `.algo` files and imports to reproduce the raw generated definitions. Release publication and exact website parity require their separately recorded checks; this metadata alone does not assert them. Prove2Me imports and declaration packaging are mechanically adapted, with original hashes, compiler-reported source ranges, and adaptations recorded in transplant provenance. Exact reproduction does not prove the compiler correct.
-- source:
--   https://github.com/lunjiah/algo2lean/blob/0f79d5e4242e6477531c9ee4410409f5b1c92f76/Algo2LeanLib/FibonacciStoredContext.lean

import Definitions.Def_Algo2LeanLib_FibonacciStorage
import Definitions.Def_Algo2LeanLib_FibonacciCascade

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true



set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

namespace Algo2Lean.Fibonacci

/-- A stored ancestor with one subtree left open. The hole is identified only
    by its address, so proofs about the descendant can be replaced locally. -/
structure StoredAncestor (state : Snapshot) (parent : Int) (frame : Ancestor) (address : Int) : Prop where
  key : state.keys frame.vertex = frame.key
  parent : state.parents frame.vertex = parent
  mark : state.marks frame.vertex = if frame.marked then 1 else 0
  degree : state.degrees frame.vertex = frame.before.length + 1 + frame.after.length
  present : state.present frame.vertex = 1
  childHead : state.children frame.vertex =
    match frame.before with | [] => address | first :: _ => first.vertex
  ring : Rings.Ring state.left state.right
    (frame.before.map Node.vertex ++ address :: frame.after.map Node.vertex)
  siblings : ∀ sibling ∈ frame.before ++ frame.after, Stored state frame.vertex sibling





/-- A finite chain of open ancestors. It contains no proof of the focused
    subtree, allowing the local cut/mark proof to be supplied independently. -/
inductive StoredContext (state : Snapshot) (rootParent : Int) : List Ancestor → Int → Int → Prop where
  | nil (address : Int) : StoredContext state rootParent [] address rootParent
  | cons {frame : Ancestor} {rest : List Ancestor} {address frameParent : Int}
      (outer : StoredContext state rootParent rest frame.vertex frameParent)
      (ancestor : StoredAncestor state frameParent frame address) :
      StoredContext state rootParent (frame :: rest) address frame.vertex












/-- A local subtree edit may also rewire the global root ring. Metadata outside
    the subtree and nonroot pointers outside its strict descendants are framed. -/
structure Snapshot.LocalChange (before after : Snapshot) (node : Node) : Prop where
  fields : ∀ vertex, ¬node.Has vertex → Snapshot.SameFields before after vertex
  links : ∀ vertex, 0 ≤ before.parents vertex → ¬Forest.Has node.children vertex →
    after.left vertex = before.left vertex ∧ after.right vertex = before.right vertex













def Ancestors.parent (context : List Ancestor) (rootParent : Int) : Int :=
  match context with | [] => rootParent | frame :: _ => frame.vertex















end Algo2Lean.Fibonacci


