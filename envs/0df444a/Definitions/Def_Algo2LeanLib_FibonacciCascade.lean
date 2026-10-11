-- Prove2me | Definitions.Def_Algo2LeanLib_FibonacciCascade
-- name    : Algo2LeanLib_FibonacciCascade
-- status  : Definition
-- author  : @lunjia
-- created : 2026-10-10T23:39:39.36672+00:00
-- url     : https://prove2.me/theorems/10274229-912e-445c-8d1d-1a2bc4fc404f
-- title:
--   Algo2LeanLib.FibonacciCascade definitions
-- statement:
--   Definitions and required structural lemmas from `Algo2LeanLib.FibonacciCascade`. Source declarations are retained by compiler-reported ranges; imports are redirected to the corresponding definition bundles. This bundle contains no theorem stubs.
--
--   <!-- algo2lean-provenance-v0.1.4 -->
--   **[Algo2Lean](https://www.algo2lean.com/) provenance and reproduction.** These definitions target [Algo2Lean](https://www.algo2lean.com/) v0.1.4, using the compiler source at [public commit `0f79d5e4242e6477531c9ee4410409f5b1c92f76`](https://github.com/lunjiah/algo2lean/tree/0f79d5e4242e6477531c9ee4410409f5b1c92f76), and Lean 4.33.1. The versioned compiler location is [Algo2Lean v0.1.4](https://www.algo2lean.com/versions/v0.1.4/). Compile all supplied `.algo` files and imports to reproduce the raw generated definitions. Release publication and exact website parity require their separately recorded checks; this metadata alone does not assert them. Prove2Me imports and declaration packaging are mechanically adapted, with original hashes, compiler-reported source ranges, and adaptations recorded in transplant provenance. Exact reproduction does not prove the compiler correct.
-- source:
--   https://github.com/lunjiah/algo2lean/blob/0f79d5e4242e6477531c9ee4410409f5b1c92f76/Algo2LeanLib/FibonacciCascade.lean

import Definitions.Def_Algo2LeanLib_FibonacciForest

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true



set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

namespace Algo2Lean.Fibonacci

/-- One ancestor records the siblings before and after the focused subtree.
    Contexts are ordered from the immediate parent towards the root. -/
structure Ancestor where
  vertex : Int
  key : Int
  marked : Bool
  before : List Node
  after : List Node

def Ancestor.plug (frame : Ancestor) (node : Node) : Node :=
  .make frame.vertex frame.key frame.marked (frame.before ++ node :: frame.after)

def Ancestors.plug (context : List Ancestor) (node : Node) : Node :=
  match context with
  | [] => node
  | frame :: rest => Ancestors.plug rest (frame.plug node)

/-- Logical cascade after the focused node loses one child. A marked nonroot
    is promoted and propagation continues; an unmarked nonroot is marked. -/
def cascadeForest (node : Node) (kept : List Node) : List Ancestor → Forest
  | [] => [node.withChildren kept]
  | frame :: rest =>
    if node.marked then
      (node.withChildren kept).withMark false ::
        cascadeForest (frame.plug node) (frame.before ++ frame.after) rest
    else
      [Ancestors.plug (frame :: rest) ((node.withChildren kept).withMark true)]

























/-- Marks contributed by ancestors and siblings, excluding the focused subtree. -/
def Ancestor.marks (frame : Ancestor) : Nat :=
  (if frame.marked then 1 else 0) + Forest.marks frame.before + Forest.marks frame.after

def Ancestors.marks (context : List Ancestor) : Nat := (context.map Ancestor.marks).sum





/-- The number of additionally promoted ancestors; the initially requested
    child cut is accounted for separately. -/
def cascadeCuts (node : Node) : List Ancestor → Nat
  | [] => 0
  | frame :: rest => if node.marked then cascadeCuts (frame.plug node) rest + 1 else 0





end Algo2Lean.Fibonacci


