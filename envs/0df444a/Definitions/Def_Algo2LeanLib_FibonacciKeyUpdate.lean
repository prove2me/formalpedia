-- Prove2me | Definitions.Def_Algo2LeanLib_FibonacciKeyUpdate
-- name    : Algo2LeanLib_FibonacciKeyUpdate
-- status  : Definition
-- author  : @lunjia
-- created : 2026-10-10T23:41:20.43419+00:00
-- url     : https://prove2.me/theorems/f2443819-8a15-414e-b4ca-0cfe4a796b7b
-- title:
--   Algo2LeanLib.FibonacciKeyUpdate definitions
-- statement:
--   Definitions and required structural lemmas from `Algo2LeanLib.FibonacciKeyUpdate`. Source declarations are retained by compiler-reported ranges; imports are redirected to the corresponding definition bundles. This bundle contains no theorem stubs.
--
--   <!-- algo2lean-provenance-v0.1.4 -->
--   **[Algo2Lean](https://www.algo2lean.com/) provenance and reproduction.** These definitions target [Algo2Lean](https://www.algo2lean.com/) v0.1.4, using the compiler source at [public commit `0f79d5e4242e6477531c9ee4410409f5b1c92f76`](https://github.com/lunjiah/algo2lean/tree/0f79d5e4242e6477531c9ee4410409f5b1c92f76), and Lean 4.33.1. The versioned compiler location is [Algo2Lean v0.1.4](https://www.algo2lean.com/versions/v0.1.4/). Compile all supplied `.algo` files and imports to reproduce the raw generated definitions. Release publication and exact website parity require their separately recorded checks; this metadata alone does not assert them. Prove2Me imports and declaration packaging are mechanically adapted, with original hashes, compiler-reported source ranges, and adaptations recorded in transplant provenance. Exact reproduction does not prove the compiler correct.
-- source:
--   https://github.com/lunjiah/algo2lean/blob/0f79d5e4242e6477531c9ee4410409f5b1c92f76/Algo2LeanLib/FibonacciKeyUpdate.lean

import Definitions.Def_Algo2LeanLib_FibonacciDecrease

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true



set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace Algo2Lean.Fibonacci

/-- Exact replacement of one queue entry; all other entries are unchanged. -/
def EntryChange (before after : List (Int × Int)) (vertex oldKey newKey : Int) : Prop :=
  ∃ unchanged, before.Perm ((vertex, oldKey) :: unchanged) ∧
    after.Perm ((vertex, newKey) :: unchanged)



/-- Entries surrounding a focused subtree in its ancestor context. -/
def Ancestors.surrounding : List Ancestor → List (Int × Int)
  | [] => []
  | frame :: rest => (frame.vertex, frame.key) ::
      (Forest.entries frame.before ++ Forest.entries frame.after ++ Ancestors.surrounding rest)





















@[simp] theorem Node.withKey_marks (node : Node) (key : Int) : (node.withKey key).marks = node.marks := by
  cases node
  simp [Node.marks, Node.withKey, Node.vertex, Node.marked, Node.children]



























end Algo2Lean.Fibonacci


