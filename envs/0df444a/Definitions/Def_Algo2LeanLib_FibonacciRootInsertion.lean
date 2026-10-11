-- Prove2me | Definitions.Def_Algo2LeanLib_FibonacciRootInsertion
-- name    : Algo2LeanLib_FibonacciRootInsertion
-- status  : Definition
-- author  : @lunjia
-- created : 2026-10-10T23:40:07.450967+00:00
-- url     : https://prove2.me/theorems/6f32440c-1005-46c2-87f6-b76e0d7cdc42
-- title:
--   Algo2LeanLib.FibonacciRootInsertion definitions
-- statement:
--   Definitions and required structural lemmas from `Algo2LeanLib.FibonacciRootInsertion`. Source declarations are retained by compiler-reported ranges; imports are redirected to the corresponding definition bundles. This bundle contains no theorem stubs.
--
--   <!-- algo2lean-provenance-v0.1.4 -->
--   **[Algo2Lean](https://www.algo2lean.com/) provenance and reproduction.** These definitions target [Algo2Lean](https://www.algo2lean.com/) v0.1.4, using the compiler source at [public commit `0f79d5e4242e6477531c9ee4410409f5b1c92f76`](https://github.com/lunjiah/algo2lean/tree/0f79d5e4242e6477531c9ee4410409f5b1c92f76), and Lean 4.33.1. The versioned compiler location is [Algo2Lean v0.1.4](https://www.algo2lean.com/versions/v0.1.4/). Compile all supplied `.algo` files and imports to reproduce the raw generated definitions. Release publication and exact website parity require their separately recorded checks; this metadata alone does not assert them. Prove2Me imports and declaration packaging are mechanically adapted, with original hashes, compiler-reported source ranges, and adaptations recorded in transplant provenance. Exact reproduction does not prove the compiler correct.
-- source:
--   https://github.com/lunjiah/algo2lean/blob/0f79d5e4242e6477531c9ee4410409f5b1c92f76/Algo2LeanLib/FibonacciRootInsertion.lean

import Definitions.Def_Algo2LeanLib_FibonacciStorage

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true



set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

namespace Algo2Lean.Fibonacci

/-- Insert an existing detached tree into the root ring without changing its
    entries or its children. This is the exact non-clock effect of `add_root`. -/
def Snapshot.addRoot (state : Snapshot) (vertex : Int) : Snapshot :=
  { state with
    parents := Rings.write state.parents vertex (-1)
    marks := Rings.write state.marks vertex 0
    left := if state.minimum < 0 then Rings.write state.left vertex vertex
      else Rings.insertAfterLeft state.left state.right state.minimum vertex
    right := if state.minimum < 0 then Rings.write state.right vertex vertex
      else Rings.insertAfterRight state.right state.minimum vertex
    minimum := if state.minimum < 0 then vertex
      else if state.keys vertex < state.keys state.minimum then vertex else state.minimum }





















end Algo2Lean.Fibonacci


