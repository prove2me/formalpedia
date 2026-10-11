-- Prove2me | Definitions.Def_Algo2LeanLib_FibonacciDeleteMin
-- name    : Algo2LeanLib_FibonacciDeleteMin
-- status  : Definition
-- author  : @lunjia
-- created : 2026-10-10T23:41:25.579976+00:00
-- url     : https://prove2.me/theorems/8e70caab-1bb4-4d6b-ba23-071c0044cca2
-- title:
--   Algo2LeanLib.FibonacciDeleteMin definitions
-- statement:
--   Definitions and required structural lemmas from `Algo2LeanLib.FibonacciDeleteMin`. Source declarations are retained by compiler-reported ranges; imports are redirected to the corresponding definition bundles. This bundle contains no theorem stubs.
--
--   <!-- algo2lean-provenance-v0.1.4 -->
--   **[Algo2Lean](https://www.algo2lean.com/) provenance and reproduction.** These definitions target [Algo2Lean](https://www.algo2lean.com/) v0.1.4, using the compiler source at [public commit `0f79d5e4242e6477531c9ee4410409f5b1c92f76`](https://github.com/lunjiah/algo2lean/tree/0f79d5e4242e6477531c9ee4410409f5b1c92f76), and Lean 4.33.1. The versioned compiler location is [Algo2Lean v0.1.4](https://www.algo2lean.com/versions/v0.1.4/). Compile all supplied `.algo` files and imports to reproduce the raw generated definitions. Release publication and exact website parity require their separately recorded checks; this metadata alone does not assert them. Prove2Me imports and declaration packaging are mechanically adapted, with original hashes, compiler-reported source ranges, and adaptations recorded in transplant provenance. Exact reproduction does not prove the compiler correct.
-- source:
--   https://github.com/lunjiah/algo2lean/blob/0f79d5e4242e6477531c9ee4410409f5b1c92f76/Algo2LeanLib/FibonacciDeleteMin.lean

import Definitions.Def_Algo2LeanLib_FibonacciConsolidation
import Definitions.Def_Algo2LeanLib_FibonacciDecrease
import Definitions.Def_Algo2LeanLib_FibonacciRootInsertion

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true



set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

namespace Algo2Lean.Fibonacci

/-- Exact non-clock effect after the selected root has lost all children.
    Consolidation starts with its former successor as the traversal cursor. -/
def Snapshot.extractRoot (state : Snapshot) (vertex : Int) : Snapshot :=
  {state with
    left := Rings.removeLeft state.left state.right vertex
    right := Rings.removeRight state.left state.right vertex
    present := Rings.write state.present vertex 0
    size := state.size - 1
    minimum := if state.right vertex = vertex then -1 else state.right vertex}







/-- One child-promotion iteration, before clock accounting. The selected child
    is the current header, exactly as read by the source loop. -/
def Snapshot.promoteChild (state : Snapshot) (vertex : Int) : Snapshot :=
  state.cut (state.children vertex) vertex

inductive PromotionRun (vertex : Int) : Snapshot → Snapshot → Nat → Prop where
  | done (state : Snapshot) (childless : state.children vertex < 0) :
      PromotionRun vertex state state 0
  | next {before after : Snapshot} {count : Nat}
      (hasChild : 0 ≤ before.children vertex)
      (rest : PromotionRun vertex (before.promoteChild vertex) after count) :
      PromotionRun vertex before after (count + 1)





/-- The complete pre-consolidation deletion effect contains actual promotion
    steps followed by the source's membership/size/cursor updates. -/
inductive DeleteMinimum (vertex : Int) : Snapshot → Snapshot → Nat → Prop where
  | finish {before promoted : Snapshot} {count : Nat}
      (promotions : PromotionRun vertex before promoted count) :
      DeleteMinimum vertex before (promoted.extractRoot vertex) count





@[simp] theorem DeleteMinimum.removed {vertex : Int} {before after : Snapshot} {count : Nat}
    (run : DeleteMinimum vertex before after count) : after.present vertex = 0 := by
  cases run
  simp [Snapshot.extractRoot]

end Algo2Lean.Fibonacci


