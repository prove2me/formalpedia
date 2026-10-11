-- Prove2me | Definitions.Def_Algo2LeanLib_FibonacciRebuild
-- name    : Algo2LeanLib_FibonacciRebuild
-- status  : Definition
-- author  : @lunjia
-- created : 2026-10-10T23:40:20.434852+00:00
-- url     : https://prove2.me/theorems/19fae289-c9e6-45d0-a051-a727125e966a
-- title:
--   Algo2LeanLib.FibonacciRebuild definitions
-- statement:
--   Definitions and required structural lemmas from `Algo2LeanLib.FibonacciRebuild`. Source declarations are retained by compiler-reported ranges; imports are redirected to the corresponding definition bundles. This bundle contains no theorem stubs.
--
--   <!-- algo2lean-provenance-v0.1.4 -->
--   **[Algo2Lean](https://www.algo2lean.com/) provenance and reproduction.** These definitions target [Algo2Lean](https://www.algo2lean.com/) v0.1.4, using the compiler source at [public commit `0f79d5e4242e6477531c9ee4410409f5b1c92f76`](https://github.com/lunjiah/algo2lean/tree/0f79d5e4242e6477531c9ee4410409f5b1c92f76), and Lean 4.33.1. The versioned compiler location is [Algo2Lean v0.1.4](https://www.algo2lean.com/versions/v0.1.4/). Compile all supplied `.algo` files and imports to reproduce the raw generated definitions. Release publication and exact website parity require their separately recorded checks; this metadata alone does not assert them. Prove2Me imports and declaration packaging are mechanically adapted, with original hashes, compiler-reported source ranges, and adaptations recorded in transplant provenance. Exact reproduction does not prove the compiler correct.
-- source:
--   https://github.com/lunjiah/algo2lean/blob/0f79d5e4242e6477531c9ee4410409f5b1c92f76/Algo2LeanLib/FibonacciRebuild.lean

import Definitions.Def_Algo2LeanLib_FibonacciConsolidation
import Definitions.Def_Algo2LeanLib_FibonacciRootInsertion

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true



set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

namespace Algo2Lean.Fibonacci



/-- The current cursor is a least-key root of the reconstructed pending ring. -/
def PendingLeast (state : Snapshot) (pending : Forest) : Prop :=
  ∀ root ∈ pending, state.keys state.minimum ≤ root.key





def Snapshot.rebuildAt (state : Snapshot) (degree : Int) : Snapshot :=
  let root := state.table degree
  let cleared := {state with table := Rings.write state.table degree (-1)}
  if root < 0 then cleared else cleared.addRoot root

/-- A finite reconstruction follows the same degree-by-degree table traversal
    as the source; counts are insertions and root-key comparisons. -/
inductive BucketRebuild (maximum : Int) : Snapshot → Int → Snapshot → Nat → Nat → Prop where
  | done (state : Snapshot) (degree : Int) (past : maximum < degree) :
      BucketRebuild maximum state degree state 0 0
  | skip {state after : Snapshot} {degree : Int} {insertions comparisons : Nat}
      (inside : degree ≤ maximum) (empty : state.table degree < 0)
      (rest : BucketRebuild maximum (state.rebuildAt degree) (degree + 1) after insertions comparisons) :
      BucketRebuild maximum state degree after insertions comparisons
  | insert {state after : Snapshot} {degree : Int} {insertions comparisons : Nat}
      (inside : degree ≤ maximum) (occupied : 0 ≤ state.table degree)
      (rest : BucketRebuild maximum (state.rebuildAt degree) (degree + 1) after insertions comparisons) :
      BucketRebuild maximum state degree after (insertions + 1)
        (comparisons + if state.minimum < 0 then 0 else 1)





@[simp] theorem Snapshot.rebuildAt_table (state : Snapshot) (degree : Int) :
    (state.rebuildAt degree).table = Rings.write state.table degree (-1) := by
  unfold Snapshot.rebuildAt
  dsimp only
  split <;> rfl

def ClearedBelow (state : Snapshot) (degree : Int) : Prop :=
  ∀ index, index < degree → state.table index < 0


















end Algo2Lean.Fibonacci


