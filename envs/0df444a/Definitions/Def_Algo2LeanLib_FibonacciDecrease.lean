-- Prove2me | Definitions.Def_Algo2LeanLib_FibonacciDecrease
-- name    : Algo2LeanLib_FibonacciDecrease
-- status  : Definition
-- author  : @lunjia
-- created : 2026-10-10T23:40:57.159639+00:00
-- url     : https://prove2.me/theorems/5f8dd971-4c96-4abf-bbc0-ab351e2b5a71
-- title:
--   Algo2LeanLib.FibonacciDecrease definitions
-- statement:
--   Definitions and required structural lemmas from `Algo2LeanLib.FibonacciDecrease`. Source declarations are retained by compiler-reported ranges; imports are redirected to the corresponding definition bundles. This bundle contains no theorem stubs.
--
--   <!-- algo2lean-provenance-v0.1.4 -->
--   **[Algo2Lean](https://www.algo2lean.com/) provenance and reproduction.** These definitions target [Algo2Lean](https://www.algo2lean.com/) v0.1.4, using the compiler source at [public commit `0f79d5e4242e6477531c9ee4410409f5b1c92f76`](https://github.com/lunjiah/algo2lean/tree/0f79d5e4242e6477531c9ee4410409f5b1c92f76), and Lean 4.33.1. The versioned compiler location is [Algo2Lean v0.1.4](https://www.algo2lean.com/versions/v0.1.4/). Compile all supplied `.algo` files and imports to reproduce the raw generated definitions. Release publication and exact website parity require their separately recorded checks; this metadata alone does not assert them. Prove2Me imports and declaration packaging are mechanically adapted, with original hashes, compiler-reported source ranges, and adaptations recorded in transplant provenance. Exact reproduction does not prove the compiler correct.
-- source:
--   https://github.com/lunjiah/algo2lean/blob/0f79d5e4242e6477531c9ee4410409f5b1c92f76/Algo2LeanLib/FibonacciDecrease.lean

import Definitions.Def_Algo2LeanLib_FibonacciMutableCascade

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true



set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

namespace Algo2Lean.Fibonacci

/-- Exact key write in the strict-decrease branch. -/
def Snapshot.lowerKey (state : Snapshot) (vertex key : Int) : Snapshot :=
  { state with keys := Rings.write state.keys vertex key }

/-- The final minimum comparison performed after every strict decrease. -/
def Snapshot.finishDecrease (state : Snapshot) (vertex : Int) : Snapshot :=
  { state with minimum := if state.keys vertex < state.keys state.minimum then vertex else state.minimum }



/-- Internal representation without rank/order assumptions. Physical root
    traversal order is kept separate from the logical forest order during cuts. -/
structure RootBoundary (state : Snapshot) (forest : Forest) : Prop where
  trees : StoredForest state forest
  roots : ∃ order : List Int, order.Perm (forest.map Node.vertex) ∧ Rings.RingOrEmpty state.left state.right order
  presence : ∀ vertex, state.present vertex ≠ 0 ↔ Forest.Has forest vertex
  size : state.size = forest.entries.length
  minimum : (forest = [] ∧ state.minimum = -1) ∨
    ∃ root ∈ forest, state.minimum = root.vertex ∧
      ∀ other ∈ forest, state.keys state.minimum ≤ state.keys other.vertex
  scratch : ∀ degree, state.table degree < 0



















/-- Existing-handle push_or_decrease follows the source's exact key, parent,
    cut/cascade, and final-minimum branches; insertion is a separate contract. -/
inductive DecreaseRun : Snapshot → Snapshot → Int → Int → Nat → Prop where
  | unchanged {state : Snapshot} {vertex key : Int} (noDecrease : state.keys vertex ≤ key) :
      DecreaseRun state state vertex key 0
  | root {state : Snapshot} {vertex key : Int} (decreased : key < state.keys vertex)
      (root : state.parents vertex < 0) :
      DecreaseRun state ((state.lowerKey vertex key).finishDecrease vertex) vertex key 0
  | ordered {state : Snapshot} {vertex key : Int} (decreased : key < state.keys vertex)
      (nonroot : 0 ≤ state.parents vertex)
      (ordered : (state.lowerKey vertex key).keys (state.parents vertex) ≤ key) :
      DecreaseRun state ((state.lowerKey vertex key).finishDecrease vertex) vertex key 0
  | cascading {state middle : Snapshot} {vertex key : Int} {cuts : Nat}
      (decreased : key < state.keys vertex) (nonroot : 0 ≤ state.parents vertex)
      (violates : key < (state.lowerKey vertex key).keys (state.parents vertex))
      (cascade : CascadeRun ((state.lowerKey vertex key).cut vertex (state.parents vertex)) middle
        (state.parents vertex) cuts) :
      DecreaseRun state (middle.finishDecrease vertex) vertex key (cuts + 1)














end Algo2Lean.Fibonacci


