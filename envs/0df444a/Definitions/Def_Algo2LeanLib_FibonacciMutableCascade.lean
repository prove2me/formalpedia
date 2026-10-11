-- Prove2me | Definitions.Def_Algo2LeanLib_FibonacciMutableCascade
-- name    : Algo2LeanLib_FibonacciMutableCascade
-- status  : Definition
-- author  : @lunjia
-- created : 2026-10-10T23:40:24.80212+00:00
-- url     : https://prove2.me/theorems/2ca598ea-c4f4-43a1-9d5e-1f9c7fcb85a1
-- title:
--   Algo2LeanLib.FibonacciMutableCascade definitions
-- statement:
--   Definitions and required structural lemmas from `Algo2LeanLib.FibonacciMutableCascade`. Source declarations are retained by compiler-reported ranges; imports are redirected to the corresponding definition bundles. This bundle contains no theorem stubs.
--
--   <!-- algo2lean-provenance-v0.1.4 -->
--   **[Algo2Lean](https://www.algo2lean.com/) provenance and reproduction.** These definitions target [Algo2Lean](https://www.algo2lean.com/) v0.1.4, using the compiler source at [public commit `0f79d5e4242e6477531c9ee4410409f5b1c92f76`](https://github.com/lunjiah/algo2lean/tree/0f79d5e4242e6477531c9ee4410409f5b1c92f76), and Lean 4.33.1. The versioned compiler location is [Algo2Lean v0.1.4](https://www.algo2lean.com/versions/v0.1.4/). Compile all supplied `.algo` files and imports to reproduce the raw generated definitions. Release publication and exact website parity require their separately recorded checks; this metadata alone does not assert them. Prove2Me imports and declaration packaging are mechanically adapted, with original hashes, compiler-reported source ranges, and adaptations recorded in transplant provenance. Exact reproduction does not prove the compiler correct.
-- source:
--   https://github.com/lunjiah/algo2lean/blob/0f79d5e4242e6477531c9ee4410409f5b1c92f76/Algo2LeanLib/FibonacciMutableCascade.lean

import Definitions.Def_Algo2LeanLib_FibonacciStoredContext
import Definitions.Def_Algo2LeanLib_FibonacciRootInsertion

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true



set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

namespace Algo2Lean.Fibonacci

/-- The two existing root addresses touched by `add_root` are actual roots. -/
def Snapshot.RootEndpoints (state : Snapshot) : Prop :=
  0 ≤ state.minimum → state.parents state.minimum = -1 ∧ state.parents (state.right state.minimum) = -1









/-- The exact local mutation performed by the source `cut` helper. -/
def Snapshot.cut (state : Snapshot) (child parent : Int) : Snapshot :=
  (state.removeChild child parent).addRoot child







/-- Finite structural storage during a cascade. Rank and heap-order restoration
    are proved at the boundary; transient child-loss states need not satisfy them. -/
structure StoredForest (state : Snapshot) (forest : Forest) : Prop where
  unique : forest.Unique
  stored : ∀ root ∈ forest, Stored state (-1) root
  nonnegative : ∀ vertex key, (vertex, key) ∈ forest.entries → 0 ≤ vertex











/-- The actual parent/mark control flow of cascading_cut, abstracted only from
    sequence references and clock increments. Each cut is the exact Snapshot effect. -/
inductive CascadeRun : Snapshot → Snapshot → Int → Nat → Prop where
  | root {state : Snapshot} {vertex : Int} (root : state.parents vertex < 0) :
      CascadeRun state state vertex 0
  | mark {state : Snapshot} {vertex : Int} (nonroot : 0 ≤ state.parents vertex)
      (unmarked : state.marks vertex = 0) :
      CascadeRun state (state.setMark vertex true) vertex 0
  | cut {state final : Snapshot} {vertex : Int} {cuts : Nat}
      (nonroot : 0 ≤ state.parents vertex) (marked : state.marks vertex ≠ 0)
      (next : CascadeRun (state.cut vertex (state.parents vertex)) final (state.parents vertex) cuts) :
      CascadeRun state final vertex (cuts + 1)





end Algo2Lean.Fibonacci


