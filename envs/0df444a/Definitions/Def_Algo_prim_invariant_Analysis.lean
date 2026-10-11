-- Prove2me | Definitions.Def_Algo_prim_invariant_Analysis
-- name    : Algo_prim_invariant_Analysis
-- status  : Definition
-- author  : @lunjia
-- created : 2026-10-11T01:09:09.272742+00:00
-- url     : https://prove2.me/theorems/b52935c0-1773-48f6-b087-4756d1ce1e55
-- title:
--   Algo.prim.invariant.Analysis definitions
-- statement:
--   Definitions and required structural lemmas from `Algo.prim.invariant.Analysis`. Source declarations are retained by compiler-reported ranges; imports are redirected to the corresponding definition bundles. This bundle contains no theorem stubs.
--
--   <!-- algo2lean-provenance-v0.1.4 -->
--   **[Algo2Lean](https://www.algo2lean.com/) provenance and reproduction.** These definitions target [Algo2Lean](https://www.algo2lean.com/) v0.1.4, using the compiler source at [public commit `0f79d5e4242e6477531c9ee4410409f5b1c92f76`](https://github.com/lunjiah/algo2lean/tree/0f79d5e4242e6477531c9ee4410409f5b1c92f76), and Lean 4.33.1. The versioned compiler location is [Algo2Lean v0.1.4](https://www.algo2lean.com/versions/v0.1.4/). Compile all supplied `.algo` files and imports to reproduce the raw generated definitions. Release publication and exact website parity require their separately recorded checks; this metadata alone does not assert them. Prove2Me imports and declaration packaging are mechanically adapted, with original hashes, compiler-reported source ranges, and adaptations recorded in transplant provenance. Exact reproduction does not prove the compiler correct.
-- source:
--   https://github.com/lunjiah/algo2lean/blob/d832a5655d7cac6d032e728a4798128147b27922/examples/analysis/prim/invariant.lean

import Definitions.Def_Algo_prim_math_Analysis

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true



/-!
Prim's whole-loop invariant and its parent-sequence output specification.
The proof separates the first root extraction from ordinary light-edge choices,
then reuses the cut theorem and adjacency-scan lemmas at every iteration.
-/

namespace Algo2Lean.Prim

open Algo2Lean.Kruskal

/-- Parent pointers encode a minimum spanning tree rooted at the supplied root.
The root has parent `-1`; every other declared vertex has a selected incoming
edge whose source is its parent. All chosen edges belong to the input graph. -/
def SpanningParents (size : Nat) (input : List Edge) (root : Int) (parent : Int → Int) : Prop :=
  ∃ chosen, MinimumSpanningTree size input chosen ∧ parent root = -1 ∧
    (∀ edge ∈ chosen, parent edge.target = edge.source ∧ edge.target ≠ root) ∧
    (∀ vertex : Int, 0 ≤ vertex → vertex < size → vertex ≠ root →
      ∃ edge ∈ chosen, edge.target = vertex)

/-- The first iteration starts from no selected vertices. Later iterations
maintain a safe rooted tree, its boundary keys, and its parent representation. -/
structure Invariant (input : List Edge) (root : Int) (visited : Int → Prop)
    (key parent : Int → Int) (chosen : List Edge) : Prop where
  keys : Keys input visited key parent
  tree : ((∀ vertex, ¬ visited vertex) ∧ chosen = [] ∧ (∀ vertex, parent vertex = -1)) ∨
    TreeState input root visited chosen
  root_parent : parent root = -1
  parents : ∀ edge ∈ chosen, parent edge.target = edge.source ∧ edge.target ≠ root
  targets : ∀ vertex, (visited vertex ∧ vertex ≠ root) ↔ ∃ edge ∈ chosen, edge.target = vertex









-- Main result: Correctness


end Algo2Lean.Prim


