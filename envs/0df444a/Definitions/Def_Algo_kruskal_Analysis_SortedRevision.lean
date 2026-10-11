-- Prove2me | Definitions.Def_Algo_kruskal_Analysis_SortedRevision
-- name    : Algo_kruskal_Analysis_SortedRevision
-- status  : Definition
-- author  : @lunjia
-- created : 2026-10-11T01:54:12.395143+00:00
-- url     : https://prove2.me/theorems/d84a417e-377e-4a9b-b4eb-a983d312980f
-- title:
--   Algo.kruskal.Analysis definitions
-- statement:
--   Definitions and required structural lemmas from `Algo.kruskal.Analysis`. Source declarations are retained by compiler-reported ranges; imports are redirected to the corresponding definition bundles. This bundle contains no theorem stubs.
--
--   <!-- algo2lean-provenance-v0.1.4 -->
--   **[Algo2Lean](https://www.algo2lean.com/) provenance and reproduction.** These definitions target [Algo2Lean](https://www.algo2lean.com/) v0.1.4, using the compiler source at [public commit `0f79d5e4242e6477531c9ee4410409f5b1c92f76`](https://github.com/lunjiah/algo2lean/tree/0f79d5e4242e6477531c9ee4410409f5b1c92f76), and Lean 4.33.1. The versioned compiler location is [Algo2Lean v0.1.4](https://www.algo2lean.com/versions/v0.1.4/). Compile all supplied `.algo` files and imports to reproduce the raw generated definitions. Release publication and exact website parity require their separately recorded checks; this metadata alone does not assert them. Prove2Me imports and declaration packaging are mechanically adapted, with original hashes, compiler-reported source ranges, and adaptations recorded in transplant provenance. Exact reproduction does not prove the compiler correct.
-- source:
--   https://github.com/lunjiah/algo2lean/blob/9755b41d188977ae1aafdaf9eccdac0b0edb0420/examples/kruskal/analysis/kruskal.lean

import Definitions.Def_Algo_kruskal_sorted_Analysis
import Definitions.Def_Algo_kruskal_clocks_Analysis_SortedRevision
import Definitions.Def_Algo_kruskal_Facts_SortedRevision
import Definitions.Def_Algo_kruskal_bounds_Analysis

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true



set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

/-!
Kruskal's complete algorithm sorts edge identifiers, then calls the independently
verified sorted-edge entry point. The two runtime results distinguish the total
work from work after sorting. Both reuse the same union-by-rank and full path
compression contracts and apply from arbitrary caller counters.
-/

namespace KruskalAnalysis

open Algo2LeanCore Algo2LeanGenerated Algo.kruskal Algo2Lean.Kruskal
open KruskalInput

/-- The total of the eight source-event clocks, shared by both entry points. -/
abbrev runtime := KruskalSortedAnalysis.runtime

/-- Exact sorting budget plus the independently proved post-sorting budget. -/
noncomputable def runtimeBound (vertices edges : Nat) : Nat :=
  SortIndicesAnalysis.runtimeBound edges + KruskalSortedAnalysis.runtimeBound vertices edges

/-- The sorting term absorbs the inverse-Ackermann contribution. The constant
    unit covers empty inputs, while V retains the cost of isolated vertices. -/
def runtimeScale (vertices edges : Nat) : Nat :=
  vertices + 1 + edges * (edges + 1).log2



















-- Main result: Running time (total)







@[simp] theorem load_sources (size count : Int) (sources targets weights : Seq) :
    (kruskal.load (size, sources, targets, weights, count)).1.read 0 = sources := rfl
@[simp] theorem load_targets (size count : Int) (sources targets weights : Seq) :
    (kruskal.load (size, sources, targets, weights, count)).1.read 1 = targets := rfl
@[simp] theorem load_weights (size count : Int) (sources targets weights : Seq) :
    (kruskal.load (size, sources, targets, weights, count)).1.read 2 = weights := rfl
@[simp] theorem load_clocks (size count : Int) (sources targets weights : Seq) :
    (kruskal.load (size, sources, targets, weights, count)).1.clocks = fun _ => 0 := rfl







-- Main result: Correctness






-- Main result: Running time (after sorting)


end KruskalAnalysis


