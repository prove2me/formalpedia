-- Prove2me | Definitions.Def_Algo_kruskal_sorted_Analysis
-- name    : Algo_kruskal_sorted_Analysis
-- status  : Definition
-- author  : @lunjia
-- created : 2026-10-11T01:53:22.437808+00:00
-- url     : https://prove2.me/theorems/35ead984-bc8b-44b2-955e-6ffa74886aae
-- title:
--   Algo.kruskal_sorted.Analysis definitions
-- statement:
--   Definitions and required structural lemmas from `Algo.kruskal_sorted.Analysis`. Source declarations are retained by compiler-reported ranges; imports are redirected to the corresponding definition bundles. This bundle contains no theorem stubs.
--
--   <!-- algo2lean-provenance-v0.1.4 -->
--   **[Algo2Lean](https://www.algo2lean.com/) provenance and reproduction.** These definitions target [Algo2Lean](https://www.algo2lean.com/) v0.1.4, using the compiler source at [public commit `0f79d5e4242e6477531c9ee4410409f5b1c92f76`](https://github.com/lunjiah/algo2lean/tree/0f79d5e4242e6477531c9ee4410409f5b1c92f76), and Lean 4.33.1. The versioned compiler location is [Algo2Lean v0.1.4](https://www.algo2lean.com/versions/v0.1.4/). Compile all supplied `.algo` files and imports to reproduce the raw generated definitions. Release publication and exact website parity require their separately recorded checks; this metadata alone does not assert them. Prove2Me imports and declaration packaging are mechanically adapted, with original hashes, compiler-reported source ranges, and adaptations recorded in transplant provenance. Exact reproduction does not prove the compiler correct.
-- source:
--   https://github.com/lunjiah/algo2lean/blob/9755b41d188977ae1aafdaf9eccdac0b0edb0420/examples/kruskal/analysis/kruskal_sorted.lean

import Definitions.Def_Algo_kruskal_scan_Analysis_SortedRevision
import Definitions.Def_Algo_kruskal_input_Analysis
import Definitions.Def_Algo_kruskal_sorted_clocks_Analysis

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true



set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

/-!
Kruskal after sorting: a caller supplies a permutation of the original edge
identifiers in nondecreasing weight order. The source allocates singleton
components and scans that order; it performs no sorting. The reusable Call
contract combines the graph exchange argument with the independently proved
inverse-Ackermann contracts for union by rank and full path compression.
-/

namespace KruskalSortedAnalysis

open Algo2LeanCore Algo2LeanGenerated
open Algo.kruskal_sorted Algo.kruskal_sorted.Algo2LeanGenerated
open Algo2Lean.Kruskal KruskalInput KruskalAnalysis

/-- The same eight source-event clocks used for the complete sorting algorithm.
    Sorting clocks have zero increments in this entry point. -/
def runtime (costs : Clocks) : Nat := SortIndicesAnalysis.runtime costs + work costs

/-- Initialization, the entry tick, and the amortized edge scan. -/
noncomputable def runtimeBound (vertices edges : Nat) : Nat :=
  vertices + 2 + edges * (10 * Algo2Lean.Ackermann.alpha vertices + 14)

/-- A uniform asymptotic scale, including the constant cost of empty inputs. -/
noncomputable def runtimeScale (vertices edges : Nat) : Nat :=
  vertices + 1 + edges * Algo2Lean.Ackermann.alpha vertices












-- Main result: Correctness and running time






@[simp] theorem load_sources (size count : Int) (sources targets weights order : Seq) :
    (kruskal_sorted.load (size, sources, targets, weights, count, order)).1.read 0 = sources := rfl
@[simp] theorem load_targets (size count : Int) (sources targets weights order : Seq) :
    (kruskal_sorted.load (size, sources, targets, weights, count, order)).1.read 1 = targets := rfl
@[simp] theorem load_weights (size count : Int) (sources targets weights order : Seq) :
    (kruskal_sorted.load (size, sources, targets, weights, count, order)).1.read 2 = weights := rfl
@[simp] theorem load_order (size count : Int) (sources targets weights order : Seq) :
    (kruskal_sorted.load (size, sources, targets, weights, count, order)).1.read 3 = order := rfl
@[simp] theorem load_clocks (size count : Int) (sources targets weights order : Seq) :
    (kruskal_sorted.load (size, sources, targets, weights, count, order)).1.clocks = fun _ => 0 := rfl













end KruskalSortedAnalysis


