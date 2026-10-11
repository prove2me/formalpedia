-- Prove2me | Definitions.Def_Algo_kruskal_Analysis
-- name    : Algo_kruskal_Analysis
-- status  : Definition
-- author  : @lunjia
-- created : 2026-10-10T23:53:35.541962+00:00
-- url     : https://prove2.me/theorems/06a2c2bf-e377-409b-b071-e244498b70ee
-- title:
--   Kruskal output selection and explicit runtime bound
-- statement:
--   This bundle provides the definitions used in the main Kruskal statements. `selectedEdges` interprets returned flags at the finite input edge identifiers. `runtime` sums the eight named sorting, heap, union-find and scan clocks with unit weights. **`KruskalAnalysis.runtimeBound V E`** is the exact finite bound below.
--
--   For $V$ vertices and $E$ edges, define
--   $$
--   B(V,E)=2E\bigl(3\lfloor\log_2(E+1)\rfloor+2\bigr)+V+2+E\bigl(10\alpha(V)+14\bigr).
--   $$
--   The eight unit-weight clocks are `sort_steps`, `heap_comparisons`, `heap_swaps`, `uf_init`, `uf_find`, `uf_compress`, `uf_union`, and `kruskal`. Their sum is `KruskalAnalysis.runtime`; the displayed expression is `KruskalAnalysis.runtimeBound`. Thus the finite inequality has scale $O(V+E\log(E+1)+E\alpha(V))$. The inverse-Ackermann improvement is in the disjoint-set term; sorting still costs $O(E\log(E+1))$.
--
--   Costs count the named source ticks over mathematical integers and total integer-indexed sequences. They are not wall-clock time, bit complexity, or a count of every arithmetic operation, access, allocation, or compiler transition. Counters may start at arbitrary values; bounds refer to the increments during this call.
--
--   The inverse-Ackermann function is `Algo2Lean.Ackermann.alpha` in its dedicated arithmetic definition bundle. The main correctness and cost claims are separate theorem nodes; a definition of a bound is not an assumption that the execution satisfies it.
--
--   <!-- algo2lean-provenance-v0.1.4 -->
--   **[Algo2Lean](https://www.algo2lean.com/) provenance and reproduction.** These definitions target [Algo2Lean](https://www.algo2lean.com/) v0.1.4, using the compiler source at [public commit `0f79d5e4242e6477531c9ee4410409f5b1c92f76`](https://github.com/lunjiah/algo2lean/tree/0f79d5e4242e6477531c9ee4410409f5b1c92f76), and Lean 4.33.1. The versioned compiler location is [Algo2Lean v0.1.4](https://www.algo2lean.com/versions/v0.1.4/). Compile all supplied `.algo` files and imports to reproduce the raw generated definitions. Release publication and exact website parity require their separately recorded checks; this metadata alone does not assert them. Prove2Me imports and declaration packaging are mechanically adapted, with original hashes, compiler-reported source ranges, and adaptations recorded in transplant provenance. Exact reproduction does not prove the compiler correct.
-- source:
--   https://github.com/lunjiah/algo2lean/blob/0f79d5e4242e6477531c9ee4410409f5b1c92f76/examples/kruskal/analysis/kruskal.lean

import Definitions.Def_Algo_kruskal_scan_Analysis
import Definitions.Def_Algo_kruskal_input_Analysis
import Definitions.Def_Algo_kruskal_clocks_Analysis

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true



set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

/-!
Kruskal's algorithm on finite undirected weighted graphs. The public interface
uses integer sequences for source vertices, target vertices, edge weights, and
returned selection flags. Correctness and running time reuse the independent
sorting, union-find, and graph analyses.
-/

namespace KruskalAnalysis

open Algo2LeanGenerated Algo.kruskal Algo2Lean.Kruskal
open KruskalInput

/-- Unit weights for sorting, heap operations, union-find operations, and edge
    scanning. Arithmetic and infinite-sequence access use the source cost model. -/
def runtime (costs : Clocks) : Nat := SortIndicesAnalysis.runtime costs + work costs

/-- Sorting costs O(E log E); the separately verified union-find contract makes
    the remaining work O(V + E alpha(V)), including initialization and scanning. -/
noncomputable def runtimeBound (vertices edges : Nat) : Nat :=
  SortIndicesAnalysis.runtimeBound edges + vertices + 2 + edges * (10 * Algo2Lean.Ackermann.alpha vertices + 14)




















/-- Input edges whose returned selection flag is one, in original input order. -/
def selectedEdges (sources targets weights flags : Seq) (count : Int) : List Edge :=
  (edges sources targets weights count).filter (fun edge => flags edge.id == 1)

@[simp] theorem load_sources (size count : Int) (sources targets weights : Seq) :
    (kruskal.load (size, sources, targets, weights, count)).1.read 0 = sources := rfl
@[simp] theorem load_targets (size count : Int) (sources targets weights : Seq) :
    (kruskal.load (size, sources, targets, weights, count)).1.read 1 = targets := rfl
@[simp] theorem load_weights (size count : Int) (sources targets weights : Seq) :
    (kruskal.load (size, sources, targets, weights, count)).1.read 2 = weights := rfl
@[simp] theorem load_clocks (size count : Int) (sources targets weights : Seq) :
    (kruskal.load (size, sources, targets, weights, count)).1.clocks = fun _ => 0 := rfl







-- Main result: Correctness


-- Main result: Running time




end KruskalAnalysis


