-- Prove2me | Definitions.Def_SubmissionAnalysis_FibonacciDijkstra
-- name    : SubmissionAnalysis_FibonacciDijkstra
-- status  : Definition
-- author  : @lunjia
-- created : 2026-10-10T23:54:00.126384+00:00
-- url     : https://prove2.me/theorems/8ff37fe3-7819-4470-bb81-a545cfd81d74
-- title:
--   Fibonacci Dijkstra: running-time growth scale
-- statement:
--   The definition `CLRS.FibonacciDijkstra.runtimeScale V E = E + 1 + V * (Nat.log2 V + 1)` expresses the growth of the thirteen selected source clocks. It has scale O(E + V log V); additions by one handle small instances. This supplemental analysis does not change any compiled algorithm definition.
--
--   <!-- algo2lean-supplemental-source -->
--   This supplemental handwritten analysis is separate from the released compiler source. Its additional analysis archive location is [here](https://github.com/lunjiah/algo2lean/releases/download/v0.1.4/algo2lean-clrs-analysis.zip), file `SubmissionAnalysis/FibonacciDijkstra.lean` (SHA-256 `0f0948f6ed2b4e461ca95bea606aa06eff534af028a0f893f42468e93dd9950d`). Publication and archive verification are tracked separately; the source is not raw compiler output.
--
--   <!-- algo2lean-provenance-v0.1.4 -->
--   **[Algo2Lean](https://www.algo2lean.com/) provenance and reproduction.** These definitions target [Algo2Lean](https://www.algo2lean.com/) v0.1.4, using the compiler source at [public commit `0f79d5e4242e6477531c9ee4410409f5b1c92f76`](https://github.com/lunjiah/algo2lean/tree/0f79d5e4242e6477531c9ee4410409f5b1c92f76), and Lean 4.33.1. The versioned compiler location is [Algo2Lean v0.1.4](https://www.algo2lean.com/versions/v0.1.4/). Compile all supplied `.algo` files and imports to reproduce the raw generated definitions. Release publication and exact website parity require their separately recorded checks; this metadata alone does not assert them. Prove2Me imports and declaration packaging are mechanically adapted, with original hashes, compiler-reported source ranges, and adaptations recorded in transplant provenance. Exact reproduction does not prove the compiler correct.
-- source:
--   https://github.com/lunjiah/algo2lean/releases/download/v0.1.4/algo2lean-clrs-analysis.zip

import Definitions.Def_Algo_dijkstra_dijkstra_fibonacci_Analysis

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true



/-!
Supplemental analysis for the Algo2Lean CLRS formalization series.
This file proves a uniform-constant corollary of the exact bound;
it does not change the algorithm or its generated definitions.
-/
namespace CLRS.FibonacciDijkstra

open Algo2LeanGenerated Algo2Lean.Dijkstra

/-- The growth scale for the selected source clocks. The additions by one
keep the bound meaningful for small vertex and edge counts. -/
def runtimeScale (vertices edges : Nat) : Nat :=
  edges + 1 + vertices * (vertices.log2 + 1)





end CLRS.FibonacciDijkstra


