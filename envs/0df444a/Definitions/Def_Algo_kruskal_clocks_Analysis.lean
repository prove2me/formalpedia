-- Prove2me | Definitions.Def_Algo_kruskal_clocks_Analysis
-- name    : Algo_kruskal_clocks_Analysis
-- status  : Definition
-- author  : @lunjia
-- created : 2026-10-10T23:51:09.748271+00:00
-- url     : https://prove2.me/theorems/f620925f-06f0-4cb7-9f7e-d7607610fa00
-- title:
--   Kruskal clock composition and monotonicity support
-- statement:
--   This bundle retains the supporting material needed to reason about nondecreasing source clocks across compiled Kruskal calls. Costs are increments of explicit ticks in the imported sorter, union-find and scan code. Monotonicity permits conversion of cumulative before/after bounds into bounds on `Heap.cost`, even when the caller's initial counters are nonzero.
--
--   The main runtime sum and explicit estimate are defined separately in `KruskalAnalysis.runtime` and `runtimeBound`; the final cost claim remains a theorem, not a primitive clock assumption.
--
--   <!-- algo2lean-provenance-v0.1.4 -->
--   **[Algo2Lean](https://www.algo2lean.com/) provenance and reproduction.** These definitions target [Algo2Lean](https://www.algo2lean.com/) v0.1.4, using the compiler source at [public commit `0f79d5e4242e6477531c9ee4410409f5b1c92f76`](https://github.com/lunjiah/algo2lean/tree/0f79d5e4242e6477531c9ee4410409f5b1c92f76), and Lean 4.33.1. The versioned compiler location is [Algo2Lean v0.1.4](https://www.algo2lean.com/versions/v0.1.4/). Compile all supplied `.algo` files and imports to reproduce the raw generated definitions. Release publication and exact website parity require their separately recorded checks; this metadata alone does not assert them. Prove2Me imports and declaration packaging are mechanically adapted, with original hashes, compiler-reported source ranges, and adaptations recorded in transplant provenance. Exact reproduction does not prove the compiler correct.
-- source:
--   https://github.com/lunjiah/algo2lean/blob/0f79d5e4242e6477531c9ee4410409f5b1c92f76/examples/kruskal/analysis/kruskal_clocks.lean

import Definitions.Def_Algo_kruskal_Generated
import Definitions.Def_Algo_data_structure_clocks_Analysis

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true



set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

/-!
Clock counters are monotone through every transition, including delegated calls.
These certificates make cost increments usable with arbitrary initial clocks.
They depend only on the compiled programs, not on graph or data-structure preconditions.
-/

namespace KruskalClocks

open Algo2LeanCore Algo2LeanGenerated DataStructureClocks





end KruskalClocks


