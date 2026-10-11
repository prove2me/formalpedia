-- Prove2me | Definitions.Def_Algo_kruskal_sorted_clocks_Analysis
-- name    : Algo_kruskal_sorted_clocks_Analysis
-- status  : Definition
-- author  : @lunjia
-- created : 2026-10-11T01:52:17.626044+00:00
-- url     : https://prove2.me/theorems/e6b0ba04-5236-4b5d-92a9-4e62a021e056
-- title:
--   Algo.kruskal_sorted_clocks.Analysis definitions
-- statement:
--   Definitions and required structural lemmas from `Algo.kruskal_sorted_clocks.Analysis`. Source declarations are retained by compiler-reported ranges; imports are redirected to the corresponding definition bundles. This bundle contains no theorem stubs.
--
--   <!-- algo2lean-provenance-v0.1.4 -->
--   **[Algo2Lean](https://www.algo2lean.com/) provenance and reproduction.** These definitions target [Algo2Lean](https://www.algo2lean.com/) v0.1.4, using the compiler source at [public commit `0f79d5e4242e6477531c9ee4410409f5b1c92f76`](https://github.com/lunjiah/algo2lean/tree/0f79d5e4242e6477531c9ee4410409f5b1c92f76), and Lean 4.33.1. The versioned compiler location is [Algo2Lean v0.1.4](https://www.algo2lean.com/versions/v0.1.4/). Compile all supplied `.algo` files and imports to reproduce the raw generated definitions. Release publication and exact website parity require their separately recorded checks; this metadata alone does not assert them. Prove2Me imports and declaration packaging are mechanically adapted, with original hashes, compiler-reported source ranges, and adaptations recorded in transplant provenance. Exact reproduction does not prove the compiler correct.
-- source:
--   https://github.com/lunjiah/algo2lean/blob/9755b41d188977ae1aafdaf9eccdac0b0edb0420/examples/kruskal/analysis/kruskal_sorted_clocks.lean

import Definitions.Def_Algo_kruskal_sorted_Generated
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

namespace KruskalSortedClocks

open Algo2LeanCore Algo2LeanGenerated DataStructureClocks





end KruskalSortedClocks


