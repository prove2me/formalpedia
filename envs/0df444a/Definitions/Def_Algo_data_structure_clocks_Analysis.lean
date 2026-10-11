-- Prove2me | Definitions.Def_Algo_data_structure_clocks_Analysis
-- name    : Algo_data_structure_clocks_Analysis
-- status  : Definition
-- author  : @lunjia
-- created : 2026-10-10T23:41:04.111871+00:00
-- url     : https://prove2.me/theorems/9d11f28b-fcff-43fc-8838-54a02bed70b6
-- title:
--   Imported heap and union-find clock bookkeeping
-- statement:
--   This bundle provides clock facts used when composing the actual compiled data-structure operations. It distinguishes the sorting/heap clocks from union-find clocks and describes preservation of counters outside an operation's tick set. These facts let the Kruskal proof add component costs while carrying arbitrary initial counters.
--
--   The nontrivial correctness and amortized bounds are separate theorem nodes. This bundle is bookkeeping over the same generated call semantics, not a replacement cost semantics.
--
--   <!-- algo2lean-provenance-v0.1.4 -->
--   **[Algo2Lean](https://www.algo2lean.com/) provenance and reproduction.** These definitions target [Algo2Lean](https://www.algo2lean.com/) v0.1.4, using the compiler source at [public commit `0f79d5e4242e6477531c9ee4410409f5b1c92f76`](https://github.com/lunjiah/algo2lean/tree/0f79d5e4242e6477531c9ee4410409f5b1c92f76), and Lean 4.33.1. The versioned compiler location is [Algo2Lean v0.1.4](https://www.algo2lean.com/versions/v0.1.4/). Compile all supplied `.algo` files and imports to reproduce the raw generated definitions. Release publication and exact website parity require their separately recorded checks; this metadata alone does not assert them. Prove2Me imports and declaration packaging are mechanically adapted, with original hashes, compiler-reported source ranges, and adaptations recorded in transplant provenance. Exact reproduction does not prove the compiler correct.
-- source:
--   https://github.com/lunjiah/algo2lean/blob/0f79d5e4242e6477531c9ee4410409f5b1c92f76/examples/kruskal/analysis/data_structure_clocks.lean

import Definitions.Def_Algo_union_find_Generated
import Definitions.Def_Algo_sort_indices_Generated
import Definitions.Def_Algo2LeanLib_CallCost

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true



set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

/-!
Clock monotonicity certificates for reusable union-find and sorting components.
Imported algorithms retain their own certificates; client proofs only compose them.
-/

namespace DataStructureClocks

open Algo2LeanCore Algo2LeanGenerated

@[simp] theorem resume_heap {Frame Result : Type} (heap : Heap)
    (result : Result) (caller : Stack Frame Result) :
    (resumeConfig heap result caller).heap = heap := by
  cases caller <;> rfl







end DataStructureClocks


