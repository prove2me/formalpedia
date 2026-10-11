-- Prove2me | Definitions.Def_Algo2LeanLib_KruskalMath_PrimExtension
-- name    : Algo2LeanLib_KruskalMath_PrimExtension
-- status  : Definition
-- author  : @lunjia
-- created : 2026-10-11T01:08:09.559101+00:00
-- url     : https://prove2.me/theorems/03a1d5a6-b66e-44ec-82c8-cfcb2c3d70ef
-- title:
--   Algo2LeanLib.KruskalMath additional definitions
-- statement:
--   Definitions and required structural lemmas from `Algo2LeanLib.KruskalMath`. Source declarations are retained by compiler-reported ranges; imports are redirected to the corresponding definition bundles. This bundle contains no theorem stubs.
--   This extension adds declarations required by Prim while importing the unchanged published definition bundle.
--
--   <!-- algo2lean-provenance-v0.1.4 -->
--   **[Algo2Lean](https://www.algo2lean.com/) provenance and reproduction.** These definitions target [Algo2Lean](https://www.algo2lean.com/) v0.1.4, using the compiler source at [public commit `0f79d5e4242e6477531c9ee4410409f5b1c92f76`](https://github.com/lunjiah/algo2lean/tree/0f79d5e4242e6477531c9ee4410409f5b1c92f76), and Lean 4.33.1. The versioned compiler location is [Algo2Lean v0.1.4](https://www.algo2lean.com/versions/v0.1.4/). Compile all supplied `.algo` files and imports to reproduce the raw generated definitions. Release publication and exact website parity require their separately recorded checks; this metadata alone does not assert them. Prove2Me imports and declaration packaging are mechanically adapted, with original hashes, compiler-reported source ranges, and adaptations recorded in transplant provenance. Exact reproduction does not prove the compiler correct.
-- source:
--   https://github.com/lunjiah/algo2lean/blob/d832a5655d7cac6d032e728a4798128147b27922/Algo2LeanLib/KruskalMath.lean

import Definitions.Def_Algo2LeanLib_KruskalMath
import Std

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true



set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

/-!
Finite undirected graph mathematics for Kruskal's algorithm. Edge identities
separate parallel input occurrences. Endpoints and weights are integers; weights
may be negative. This module does not depend on a union-find implementation or
on generated algorithm definitions.
-/

namespace Algo2Lean.Kruskal














































































































/-- Connectivity includes all declared vertices, including isolated vertices. -/
def ConnectedOn (size : Nat) (edges : List Edge) : Prop :=
  ∀ u v, 0 ≤ u → u < size → 0 ≤ v → v < size → Connected edges u v

/-- On a nonempty connected input graph, a minimum spanning forest is a minimum
    spanning tree. The vertex range is explicit so isolated vertices are not lost. -/
def MinimumSpanningTree (size : Nat) (input selected : List Edge) : Prop :=
  0 < size ∧ ValidInput size input ∧
    MinimumSpanningForest input selected ∧ ConnectedOn size selected





end Algo2Lean.Kruskal


