-- Prove2me | Definitions.Def_SubmissionAnalysis_Kruskal
-- name    : SubmissionAnalysis_Kruskal
-- status  : Definition
-- author  : @lunjia
-- created : 2026-10-10T23:54:11.344875+00:00
-- url     : https://prove2.me/theorems/d4f5655f-bc11-4aa8-ad39-40439f130a4e
-- title:
--   Kruskal: inverse-Ackermann running-time growth scale
-- statement:
--   The noncomputable definition `CLRS.Kruskal.runtimeScale V E = V + 1 + E * (Nat.log2 (E + 1) + Algo2Lean.Ackermann.alpha V + 1)` separates initialization, edge sorting and inverse-Ackermann union-find work. Additions by one handle empty and small inputs. The function alpha is the separately defined inverse-Ackermann function, not a new assumption.
--
--   <!-- algo2lean-supplemental-source -->
--   This supplemental handwritten analysis is separate from the released compiler source. Its additional analysis archive location is [here](https://github.com/lunjiah/algo2lean/releases/download/v0.1.4/algo2lean-clrs-analysis.zip), file `SubmissionAnalysis/Kruskal.lean` (SHA-256 `31533c2285238e53767bc6de90bc1566d00a73cc32c15629c14f0b68b081b640`). Publication and archive verification are tracked separately; the source is not raw compiler output.
--
--   <!-- algo2lean-provenance-v0.1.4 -->
--   **[Algo2Lean](https://www.algo2lean.com/) provenance and reproduction.** These definitions target [Algo2Lean](https://www.algo2lean.com/) v0.1.4, using the compiler source at [public commit `0f79d5e4242e6477531c9ee4410409f5b1c92f76`](https://github.com/lunjiah/algo2lean/tree/0f79d5e4242e6477531c9ee4410409f5b1c92f76), and Lean 4.33.1. The versioned compiler location is [Algo2Lean v0.1.4](https://www.algo2lean.com/versions/v0.1.4/). Compile all supplied `.algo` files and imports to reproduce the raw generated definitions. Release publication and exact website parity require their separately recorded checks; this metadata alone does not assert them. Prove2Me imports and declaration packaging are mechanically adapted, with original hashes, compiler-reported source ranges, and adaptations recorded in transplant provenance. Exact reproduction does not prove the compiler correct.
-- source:
--   https://github.com/lunjiah/algo2lean/releases/download/v0.1.4/algo2lean-clrs-analysis.zip

import Definitions.Def_Algo_kruskal_Analysis

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true



/-!
Supplemental analysis for the Algo2Lean CLRS formalization series.
This file proves a uniform-constant corollary of the exact bound;
it does not change the algorithm or its generated definitions.
-/
namespace CLRS.Kruskal

open Algo2LeanGenerated

/-- Edge sorting plus initialization and inverse-Ackermann union-find work.
The additions by one keep the bound meaningful for empty and small inputs. -/
noncomputable def runtimeScale (vertices edges : Nat) : Nat :=
  vertices + 1 + edges * ((edges + 1).log2 + Algo2Lean.Ackermann.alpha vertices + 1)





end CLRS.Kruskal


