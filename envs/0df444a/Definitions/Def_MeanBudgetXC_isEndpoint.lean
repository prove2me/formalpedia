-- Prove2me | Definitions.Def_MeanBudgetXC_isEndpoint
-- name    : MeanBudgetXC_isEndpoint
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T05:40:20.945949+00:00
-- url     : https://prove2.me/theorems/b141129d-9924-4a6d-b780-7caeb782a239
-- title:
--   Path endpoints of the host graph
-- statement:
--   A vertex of the host graph is a **path endpoint** when it is $v_{i,0}$ or $v_{i,1}$ for some source variable $i$. The interaction edges are exactly the edges joining two path endpoints.
-- source:
--   Chao–Gao–Qi–Wang, A Sharp Mean-Budget Transition for Local Pair Marginals, STOC 2027 submission (manuscript sha256 882d9c71…), Section 4.3, p.19

import Mathlib
import Definitions.Def_MeanBudgetXC_HostV

namespace MeanBudgetXC

variable {n₀ t ℓ c niso : ℕ}

/-- A host vertex is a **path endpoint** `v_{i,0}` or `v_{i,1}` (Chao–Gao–Qi–Wang, *A Sharp Mean-Budget Transition for Local Pair Marginals*, STOC 2027
submission, manuscript sha256 882d9c71…9e76, Section 4.3, p.19). -/
def isEndpoint : HostV n₀ t ℓ c niso → Bool
  | .inl (_, _, k) => decide (k = 0 ∨ k = 3)
  | _ => false

end MeanBudgetXC


