-- Prove2me | Definitions.Def_AndOrSched_cost
-- name    : AndOrSched_cost
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T11:26:58.182445+00:00
-- url     : https://prove2.me/theorems/261f49ea-d5b1-4833-8e6a-ad35e78066f0
-- title:
--   The objective $\sum_j w_jC_j$
-- statement:
--   The cost of a schedule $C$ is the sum of weighted completion times
--   $$\sum_{j\in N}w_jC_j .$$
-- source:
--   F. Happach, A. S. Schulz, Approximation Algorithms and LP Relaxations for Scheduling Problems Related to Min-Sum Set Cover, arXiv:2001.07011v1, §1, p.2, "minimizes the sum of weighted completion times"

import Mathlib
import Definitions.Def_AndOrSched_Instance
open scoped Classical NNReal

namespace AndOrSched

/-- The objective `Σ_{j ∈ N} wⱼ Cⱼ`, the sum of weighted completion times (Happach, Schulz, arXiv:2001.07011v1, §1, p.2). -/
def cost (I : Instance) (C : I.N → ℝ) : ℝ :=
  ∑ j, (I.w j : ℝ) * C j

end AndOrSched


