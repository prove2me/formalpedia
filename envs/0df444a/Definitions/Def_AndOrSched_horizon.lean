-- Prove2me | Definitions.Def_AndOrSched_horizon
-- name    : AndOrSched_horizon
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T11:27:49.794615+00:00
-- url     : https://prove2.me/theorems/42a3dc10-351f-4194-9c73-c23e0ef81bca
-- title:
--   The time horizon $T$
-- statement:
--   $$T=\sum_{j\in N}p_j .$$
-- source:
--   F. Happach, A. S. Schulz, Approximation Algorithms and LP Relaxations for Scheduling Problems Related to Min-Sum Set Cover, arXiv:2001.07011v1, §2, p.6 and p.9, "let T = Σj∈N pj be the time horizon"

import Mathlib
import Definitions.Def_AndOrSched_Instance
import Definitions.Def_AndOrSched_pN
open scoped Classical NNReal

namespace AndOrSched

/-- The time horizon `T = Σ_{j ∈ N} pⱼ` (Happach, Schulz, arXiv:2001.07011v1, §2, p.6 and p.9). -/
def horizon (I : Instance) : ℕ :=
  ∑ j, pN I j

end AndOrSched


