-- Prove2me | Definitions.Def_AndOrSched_numIntervals
-- name    : AndOrSched_numIntervals
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T11:29:00.405222+00:00
-- url     : https://prove2.me/theorems/45574ba2-0b99-4d68-9f5c-bf37c1e62dd4
-- title:
--   The number of intervals $L$
-- statement:
--   $L$ is the least $L\ge1$ with $(1+\varepsilon')^{L-1}\ge T$.
-- source:
--   F. Happach, A. S. Schulz, Approximation Algorithms and LP Relaxations for Scheduling Problems Related to Min-Sum Set Cover, arXiv:2001.07011v1, §2, p.9, "let L be minimal such that (1 + ε′)^(L−1) ≥ T"

import Mathlib
import Definitions.Def_AndOrSched_Instance
import Definitions.Def_AndOrSched_horizon
open scoped Classical NNReal

namespace AndOrSched

/-- The number of intervals `L` of LP (5) (Happach, Schulz, arXiv:2001.07011v1, §2, p.9, "let L be minimal such that
(1 + ε′)^(L−1) ≥ T").

**Formalization Note** `L ≥ 1` is required so that `[L]` is nonempty (this only matters when
`T ≤ 1`). For `ε' > 0` the set is nonempty and `L` is its least element. -/
noncomputable def numIntervals (I : Instance) (ε' : ℝ) : ℕ :=
  sInf {L : ℕ | 1 ≤ L ∧ (horizon I : ℝ) ≤ (1 + ε') ^ (L - 1)}

end AndOrSched


