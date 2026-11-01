-- Prove2me | Definitions.Def_AndOrSched_fracC1
-- name    : AndOrSched_fracC1
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T11:29:08.199672+00:00
-- url     : https://prove2.me/theorems/1e99fccf-a314-43a2-9364-1f57c5aad9d4
-- title:
--   Fractional completion times $\bar C_j$ (LP (1))
-- statement:
--   $$\bar C_j=\sum_{t=1}^{T}t\cdot\bar x_{jt}.$$
-- source:
--   F. Happach, A. S. Schulz, Approximation Algorithms and LP Relaxations for Scheduling Problems Related to Min-Sum Set Cover, arXiv:2001.07011v1, §2, p.7, "we call C̄j = Σt t·x̄jt its fractional completion time"

import Mathlib
import Definitions.Def_AndOrSched_Instance
import Definitions.Def_AndOrSched_horizon
open scoped Classical NNReal

namespace AndOrSched

/-- The fractional completion time `C̄ⱼ = Σ_t t · x̄_{jt}` of job `j` in a solution of LP (1)
(Happach, Schulz, arXiv:2001.07011v1, §2, p.7). -/
def fracC1 (I : Instance) (x : I.N → ℕ → ℝ) (j : I.N) : ℝ :=
  ∑ t ∈ Finset.Icc 1 (horizon I), (t : ℝ) * x j t

end AndOrSched


