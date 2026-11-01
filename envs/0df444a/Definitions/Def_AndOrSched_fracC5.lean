-- Prove2me | Definitions.Def_AndOrSched_fracC5
-- name    : AndOrSched_fracC5
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T11:30:19.590935+00:00
-- url     : https://prove2.me/theorems/7553d883-3469-4007-8bad-638eb33edc4c
-- title:
--   Fractional completion times $\bar C_j$ (LP (5))
-- statement:
--   $$\bar C_j=\sum_{l=1}^{L}\tau_{l-1}\,\bar x_{jl}.$$
-- source:
--   F. Happach, A. S. Schulz, Approximation Algorithms and LP Relaxations for Scheduling Problems Related to Min-Sum Set Cover, arXiv:2001.07011v1, §2, p.9, "let C̄j = Σl τl−1 x̄jl"

import Mathlib
import Definitions.Def_AndOrSched_Instance
import Definitions.Def_AndOrSched_numIntervals
import Definitions.Def_AndOrSched_tau
open scoped Classical NNReal

namespace AndOrSched

/-- The fractional completion time `C̄ⱼ = Σ_l τ_{l−1} x̄_{jl}` of job `j` in a solution of LP (5)
(Happach, Schulz, arXiv:2001.07011v1, §2, p.9). -/
noncomputable def fracC5 (I : Instance) (ε' : ℝ) (x : I.N → ℕ → ℝ) (j : I.N) : ℝ :=
  ∑ l ∈ Finset.Icc 1 (numIntervals I ε'), tau ε' (l - 1) * x j l

end AndOrSched


