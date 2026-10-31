-- Prove2me | Definitions.Def_DeltaSLearning_grid
-- name    : DeltaSLearning_grid
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T19:05:49.004451+00:00
-- url     : https://prove2.me/theorems/1f3f4222-d649-4353-a73c-277fdf00fff1
-- title:
--   Grid of inventory gaps $\delta_j=j\beta/J$
-- statement:
--   The algorithm discretizes the gap range $[0,\beta]$ into $J$ equally spaced points
--   $$\delta_j := \frac{j\beta}{J},\qquad j\in[J]=\{1,\dots,J\}.$$
-- source:
--   Yuan, Luo, Shi, Marrying SGD with Bandits, SSRN 3329611 (accepted manuscript, Management Science 2021, doi:10.1287/mnsc.2020.3799), §3.3 step (0a), p.13; Algorithm 1, p.15

import Mathlib

namespace DeltaSLearning

/-- The discretized inventory gaps `δ_j = j β / J`, `j ∈ [J] = {1, …, J}`.
Yuan, Luo, Shi, SSRN 3329611 (Management Science 2021, doi:10.1287/mnsc.2020.3799), §3.3 step (0a), p.13, and Algorithm 1, p.15. -/
noncomputable def grid (β : ℝ) (J j : ℕ) : ℝ :=
  (j : ℝ) * β / J

end DeltaSLearning


