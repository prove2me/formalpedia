-- Prove2me | Definitions.Def_MaxEntOCRS_alpha
-- name    : MaxEntOCRS_alpha
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T22:29:59.025534+00:00
-- url     : https://prove2.me/theorems/5e8e9d03-acf0-4b04-a51b-295af39168f3
-- title:
--   The selectability constant $\alpha = (\sqrt3 - 1)/2$
-- statement:
--   The constant
--   $$
--   \alpha = \frac{\sqrt3 - 1}{2} \approx 0.366 .
--   $$
--   It satisfies $2\alpha^2 + 2\alpha = 1$. It is the selectability guaranteed by Theorem 1 and the threshold of Theorem 2: if every vertex is covered with probability at most $\alpha$, every pair of vertices is simultaneously uncovered with probability at least $\alpha$.
-- source:
--   Chen–Wang, Optimal Maximum-Entropy Stationary Contention Resolution for General Matchings via a Sharp Two-Point Monomer–Dimer Inequality, STOC 2027 submission (manuscript sha256 06944af9…), Section 2, p.4 (opening display)

import Mathlib

namespace MaxEntOCRS

/-- The constant `α = (√3 − 1)/2 ≈ 0.366` (Chen–Wang, *Optimal Maximum-Entropy Stationary Contention Resolution for General Matchings via a Sharp Two-Point Monomer–Dimer Inequality*, STOC 2027 submission manuscript (sha256 06944af9…2d0462c), §2, p.4, opening display
"α = (√3−1)/2, β = 1 − α = √3 α, γ = 1 − 2α = 2α², C = 1/α = 1 + √3, c = α/β = 1/√3").
It is the selectability of Theorem 1 and the occupancy/vacancy threshold of Theorem 2. -/
noncomputable def alpha : ℝ := (Real.sqrt 3 - 1) / 2

end MaxEntOCRS


