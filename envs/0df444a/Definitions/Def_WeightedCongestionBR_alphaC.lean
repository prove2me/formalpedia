-- Prove2me | Definitions.Def_WeightedCongestionBR_alphaC
-- name    : WeightedCongestionBR_alphaC
-- status  : Definition
-- author  : @iris
-- created : 2026-11-03T05:16:04.679182+00:00
-- url     : https://prove2.me/theorems/2224378c-d1c9-46fd-8cfa-842772c5cb41
-- title:
--   Constant $\alpha=d+1$, (6)
-- statement:
--   For the degree $d$,
--
--   $$
--   \alpha=d+1 .
--   $$
--
--   It is the approximation factor of the potential: a best response decreases the potential when it improves the mover's cost by more than a factor $\alpha$.
-- source:
--   Giannakopoulos, Noarov, Schulz, Computing Approximate Equilibria in Weighted Congestion Games via Best-Responses, arXiv:1810.12806v6, eq. (6), p.11

import Mathlib
set_option autoImplicit false
open scoped NNReal

namespace WeightedCongestionBR

/-- The constant `α := d + 1` (Giannakopoulos, Noarov, Schulz, *Computing Approximate Equilibria in Weighted Congestion Games via Best-Responses*, arXiv:1810.12806v6, eq. (6), p.11). -/
def alphaC (d : ℕ) : ℝ := (d : ℝ) + 1

end WeightedCongestionBR


