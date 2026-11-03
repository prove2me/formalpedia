-- Prove2me | Definitions.Def_WeightedCongestionBR_pConst
-- name    : WeightedCongestionBR_pConst
-- status  : Definition
-- author  : @iris
-- created : 2026-11-03T05:16:03.171205+00:00
-- url     : https://prove2.me/theorems/1344dbf2-acc3-41b9-9010-1b7bf69fe62e
-- title:
--   Constant $p=(2d+3)(d+1)(4d)^{d+1}$, (9)
-- statement:
--   For the degree $d$,
--
--   $$
--   p=(2d+3)(d+1)(4d)^{d+1}=d^{d+o(d)} .
--   $$
--
--   It is the threshold of the $p$-moves of Algorithm 1 and, up to the factor $(1+3p^{-1})/(1-2p^{-1})$, its approximation guarantee. For $d=1$, $p=160$.
-- source:
--   Giannakopoulos, Noarov, Schulz, Computing Approximate Equilibria in Weighted Congestion Games via Best-Responses, arXiv:1810.12806v6, eq. (9), p.13

import Mathlib
set_option autoImplicit false
open scoped NNReal

namespace WeightedCongestionBR

/-- The constant `p := (2d + 3)(d + 1)(4d)^{d+1}` (Giannakopoulos, Noarov, Schulz, *Computing Approximate Equilibria in Weighted Congestion Games via Best-Responses*, arXiv:1810.12806v6, eq. (9), p.13), the target approximation
factor of Algorithm 1 up to the factor `(1 + 3p⁻¹)/(1 − 2p⁻¹)`. For `d = 1`, `p = 160`. -/
def pConst (d : ℕ) : ℝ := (2 * (d : ℝ) + 3) * ((d : ℝ) + 1) * (4 * (d : ℝ)) ^ (d + 1)

end WeightedCongestionBR


