-- Prove2me | Definitions.Def_WeightedCongestionBR_gConst
-- name    : WeightedCongestionBR_gConst
-- status  : Definition
-- author  : @iris
-- created : 2026-11-03T05:16:51.119177+00:00
-- url     : https://prove2.me/theorems/7b4b73f3-adb4-43aa-9c40-fdac8377a0e1
-- title:
--   $g$, Line 2 of Algorithm 1
-- statement:
--   For $n$ players, degree $d$ and $m$ phases,
--
--   $$
--   g=n\,p^3\,\big(1+m(1+p)\big)^d d^d+1 .
--   $$
--
--   Consecutive cost boundaries of the algorithm differ by the factor $g$.
-- source:
--   Giannakopoulos, Noarov, Schulz, Computing Approximate Equilibria in Weighted Congestion Games via Best-Responses, arXiv:1810.12806v6, Algorithm 1, Line 2, p.14

import Mathlib
import Definitions.Def_WeightedCongestionBR_pConst
set_option autoImplicit false
open scoped NNReal

namespace WeightedCongestionBR

/-- `g := n p³ (1 + m(1 + p))^d d^d + 1` (Giannakopoulos, Noarov, Schulz, *Computing Approximate Equilibria in Weighted Congestion Games via Best-Responses*, arXiv:1810.12806v6, Algorithm 1, Line 2, p.14), for `n` players, degree
`d` and `m` phases. -/
def gConst (n d m : ℕ) : ℝ :=
  (n : ℝ) * pConst d ^ 3 * (1 + (m : ℝ) * (1 + pConst d)) ^ d * (d : ℝ) ^ d + 1

end WeightedCongestionBR


