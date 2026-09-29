-- Prove2me | Definitions.Def_BinPacking_FirstFit_W
-- name    : BinPacking_FirstFit_W
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-26T22:04:59.382353+00:00
-- url     : https://prove2.me/theorems/7411f119-1e63-412f-b90d-930a916a9d06
-- title:
--   The weighting function $W:[0,1]\to[0,1]$ of the First-Fit analysis
-- statement:
--   The weighting function $W:[0,1]\to[0,1]$ used in the proof that First-Fit and Best-Fit use at most $1.7L^*+2$ bins is the piecewise linear function
--
--   $$
--   W(\alpha)=\begin{cases}
--   \tfrac65\alpha, & 0\le\alpha\le\tfrac16,\\[2pt]
--   \tfrac95\alpha-\tfrac1{10}, & \tfrac16<\alpha\le\tfrac13,\\[2pt]
--   \tfrac65\alpha+\tfrac1{10}, & \tfrac13<\alpha\le\tfrac12,\\[2pt]
--   1, & \tfrac12<\alpha\le 1.
--   \end{cases}
--   $$
--
--   It is continuous on $[0,\tfrac12]$, with $W(\tfrac16)=\tfrac15$, $W(\tfrac13)=\tfrac12$, $W(\tfrac12)=\tfrac7{10}$, and jumps to $1$ just above $\tfrac12$. The weight of a list is the sum of the weights of its elements; the analysis compares the number of bins with the total weight.
--
--   **Formalization Note** `W` is a function `ℝ → ℝ`. Outside $[0,1]$ its values ($\tfrac65\alpha$ for $\alpha<0$, $1$ for $\alpha>1$) are not the paper's and are never used: every statement applies `W` only to elements of lists in $(0,1]$.
-- source:
--   Johnson, Demers, Ullman, Garey, Graham, Worst-Case Performance Bounds for Simple One-Dimensional Packing Algorithms, SIAM J. Comput. 3(4) (1974), p. 304, Section 2, proof of Theorem 2.2 (definition of W, Fig. 2)

import Mathlib

namespace BinPacking.FirstFit

/-- The weighting function `W : [0, 1] → [0, 1]` of the proof of Theorem 2.2 (p. 304, Fig. 2):
`W(α) = (6/5)α` for `0 ≤ α ≤ 1/6`, `(9/5)α − 1/10` for `1/6 < α ≤ 1/3`,
`(6/5)α + 1/10` for `1/3 < α ≤ 1/2`, and `1` for `1/2 < α ≤ 1`.
As a function `ℝ → ℝ` its values outside `[0, 1]` are not the paper's (`(6/5)α` below `0`,
`1` above `1`); every statement restricts its arguments to `(0, 1]`. -/
noncomputable def W (α : ℝ) : ℝ :=
  if α ≤ 1 / 6 then 6 / 5 * α
  else if α ≤ 1 / 3 then 9 / 5 * α - 1 / 10
  else if α ≤ 1 / 2 then 6 / 5 * α + 1 / 10
  else 1

end BinPacking.FirstFit


