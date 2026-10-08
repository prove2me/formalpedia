-- Prove2me | Definitions.Def_CarryRNG_AWC_digit
-- name    : CarryRNG_AWC_digit
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-06T15:01:52.962182+00:00
-- url     : https://prove2.me/theorems/17e3ac57-6304-4870-b5d6-df597c38867b
-- title:
--   The $j$-th base-$b$ digit of $k/m$ (Section 4.1, p. 467)
-- statement:
--   Let $b \ge 2$ be a base, $m \ge 1$ a modulus, and $k$ a natural number. For $j \ge 1$, the **$j$-th digit** of the base-$b$ expansion of $k/m$ is
--
--   $$d_j(k/m) = \left\lfloor \frac{b \cdot \bigl(b^{j-1} k \bmod m\bigr)}{m} \right\rfloor .$$
--
--   For $0 \le k < m$ this is the $j$-th digit after the point in the base-$b$ expansion $k/m = 0.d_1 d_2 d_3 \dots$ (base $b$), the one that never ends in an infinite run of the digit $b - 1$: the fractional part of $b^{j-1} k / m$ is $(b^{j-1}k \bmod m)/m$, and its leading base-$b$ digit is the floor above. These are the expansions of Section 4.1, for example $1/39 = 0.025641025\dots$ in base $10$.
--
--   **Formalization Note** The definition is exact integer arithmetic, with natural-number division as the floor. Only $j \ge 1$ is meaningful; the value at $j = 0$ coincides with the value at $j = 1$ and is never used. The Lean function is total and also returns a number when $m=0$; the expansion claims use $m>0$.
-- source:
--   G. Marsaglia and A. Zaman, A new class of random number generators, Ann. Appl. Probab. 1 (1991), p. 467, Section 4.1 (base-b expansion of k/m)

import Mathlib

namespace CarryRNG.AWC

/-- The `j`-th base-`b` digit after the point in the expansion of `k/m` (Section 4.1, p. 467),
for `j ≥ 1`: `⌊b · ((b^(j-1) k) mod m) / m⌋`. The value at `j = 0` equals the value at `j = 1`
and is never used. -/
def digit (b m k j : ℕ) : ℕ := b * (b ^ (j - 1) * k % m) / m

end CarryRNG.AWC


