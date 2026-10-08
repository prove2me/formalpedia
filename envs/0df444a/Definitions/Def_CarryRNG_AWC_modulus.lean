-- Prove2me | Definitions.Def_CarryRNG_AWC_modulus
-- name    : CarryRNG_AWC_modulus
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-06T15:12:51.862379+00:00
-- url     : https://prove2.me/theorems/ac7c5c5a-2fc2-4eb8-90c4-581a1dd7137b
-- title:
--   The add-with-carry modulus $m = b^r + b^s - 1$ (Section 4.2, p. 467)
-- statement:
--   For a base $b$ and lags $0 < s < r$, the **add-with-carry modulus** is the natural number
--
--   $$m = b^r + b^s - 1 .$$
--
--   The periods of the add-with-carry generator are periods of base-$b$ expansions of fractions $k/m$ with this denominator (Section 4.2). For $b \ge 2$ one has $m \ge b^2 + b - 1 \ge 5$, and $m \equiv -1 \pmod b$, so $b$ is invertible modulo $m$.
--
--   **Formalization Note** The subtraction is natural-number subtraction; it is exact whenever $b \ge 1$, and every statement using the modulus assumes $b \ge 2$.
-- source:
--   G. Marsaglia and A. Zaman, A new class of random number generators, Ann. Appl. Probab. 1 (1991), p. 467, Section 4.2 (m = b^r + b^s - 1); p. 472, Method 3

import Definitions.Def_CarryRNG_AWC_Lags

namespace CarryRNG.AWC

/-- The add-with-carry modulus `m = b^r + b^s - 1` (Section 4.2, p. 467). -/
def modulus (b : ℕ) (L : Lags) : ℕ := b ^ L.r + b ^ L.s - 1

end CarryRNG.AWC


