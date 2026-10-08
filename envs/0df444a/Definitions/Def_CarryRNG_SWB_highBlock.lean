-- Prove2me | Definitions.Def_CarryRNG_SWB_highBlock
-- name    : CarryRNG_SWB_highBlock
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-06T17:41:08.128177+00:00
-- url     : https://prove2.me/theorems/f39671ae-2448-415c-96ea-6db363101293
-- title:
--   The integer x_r ... x_(s+1)
-- statement:
--   The paper reads the symbol string $x_r\cdots x_{s+1}$ as a base-$b$ integer. In the oldest-first indexing of the state, this is
--   $$A=\sum_{i=0}^{r-s-1}x_{s+i+1}b^i.$$
--   Thus $x_r$ is the most significant digit and $x_{s+1}$ the least significant digit. This integer appears in Method 1’s classification of periodic seeds.
-- source:
--   G. Marsaglia and A. Zaman, A new class of random number generators, Ann. Appl. Probab. 1 (1991), p. 472, Section 4.5, Method 1

import Definitions.Def_CarryRNG_AWC_State

namespace CarryRNG.SWB

/-- The integer with base-`b` representation `x_r ... x_(s+1)`. -/
def highBlock (b : ℕ) (L : CarryRNG.AWC.Lags) (z : CarryRNG.AWC.State b L.r) : ℕ :=
  ∑ i : Fin (L.r - L.s), (z.x ⟨L.s + i.val, by have := L.hsr; have := i.isLt; omega⟩).val * b ^ i.val

end CarryRNG.SWB


