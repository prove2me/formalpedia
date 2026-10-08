-- Prove2me | Definitions.Def_CarryRNG_SWB_lowBlock
-- name    : CarryRNG_SWB_lowBlock
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-06T17:41:05.330354+00:00
-- url     : https://prove2.me/theorems/ca1208bb-a883-49a7-a69e-d954be53bc6a
-- title:
--   The integer x_(r-s) ... x_1
-- statement:
--   The paper reads the symbol string $x_{r-s}\cdots x_1$ as a base-$b$ integer. In the oldest-first indexing of the state, this is
--   $$B=\sum_{i=0}^{r-s-1}x_{i+1}b^i.$$
--   Thus $x_{r-s}$ is the most significant digit and $x_1$ the least significant digit. It is compared with $A=x_r\cdots x_{s+1}$ in Method 1’s seed rule.
-- source:
--   G. Marsaglia and A. Zaman, A new class of random number generators, Ann. Appl. Probab. 1 (1991), p. 472, Section 4.5, Method 1

import Definitions.Def_CarryRNG_AWC_State

namespace CarryRNG.SWB

/-- The integer with base-`b` representation `x_(r-s) ... x_1`. -/
def lowBlock (b : ℕ) (L : CarryRNG.AWC.Lags) (z : CarryRNG.AWC.State b L.r) : ℕ :=
  ∑ i : Fin (L.r - L.s), (z.x ⟨i.val, by have := L.hsr; have := i.isLt; omega⟩).val * b ^ i.val

end CarryRNG.SWB


