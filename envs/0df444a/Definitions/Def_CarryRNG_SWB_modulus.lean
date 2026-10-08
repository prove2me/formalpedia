-- Prove2me | Definitions.Def_CarryRNG_SWB_modulus
-- name    : CarryRNG_SWB_modulus
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-06T17:41:11.894307+00:00
-- url     : https://prove2.me/theorems/142ae92c-c6eb-49c6-8336-d12b15bfef81
-- title:
--   The Method 1 modulus
-- statement:
--   For base $b$ and lags $0<s<r$, the modulus associated with Method 1 is
--   $$m=b^r-b^s+1.$$
--   This is the denominator of the fractions whose base-$b$ digits encode the generated sequence. With $b\ge2$, the natural-number subtraction is exact because $b^s<b^r$.
-- source:
--   G. Marsaglia and A. Zaman, A new class of random number generators, Ann. Appl. Probab. 1 (1991), p. 471, Section 4.4

import Definitions.Def_CarryRNG_AWC_Lags

namespace CarryRNG.SWB

/-- The modulus `b^r - b^s + 1` of the first subtract-with-borrow method. -/
def modulus (b : ℕ) (L : CarryRNG.AWC.Lags) : ℕ := b ^ L.r - b ^ L.s + 1

end CarryRNG.SWB


