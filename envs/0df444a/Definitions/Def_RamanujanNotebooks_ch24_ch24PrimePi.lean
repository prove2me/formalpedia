-- Prove2me | Definitions.Def_RamanujanNotebooks_ch24_ch24PrimePi
-- name    : RamanujanNotebooks_ch24_ch24PrimePi
-- status  : Definition
-- author  : @Xiang Huang
-- created : 2026-10-06T23:57:39.507389+00:00
-- url     : https://prove2.me/theorems/b7cf76a3-6d0b-4933-9a18-ac3b2e5bffb7
-- title:
--   Ramanujan's Notebooks, Part IV, Ch. 24: ch24PrimePi
-- statement:
--   The prime counting function `π(x)`, the number of primes `≤ x`, for real `x` (Part IV,
--   Chapter 24, p. 111), as `ch24PrimeCount` of the natural-number floor of `x`.
--   Domain: all real `x`; for `x < 2` (in particular for negative `x`, where the floor is `0`)
--   the value is `0`, which is the correct count.  No junk value.
--   Reference: `π(10) = 4`, `π(π) = 2`, `π(1000) = 168`.
-- source:
--   Bruce C. Berndt, Ramanujan's Notebooks, Part IV (Springer, 1994), Chapter 24.

import Mathlib
import Definitions.Def_RamanujanNotebooks_ch24_ch24PrimeCount

namespace RamanujanNotebooks

/-- The prime counting function `π(x)`, the number of primes `≤ x`, for real `x` (Part IV,
Chapter 24, p. 111), as `ch24PrimeCount` of the natural-number floor of `x`.
Domain: all real `x`; for `x < 2` (in particular for negative `x`, where the floor is `0`)
the value is `0`, which is the correct count.  No junk value.
Reference: `π(10) = 4`, `π(π) = 2`, `π(1000) = 168`. -/
noncomputable def ch24PrimePi (x : ℝ) : ℕ :=
  ch24PrimeCount ⌊x⌋₊

end RamanujanNotebooks


