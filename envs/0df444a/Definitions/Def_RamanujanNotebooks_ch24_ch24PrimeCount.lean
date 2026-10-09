-- Prove2me | Definitions.Def_RamanujanNotebooks_ch24_ch24PrimeCount
-- name    : RamanujanNotebooks_ch24_ch24PrimeCount
-- status  : Definition
-- author  : @Xiang Huang
-- created : 2026-10-06T23:54:04.09915+00:00
-- url     : https://prove2.me/theorems/d493f062-7e9f-46d0-9512-dd8c34755e97
-- title:
--   Ramanujan's Notebooks, Part IV, Ch. 24: ch24PrimeCount
-- statement:
--   Number of primes `p ≤ n`, for a natural number `n`: the cardinality of
--   `{p ∈ {0, 1, …, n} | p prime}` (the prime counting function `π` at an integer; Part IV,
--   Chapter 24, p. 111).  Total, computable, no junk value.
--   Reference: `ch24PrimeCount 1 = 0`, `ch24PrimeCount 2 = 1`, `ch24PrimeCount 10 = 4`,
--   `ch24PrimeCount 1000 = 168`.
-- source:
--   Bruce C. Berndt, Ramanujan's Notebooks, Part IV (Springer, 1994), Chapter 24.

import Mathlib

namespace RamanujanNotebooks

/-- Number of primes `p ≤ n`, for a natural number `n`: the cardinality of
`{p ∈ {0, 1, …, n} | p prime}` (the prime counting function `π` at an integer; Part IV,
Chapter 24, p. 111).  Total, computable, no junk value.
Reference: `ch24PrimeCount 1 = 0`, `ch24PrimeCount 2 = 1`, `ch24PrimeCount 10 = 4`,
`ch24PrimeCount 1000 = 168`. -/
def ch24PrimeCount (n : ℕ) : ℕ :=
  (Finset.filter Nat.Prime (Finset.range (n + 1))).card

end RamanujanNotebooks


