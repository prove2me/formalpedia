-- Prove2me | Definitions.Def_RamanujanLostNotebook_PartIV_ch11_primeTheta
-- name    : RamanujanLostNotebook_PartIV_ch11_primeTheta
-- status  : Definition
-- author  : @Xiang Huang
-- created : 2026-10-06T14:26:46.187543+00:00
-- url     : https://prove2.me/theorems/5a62a471-15c9-4164-bf16-24f7b378c41d
-- title:
--   Ramanujan's Lost Notebook Part IV, Ch. 11: primeTheta
-- statement:
--   Chebyshev's function `ϑ(x) = ∑_{p ≤ x} log p`, the sum over primes `p ≤ x`
--   (zero for `x < 2`).  It is the function called `ϑ` in Chapter 11; if the pinned Mathlib has
--   `Chebyshev.theta`, this is the same function, written out to avoid depending on that name.
-- source:
--   G. E. Andrews and B. C. Berndt, Ramanujan's Lost Notebook, Part IV, Springer 2013, Chapter 11.

import Mathlib

namespace RamanujanLostNotebook.PartIV

/-- Chebyshev's function `ϑ(x) = ∑_{p ≤ x} log p`, the sum over primes `p ≤ x`
(zero for `x < 2`).  It is the function called `ϑ` in Chapter 11; if the pinned Mathlib has
`Chebyshev.theta`, this is the same function, written out to avoid depending on that name. -/
noncomputable def primeTheta (x : ℝ) : ℝ :=
  ∑ p ∈ Finset.filter Nat.Prime (Finset.range (⌊x⌋₊ + 1)), Real.log (p : ℝ)

end RamanujanLostNotebook.PartIV


