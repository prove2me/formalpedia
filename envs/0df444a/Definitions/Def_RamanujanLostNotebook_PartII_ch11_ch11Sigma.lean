-- Prove2me | Definitions.Def_RamanujanLostNotebook_PartII_ch11_ch11Sigma
-- name    : RamanujanLostNotebook_PartII_ch11_ch11Sigma
-- status  : Definition
-- author  : @Xiang Huang
-- created : 2026-10-11T11:23:47.377362+00:00
-- url     : https://prove2.me/theorems/c4ea9efb-760c-4b92-bac3-6e2a7d345657
-- title:
--   Ramanujan's Lost Notebook Part II, Ch. 11: ch11Sigma
-- statement:
--   Divisor power sum, evaluated only at positive indices in the coefficient polynomials.
-- source:
--   G. E. Andrews and B. C. Berndt, Ramanujan's Lost Notebook, Part II, Springer 2009, Chapter 11.

import Mathlib

noncomputable section

namespace RamanujanLostNotebook.PartII

/-- Divisor power sum, evaluated only at positive indices in the coefficient polynomials. -/
def ch11Sigma (k n : ℕ) : ℤ :=
  ∑ d ∈ Nat.divisors n, (d : ℤ) ^ k

end RamanujanLostNotebook.PartII

end


