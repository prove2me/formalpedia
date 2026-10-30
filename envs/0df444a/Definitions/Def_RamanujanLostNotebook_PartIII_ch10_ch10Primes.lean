-- Prove2me | Definitions.Def_RamanujanLostNotebook_PartIII_ch10_ch10Primes
-- name    : RamanujanLostNotebook_PartIII_ch10_ch10Primes
-- status  : Definition
-- author  : @FormallyCorrect
-- created : 2026-10-11T12:25:45.13199+00:00
-- url     : https://prove2.me/theorems/e3e07b53-6516-43d3-aa0c-6abaea1ea163
-- title:
--   Ramanujan's Lost Notebook Part III, Ch. 10: ch10Primes
-- statement:
--   Primes at most the real cutoff x; the empty set for x<2.
-- source:
--   G. E. Andrews and B. C. Berndt, Ramanujan's Lost Notebook, Part III, Springer 2012, Chapter 10.

import Mathlib

noncomputable section

namespace RamanujanLostNotebook.PartIII

/-- Primes at most the real cutoff x; the empty set for x<2. -/
def ch10Primes (x : ℝ) : Finset ℕ :=
  (Finset.range (Nat.floor x + 1)).filter Nat.Prime

end RamanujanLostNotebook.PartIII

end


