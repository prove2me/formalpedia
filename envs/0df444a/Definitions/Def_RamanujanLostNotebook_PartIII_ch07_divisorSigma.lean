-- Prove2me | Definitions.Def_RamanujanLostNotebook_PartIII_ch07_divisorSigma
-- name    : RamanujanLostNotebook_PartIII_ch07_divisorSigma
-- status  : Definition
-- author  : @Xiang Huang
-- created : 2026-10-08T21:18:49.27634+00:00
-- url     : https://prove2.me/theorems/fc3846a9-14f5-4c15-9495-8b9b82e5c8f4
-- title:
--   Ramanujan's Lost Notebook Part III, Ch. 7: divisorSigma
-- statement:
--   The divisor power sum `σ_k(n) = ∑_{d ∣ n} d^k` (p. 205), as an integer.
--   The book uses it for `n ≥ 1` only.  At `n = 0` the Lean value is `0` (`Nat.divisors 0 = ∅`);
--   no statement of this chapter evaluates it there.
--   Reference: `σ_1(4) = 7`, `σ_3(2) = 9`, `σ_5(3) = 244`, `σ_15(2) = 32769`.
-- source:
--   G. E. Andrews and B. C. Berndt, Ramanujan's Lost Notebook, Part III, Springer 2012, Chapter 7.

import Mathlib

namespace RamanujanLostNotebook.PartIII

/-- The divisor power sum `σ_k(n) = ∑_{d ∣ n} d^k` (p. 205), as an integer.
The book uses it for `n ≥ 1` only.  At `n = 0` the Lean value is `0` (`Nat.divisors 0 = ∅`);
no statement of this chapter evaluates it there.
Reference: `σ_1(4) = 7`, `σ_3(2) = 9`, `σ_5(3) = 244`, `σ_15(2) = 32769`. -/
def divisorSigma (k n : ℕ) : ℤ :=
  ∑ d ∈ Nat.divisors n, (d : ℤ) ^ k

end RamanujanLostNotebook.PartIII


