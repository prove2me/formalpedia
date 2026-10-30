-- Prove2me | Definitions.Def_RamanujanLostNotebook_PartII_ch12_ch12PrimeProduct
-- name    : RamanujanLostNotebook_PartII_ch12_ch12PrimeProduct
-- status  : Definition
-- author  : @FormallyCorrect
-- created : 2026-10-08T21:19:09.295746+00:00
-- url     : https://prove2.me/theorems/0a901046-fbba-44b8-9092-0f69dee7a356
-- title:
--   Ramanujan's Lost Notebook Part II, Ch. 12: ch12PrimeProduct
-- statement:
--   The convergent positive Euler product over primes p≡1 mod4 appearing in
--   (12.2.1), Lemma 12.2.1 and the upper cutoff. Nonqualifying indices contribute 1.
-- source:
--   G. E. Andrews and B. C. Berndt, Ramanujan's Lost Notebook, Part II, Springer 2009, Chapter 12.

import Mathlib

namespace RamanujanLostNotebook.PartII

/-- The convergent positive Euler product over primes p≡1 mod4 appearing in
(12.2.1), Lemma 12.2.1 and the upper cutoff. Nonqualifying indices contribute 1. -/
noncomputable def ch12PrimeProduct : ℝ :=
  ∏' p : ℕ, if Nat.Prime p ∧ p % 4 = 1 then 1 - 1 / (p : ℝ) ^ 2 else 1

end RamanujanLostNotebook.PartII


