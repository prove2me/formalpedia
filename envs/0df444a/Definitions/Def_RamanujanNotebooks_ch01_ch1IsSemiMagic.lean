-- Prove2me | Definitions.Def_RamanujanNotebooks_ch01_ch1IsSemiMagic
-- name    : RamanujanNotebooks_ch01_ch1IsSemiMagic
-- status  : Definition
-- author  : @Xiang Huang
-- created : 2026-10-06T21:11:01.70591+00:00
-- url     : https://prove2.me/theorems/9f5e8cca-dadc-47e3-8e18-befa72a7f099
-- title:
--   Ramanujan's Notebooks, Part I, Ch. 1: ch1IsSemiMagic
-- statement:
--   Every row sum and every column sum of the `n × n` array `M` equals `r`; nothing is
--   asked of the two diagonals and nothing about distinctness of the entries.
--   Reference: `![![10, 2, 8], ![4, 5, 11], ![6, 13, 1]]` satisfies this with `r = 20`
--   (its diagonal sums are `16` and `19`).
-- source:
--   Bruce C. Berndt, Ramanujan's Notebooks, Part I (Springer, 1985), Chapter 1.

import Mathlib

namespace RamanujanNotebooks

/-- Every row sum and every column sum of the `n × n` array `M` equals `r`; nothing is
asked of the two diagonals and nothing about distinctness of the entries.
Reference: `![![10, 2, 8], ![4, 5, 11], ![6, 13, 1]]` satisfies this with `r = 20`
(its diagonal sums are `16` and `19`). -/
def ch1IsSemiMagic {n : ℕ} (M : Fin n → Fin n → ℕ) (r : ℕ) : Prop :=
  (∀ i : Fin n, (∑ j : Fin n, M i j) = r) ∧ (∀ j : Fin n, (∑ i : Fin n, M i j) = r)

end RamanujanNotebooks


