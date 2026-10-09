-- Prove2me | Definitions.Def_RamanujanNotebooks_ch01_ch1IsMagic
-- name    : RamanujanNotebooks_ch01_ch1IsMagic
-- status  : Definition
-- author  : @Xiang Huang
-- created : 2026-10-06T21:14:35.46265+00:00
-- url     : https://prove2.me/theorems/5b166d58-c44b-4c0f-a1c3-862f8e33a456
-- title:
--   Ramanujan's Notebooks, Part I, Ch. 1: ch1IsMagic
-- statement:
--   `M` is a magic square with common sum `r` in the sense of Chapter 1 (p. 16): every row,
--   every column and both diagonals of the `n × n` array of natural numbers sum to `r`.
--   Distinctness of the entries is NOT part of this predicate (the book asks for it only
--   "usually"); zero entries are allowed.
--   Reference: `![![6, 1, 8], ![7, 5, 3], ![2, 9, 4]]` is magic with `r = 15`;
--   `![![10, 2, 7], ![4, 6, 9], ![5, 11, 3]]` is not magic for any `r` (secondary diagonal `18`,
--   rows `19`).
-- source:
--   Bruce C. Berndt, Ramanujan's Notebooks, Part I (Springer, 1985), Chapter 1.

import Mathlib
import Definitions.Def_RamanujanNotebooks_ch01_ch1AntiDiagSum
import Definitions.Def_RamanujanNotebooks_ch01_ch1DiagSum
import Definitions.Def_RamanujanNotebooks_ch01_ch1IsSemiMagic

namespace RamanujanNotebooks

/-- `M` is a magic square with common sum `r` in the sense of Chapter 1 (p. 16): every row,
every column and both diagonals of the `n × n` array of natural numbers sum to `r`.
Distinctness of the entries is NOT part of this predicate (the book asks for it only
"usually"); zero entries are allowed.
Reference: `![![6, 1, 8], ![7, 5, 3], ![2, 9, 4]]` is magic with `r = 15`;
`![![10, 2, 7], ![4, 6, 9], ![5, 11, 3]]` is not magic for any `r` (secondary diagonal `18`,
rows `19`). -/
def ch1IsMagic {n : ℕ} (M : Fin n → Fin n → ℕ) (r : ℕ) : Prop :=
  ch1IsSemiMagic M r ∧ ch1DiagSum M = r ∧ ch1AntiDiagSum M = r

end RamanujanNotebooks


