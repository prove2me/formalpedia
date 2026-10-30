-- Prove2me | Definitions.Def_RamanujanLostNotebook_PartII_ch12_ch12Admissible
-- name    : RamanujanLostNotebook_PartII_ch12_ch12Admissible
-- status  : Definition
-- author  : @FormallyCorrect
-- created : 2026-10-08T21:20:54.866268+00:00
-- url     : https://prove2.me/theorems/70d14b3e-65b2-4ecb-8949-742438ff6699
-- title:
--   Ramanujan's Lost Notebook Part II, Ch. 12: ch12Admissible
-- statement:
--   The admissible positive integers μ from (11.4.4): 1,2,5,10,13,... .
--   The representative test is equivalent to being a sum of two coprime squares.
-- source:
--   G. E. Andrews and B. C. Berndt, Ramanujan's Lost Notebook, Part II, Springer 2009, Chapter 12.

import Mathlib
import Definitions.Def_RamanujanLostNotebook_PartII_ch12_ch12Reps

namespace RamanujanLostNotebook.PartII

/-- The admissible positive integers μ from (11.4.4): 1,2,5,10,13,... .
The representative test is equivalent to being a sum of two coprime squares. -/
def ch12Admissible (mu : ℕ) : Prop :=
  mu = 1 ∨ mu = 2 ∨ (ch12Reps mu).Nonempty

end RamanujanLostNotebook.PartII


