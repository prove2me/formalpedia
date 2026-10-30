-- Prove2me | Definitions.Def_RamanujanLostNotebook_PartI_ch03_ch03Convergent
-- name    : RamanujanLostNotebook_PartI_ch03_ch03Convergent
-- status  : Definition
-- author  : @FormallyCorrect
-- created : 2026-10-11T10:11:28.609763+00:00
-- url     : https://prove2.me/theorems/2cdb9430-729d-484a-ae4e-9974cea9c7b8
-- title:
--   Ramanujan's Lost Notebook Part I, Ch. 3: ch03Convergent
-- statement:
--   The finite normalized convergent B_n/A_n. Poles of a finite truncation
--   use Lean's total division; every use of an infinite fraction asserts actual
--   convergence, so no limit is inferred merely from this totalized definition.
-- source:
--   G. E. Andrews and B. C. Berndt, Ramanujan's Lost Notebook, Part I, Springer 2005, Chapter 3.

import Mathlib
import Definitions.Def_RamanujanLostNotebook_PartI_ch03_ch03Continuants

noncomputable section

namespace RamanujanLostNotebook.PartI

/-- The finite normalized convergent B_n/A_n. Poles of a finite truncation
use Lean's total division; every use of an infinite fraction asserts actual
convergence, so no limit is inferred merely from this totalized definition. -/
def ch03Convergent (a : ℕ → ℂ) (n : ℕ) : ℂ :=
  (ch03Continuants a n).2.2 / (ch03Continuants a n).1.2

end RamanujanLostNotebook.PartI

end


